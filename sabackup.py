#!/usr/bin/python

################################
##
##  sabackup
##  A tool to backup OS X Server Service Configurations
##
##  Written by: Beau Hunter beau@318.com 12/28/09
##	
##  Changelog
##
##  11/07/2011		Began adding restore functionality
##					gsullivan
##  12/8/2011		Updated servicesMap for Lion
##					gsullivan
##	1/25/2012		Built OD backup into
#############################################################


## Setup our variables

import sys,getopt,re,os,string,types,datetime,time,glob
import syslog,logging,logging.handlers,plistlib,shutil,subprocess
import platform
import codecs
import sqlite3

## init our vars
version = ".60"
build = "20111213"
DEBUG = False


######################### START FUNCTIONS ###############################

def helpMessage():
  print '''sabackup.py: A tool to backup OS X Server Service Configurations
   
Syntax: 
  sabackup.py --outputdir="/sabackups/" [options]
  sabackup.py --outputfile="/sabackup.dmg" [--services=afp,dns,ftp] [options] 
  sabackup.py --outputfile="/sabackup.plist" --nodmg [--service=dns] [options]
  sabackup.py --plist="/Library/Preferences/com.318.sabackup.plist"
  
Flags: 
  --plist=         ## Path to a plist to read configuration information from
                    This will override any other provided options!
                    
  --outputfile=    ## path to save exported plist or sparseimage file.
  --outputdir=     ## path to directory for export. If multiple services are
                    specified, they will be saved in service-specific 
                    subdirectories under 'dir'

  --usedmg         ## When specified, backups will be saved in the form of 
                    a sparseimage file, which contain versioned backups of
                    service configs. Defaults to true with the 
                    '--outputfile=' option, and defaults to false with
                    the '--outputdir=' option. If --useimage is used with
                    '--outputdir', then a disk image will be made based on
                    the machines hostname: "myhost.local_sabackups.sparseimage"

  --nodmg          ## When used in conjunction with the '--outputfile' 
                    option, output will be in the form of an XML plist
                    of the specified services. 

  --nosubdirs      ## Disables the use of service-specific subdirectories  

  --service=       ## Used with '--outputfile' option to denote which 
                    service is to be saved to the specified file.

  --services=      ## Used with --outputdir option to denote which services
                    will be backed up. Supported Services:
                    "all" - akin to 'serveradmin settings all'
                    "running" - backs up all running services
                    "afp,smb"... (all services supported by `serveradmin list`)

  --odarchive      ## Enables creation of an Open Directory archive. This flag
                    requires a password be specified for the OD archive with the
                    --odpassword flag

  --odpassword     ## Used with the --odarchive flag to specify the password
                    for the OD archive sparseimage.

  --usetimestamps  ## Forces written file to include a timestamp:
                    myfile_201001102301.plist 
                    (Y+M+D++time) (2010/01/10 11:01PM)
                    Defaults to true with --outputdir option

  --notimestamps   ## Omits timestamp from all written files. Defaults to 
                    true with --outputfile option
                            
  -p,--prune       ## Prune backups (only qualifies with timestamped backups)
    --maxage=      ## Max age of a file (in days) before qualifying for pruning
    --mincopies=   ## Minimum number of copies to keep of a file, overrides maxage
    --maxcopies=   ## Maximum number of copies to keep of a file, regardless of age

  -f,--force       ## Do not prompt for verification when overwriting 
                    existing files or performing restore operations. 

  -v,--version     ## Print out version info.

  --restore        ## Specifies a restore operation

   '''
   
   ## NEEDS IMPLEMENTING
  '''    --restoreFrom=   ## Specifies the backup to restore from. Options:
                    "latest" - Uses the latest backup for each specified
                    service.
                    "first"  -  Uses the first backup for each specified
                    service.
                    "choose" - Prompts the user to choose from a backup.'''
   
    
def getNextFSName(self,filePath,dirPath=""):
  '''Accepts a fileName and optionally, a directory. If the latter is supplied
  filePath will be considered relative to directory. Returns a filepath with a 
  fileName portion of a file that does not exist by iterating. I.E:
  if called with filePath = /filename.txt, it will return "/filename.txt" if 
  no file exists at /filename.txt, if file does exist, it will return 
  "/filename_1.txt", or "/filename_2.txt" iterating until it finds a filename that doesn't already
  exist. '''
  
  if dirPath:
    if filePath[0:1] == "/":
      filePath = filePath[1:]
    absFilePath = os.path.abspath(os.path.join(dirPath,filePath))
  else:
    absFilePath = os.path.abspath(filePath)
    
  absDirPath = os.path.parent(filePath)
  fileName = os.path.basename(filePath)
  baseFileName = os.path.splitext(fileName)[0]
  fileExtension = os.path.splitext(fileName)[1]
  
  myFilePath = absFilePath
  myCount = 1
  while os.path.exists(myFilePath):
    myFilePath = os.path.join(absDirPath,"%s_%s%s" % (baseFileName,myCount,fileExtension))
    myCount += 1

  return myFilePath
  
  

######################### END FUNCTIONS #################################

######################### START CLASSES ###############################

class baseService: 
  '''This is our base object which contains members that store basic service 
  and backup information. It also defines logging routines used by our 
  individual classes'''
  
  
  name = ""              ## The service as used in SA (i.e. 'afp')
  baseName = ""          ## Name used in backup naming conventions (i.e. system_profiler,sa_afp)
  displayName = ""       ## Our display name for the service, used to properly encode serveradmin exports
  backupPath = ""        ## our service-specific backupPath
  
  backupSessions = []    ## List of found files
  useTimeStamps = True   ## bool value on whether to timestamp files
  timeStamp = ""         ## String value of our timestamp 
  overWriteExistingFiles = False

  supportsSingleFileOutput = False
  
  isLoaded = False         ## bool value on whether we've loaded
  plist = {}               ## our services plist dictionary
  servicesMap = {}         ## dictionary of services which we are responsible for
  loadedServices = []      ## Array of keys which have been loaded

  canPrune = False
  pruneOptions = {"maxAge" : 30, "minCopies" : 1, "maxCopies" : 0}

  lastMSG = ""             ## Last log message
  lastError = ""           ## Last error log message
  log = []                 ## Array of logged messages
  echoLogs = True          ## Is logging enabled
  debug = False            ## Is debug mode enabled
  
  
  def __init__(self,name="",backupPath=""):
    '''Inits our base vars'''
    
    self.backupPath = ""
    self.useTimeStamps = True
    self.overWriteExistingFiles = False
    self.isLoaded = False
    self.pruneOptions = { "maxAge":2,"minCopies":1,"maxCopies":0 }
    self.lastMSG = ""
    self.lastError = ""
    self.log = []
    self.info = {}


    if backupPath:
      self.setBackupPath(backupPath)
    if name:
      self.setName(name)

  def logger(self, logMSG, logLevel="normal"):
    """(very) Basic Logging Function, we'll probably migrate to msg module"""
    if logLevel[0:5] == "debug" and not self.debug:
      return
    if logLevel == "error":
      self.lastError = logMSG

    self.lastMSG = logMSG
    
    if self.echoLogs or self.debug:
      if self.debug:
        print "%s: %s" % (self.name, logMSG)
      else:
        print logMSG
    sys.stdout.flush()
        
    self.log.append({"logLevel" : logLevel, "logMSG" : logMSG})
  
  def printLogs(self, logLevel="all"):
    """output our logs"""
    for log in self.log:
      if logLevel == "all" or logLevel == log["logLevel"]:
        print "%s:%s:%s" % (self.name,log["logLevel"], log["logMSG"])
  
  def setName(self,name):
    """ Method which sets local serveradmin name """
    
    self.logger("setName hit: %s" % name,"debug")
    if name in self.servicesMap:
      self.displayName = self.servicesMap[name]
      self.name = name
      self.logger("Setting name %s for service %s" % (self.name,self.displayName),"debug")
      return True
    else:
      self.logger("Could not find registered service for"        
        + " name: %s" % name,"error")
      self.logger("   -- Service Class: %s " % self.__class__,"debug")
      self.logger("   -- Services Map: %s" % self.servicesMap.keys(),"debug")
      return False
    
    return
  
  def setPruneOptions(self,pruneOptions):
    '''Function which sets our pruning options'''
    try:
      for key,value in pruneOptions.iteritems():
        if key == "minCopies":
          self.pruneOptions["minCopies"] = value
        elif key == "maxCopies":
          self.pruneOptions["maxCopies"] = value
        elif key == "maxAge":
          self.pruneOptions["maxAge"] = value
        else:
          self.logger("Ignoring prune option: %s"  % key,"debug")
          continue
        self.logger("Setting Prune Option: %s to %s" %(key,value),"debug")
    except Exception,err:
      self.logger("Could not set pruneOptions: %s" % err,"error")
      return False
    
    return True
  
  def prune(self,dirPath=""):
    '''Function which prunes backups from the provided directory. Utilized
    self.pruneOptions'''
    
    if not self.baseName:
      self.baseName = self.name
    baseName = self.baseName
    
    ## Get our directory
    if not dirPath:
      dirPath = self.backupPath
    
    ## Get our prune options
    pruneOptions = self.pruneOptions
    maxAge = pruneOptions["maxAge"]
    minCopies = pruneOptions["minCopies"]
    maxCopies = pruneOptions["maxCopies"]
    globString = "%s_*" % baseName
        
    self.pruneBackupsFromDirectory(dirPath,maxAge=maxAge, minCopies=minCopies,maxCopies=maxCopies,globString=globString)
    
    return True
            
  def pruneBackupsFromDirectory(self,dirPath,maxAge=10,minCopies=1,maxCopies=0,globString="*"):
    """This function prunes backups from the specified directory. When ran, it 
    will remove all files in the directory older that maxAge days.
    Regardless of age, at least minCopies will be retained in the directory."""
  
    ## Sanitize our arguments
    try:
      maxAgeInt = int(maxAge)
    except:
      print "maxAge must be an integer!"
      return False
      
    try:
      minCopiesInt = int(minCopies)
    except:
      print "minCopies must be an integer!"
      return False
    try:
      maxCopiesInt = int(maxCopies)
      if maxCopiesInt > 0 and maxCopiesInt < minCopiesInt:
        print "maxCopies must be equal to or larger than minCopies!"
        maxCopiesInt = 0
    except:
      print "maxCopies must be an integer!"
      return False
      
    if not os.path.exists(dirPath):
      print "Failed to prune backups! '%s' does not exist!" % dirPath
      return False
    elif not os.path.isdir(dirPath):
      print "Failed to prune backups! '%s' is not a directory!" % dirPath
      return False
    
    ## Create our datetime objects which represent expired files
    maxTimeDelta = datetime.timedelta(days=maxAgeInt)
    expiredDateTime = datetime.datetime.today() - maxTimeDelta


    ## Get a list of files in the directory, calculate their mtimes
    myFiles = {}
    expiredFiles = []   ## List of expired filenames sorted by date (oldest first)
    allFiles = []       ## List of all filenames sorted by date (oldest first)
      
    fileList = glob.glob(os.path.join(dirPath,globString))

    latestStubName = "%s_latest" % self.baseName
    self.logger("latestStubName: %s" % latestStubName,"debug2")    
    
    for entity in fileList:
      fileName = os.path.basename(entity)
      ## Exclude the "lastest" link from pruning consideration

      self.logger("  - checking fileName %s" % fileName,"debug")
      ##self.logger("fileName stub: %s" % fileName[0:len(latestStubName)],"debug")
      
      if fileName[0:len(latestStubName)] == latestStubName:
        self.logger("Skipping file for pruning: %s" % fileName,"debug")
        continue
      myFilePath = entity
      if os.path.exists(myFilePath):
        myFileDateTime = datetime.datetime.fromtimestamp(os.path.getmtime(myFilePath))
        if myFileDateTime > expiredDateTime:
          myFileExpired = False
        else:
          myFileExpired = True
          ## Add our file to the expiredFiles list based upon it's age
          count = 0
          for expiredFile in expiredFiles:
            if myFiles[expiredFile]["datetime"] > myFileDateTime:
              expiredFiles.insert(count,fileName)
              break
            count += 1
          ## If it hasn't been inserted, append it to the end
          if not entity in expiredFiles:
            expiredFiles.append(fileName)
        ## Add our file to the allFiles list based upon it's age
        count = 0
        for file in allFiles:
          if myFiles[file]["datetime"] > myFileDateTime:
            allFiles.insert(count,fileName)
            break
          count += 1
        ## If it hasn't been inserted, append it to the end
        if not fileName in allFiles:
          allFiles.append(fileName)
        
        ## Add the file to the myFiles dictionary
        myFiles[fileName] = {"datetime": myFileDateTime,"expired": myFileExpired,"path":myFilePath}
      
    ## We have now processed expiration for all files in the directory,
    ## and have comprised an expired files list store at expiredFiles
    ## Remove all expired files or until we have hit our minCopies parameter
    if len(expiredFiles) > (len(myFiles) - minCopiesInt):
      numFilesToRemove = len(myFiles) - minCopiesInt
    else:
      numFilesToRemove = len(expiredFiles)
    
    if maxCopiesInt:
      if len(myFiles) - numFilesToRemove > maxCopiesInt:
        numFilesToRemove = len(myFiles) - maxCopiesInt
      
      if numFilesToRemove > len(expiredFiles):
        rmFileDelta = numFilesToRemove - len(expiredFiles)
        count = 0
        for file in allFiles:
          if count < rmFileDelta:
            expiredFiles.append(file)
          else: 
            break
          count += 1
          
        
    
    
    ## Debug
    ##print "myFiles: %s\nexpiredFiles: %s\n" % (myFiles,expiredFiles)
    
    if numFilesToRemove <= 0:
      self.logger("     No files qualify for pruning!","detailed")
      return True
    
    self.logger("     Pruning %s of %s files!" % (numFilesToRemove,len(myFiles)))
    count = 0
    failedFiles = []
    while count < numFilesToRemove:
      fileToRemove = expiredFiles[count]

      try:
        rmPath = myFiles[fileToRemove]["path"]
        if os.path.isdir(rmPath):
          shutil.rmtree(rmPath)
          self.logger("     - Pruned Directory: %s" % fileToRemove,"detailed")
        else:
          os.remove(rmPath)
          self.logger("     - Pruned file: %s" % fileToRemove,"detailed")

      except:
        self.logger("     ERROR: could not prune file: %s" % fileToRemove,"error")
        failedFiles.append(fileToRemove)
      count += 1
    
    if len(failedFiles) == 0:
      self.logger("     Successfully pruned expired files!","detailed")
      return True
    
    return False
  
  def setBackupPath(self,backupPath):
    """ Method which sets the backup directory"""
    
    ## Normalize the path
    realBackupPath = os.path.abspath(os.path.realpath(os.path.expanduser(backupPath)))
    parentDir = os.path.dirname(realBackupPath)
    
    #self.logger("backupPath: %s parentDir: %s" % (backupPath,parentDir),"debug")
    
    if not os.path.isdir(parentDir):
      self.logger("setBackupPath() could not set backupPath, parent:'%s' "  % parentDir
            + "does not exist!","error")        
      if not os.path.exists(realBackupPath):
        try:
          if not os.mkdir(realBackupPath):
            self.logger("setBackupPath() could not create directory at "
            + "path:'%s'" % backupPath,"error")
            return False
        except:
          self.logger("setBackupPath() could not create directory at "
            + "path:'%s'" % backupPath,"error")
          return False
      else:
        self.logger("setBackupPath() Non-directory exists at path:'%s' "
          + "cannot continue!" % backupPath,"error")
        return False
    self.backupPath = realBackupPath
    return True
  
  def getRunningServiceList(self=""):
    '''Returns a list of running services. This returns all registered
    services for the object, over-ride this for your specific object'''
    return self.servicesMap.keys()
  
  def valueForAliasKeyPath(self,keyPath=""):
    """Returns a value for keyPath based upon a specific keyPath alias
    This function primarily serves as an override method for valueForKeyPath
    where manipulation of stored data is replied (concatanation of fields,
    mathematics, etc..."""
    
    raise RuntimeError("No alias exists for keyPath: %s" % keyPath)
  
  def mergeTrees(self,tree1,tree2):
    """This function will merge array/dict/key value trees from tree2 to tree1.
    In the event of two conflicting values, tree1 will provide the dominant 
    value, provided it is not null"""
    
    if not type(tree1) == type(tree2):
      raise RuntimeError("mergeTrees() Passed trees do not have the same types! "
        " Tree1: %s, Tree2: %s" % (type(tree1),type(tree2)))
    currentTree1Iterater = tree1
    currentTree2Iterater = tree2
    
    if type(currentTree2Iterater) == type({}):
      for key,value in currentTree2Iterater.iteritems():
        if not key in currentTree1Iterater:
          currentTree1Iterater[key] = value
        else:
          if type(key) == type({}) or type(key) == type([]):
            currentTree1Iterater[key] = self.mergeTrees(currentTree1Iterater[key],currentTree2Iterator[key])
          else:
            if not currentTree1Iterater[key] and currentTree2Iterator[key]:
              self.logger("mergeTrees() found conflicting value for key: %s, "
                            "utilizing tree2 value: %s over current value: %s"
                            % (key,currentTree2Iterator[key],currentTree1Iterator[key]),"detailed")
              currentTree1Iterater[key] = currentTree2Iterator[key]
    elif type(currentTree2Iterator) == type([]):
      for value in currentTree2Iterator:
        if not value in currentTree1Iterater:
          currentTree1Iterater.append(value)
    else:
      if not currentTree1Iterator[key] and currentTree2Iterator[key]:
        self.logger("mergeTrees() found empty value for key: %s, "
                      "utilizing tree2 value: %s"
                      % (key,currentTree2Iterator[key]),"detailed")
        currentTree1Iterater[key] = currentTree2Iterator[key]

      elif currentTree1Iterator[key] and currentTree2Iterator[key]:
        self.logger("mergeTrees() found conflicting value for key: %s, "
                      "utilizing tree2 value: %s over current value: %s"
                      % (key,currentTree2Iterator[key],currentTree1Iterator[key]),"debug")
        currentTree1Iterater[key] = currentTree2Iterator[key]
    return tree1
  


class saService(baseService):
  '''Our ServerAdmin service object. This object is responsible
  for performing and organizing backups for an individual service'''   

  serverAdminPath = "/usr/sbin/serveradmin"  

  def __init__(self,name="",backupPath=""):
    """Our construct"""
    self.servicesMap = {
        "info" : "Server",
        "accounts" : "Lion Account Management",
        "addressbook" : "Address Book",
        "afp" : "AFP",
        "backup" : "Backup",
        "devicemgr" : "Mobile Device Management",
        "dhcp" : "DHCP",
        "dns" : "DNS", 
        "ipfilter" : "Firewall",
        "ftp" : "FTP",
        "calendar" : "iCal",
        "jabber" : "iChat",
        "sharing" : "File Sharing",
        "mail" : "Mail", 
        "mysql" : "MySQL",
        "postgres" : "PostreSQL",
        "nat" : "NAT",
        "netboot" : "NetBoot",
        "notification" : "Notification",
        "nfs" : "NFS",
        "dirserv" : "Open Directory",
        "pcast" : "PodCast Producer",
        "print" : "Print",
        "qtss" : "QuickTime Streaming",
        "radius" : "RADIUS",
        "sharing" : "Sharepoint Definitions",
        "smb" : "SMB",
        "swupdate" : "Software Update",
        "vpn" : "VPN",
        "web" : "Web",
        "webobjects" : "WebObjects",
        "wiki" : "Wiki Services",
        "xgrid" : "Xgrid"
    }
    baseService.__init__(self,name=name,backupPath=backupPath)
    self.plist = {}
    self.canPrune = True
  
    return
    
  def load(self):
    """ Loads our object from serveradmin """
    
    name = self.name
    displayName = self.displayName
    serverAdminPath = self.serverAdminPath
       
    if not name or not displayName:
      self.logger("load() could not perform backup: name or"
      + " displayName not set!","error")
    if not os.path.isfile(serverAdminPath):
      self.logger("backupSettings() Could not find serveradmin at path:'%s', cannot continue!" % serverAdminPath,"error")
      return False

    ## We have passed sanity checks.     
    saCMD = subprocess.Popen('"%s" -x settings "%s"' 
        % (serverAdminPath,name),shell=True,
          stdout=subprocess.PIPE,universal_newlines=True)
    saCMD_STDOUT, saCMD_STDERR = saCMD.communicate()
    
    ## This is where it actually dumps the settings
    if len(saCMD_STDOUT) == 0:
      ##self.logger("backupSettings() '%s -x settings \"%s\"'  "
      ##  +"returned null string! " % (serverAdminPath,name),"error")
      self.logger("serveradmin returned null string!","error")
      return False
    ## initialize our new dictionary
    plistDict = self.plist

    ## Create a plist object from our output.
    plistObj = plistlib.readPlistFromString(saCMD_STDOUT)
    if "configuration" in plistObj:
      plistDict["%s Config" % displayName] = plistObj["configuration"]
    elif "%s Config" % displayName in plistObj:
      plistDict["%s Config" % displayName] = plistObj["%s Config" % displayName]
    else:
      self.logger("Could not interpret XML for '%s', key 'configuration' is not present!" % displayName,"error")
      return False
    self.plist = plistDict
    self.isLoaded = True
    self.loadedServices.append(name)
  
  def loadFromPath(self,path):
    """ Loads our object from a specified path. If a file is provided, it will
    be passed to self.loadFromFile(), if a directory is provided, we attempt
    to determine the appropriate subfile, and pass that to self.loadFromFile()"""
    
    name = self.name
    displayName = self.displayName
    
    if not os.path.exists(path):
      self.logger("Path: '%s' does not exist, cannot continue!" % path,"error")
      return False
    
    if os.path.isfile(path):
      return self.loadFromFile(filePath=path)
    
    plistFileList = glob.glob(os.path.join(path, "*.plist"))
    if len(plistFileList) == 0:
      self.logger("No plist files could be found at path: '%s', cannot continue!" % path,"error")
      return False
    for file in plistFileList:
      filePath = file
      fileName = os.path.splitext(file)
      if fileName == "sa_%s_latest.plist" % self.name or fileName == "latest.plist":
        break
      elif fileName == "sa_global.plist":
        break

    return self.loadFromFile(filePath=filePath)
              
  def loadFromFile(self,filePath):
    """ Loads our object from serveradmin """
    
    name = self.name
    displayName = self.displayName
    
    self.logger("%s: loading from file: %s" % (displayName,filePath))
    
    ## initialize our dict
    plistDict = {}
    if os.path.isfile(filePath):
      try:
        plistObj = plistlib.readPlist(filePath)
      except:
        self.logger("loadFromFile() Error Reading File!","error")
        return False
      if "configuration" in plistObj and len(plistObj) == 1:
        if not name or not displayName:
          self.logger("loadFromFile() could not load: name or"
          + " displayName not set!","error")
          return False        ## Here if this is captured output from serveradmin utility.
        plistDict["%s Config" % displayName] = plistObj["configuration"]
      elif "%s Config" % displayName in plistObj:
        plistDict["%s Config" % displayName] = plistObj["%s Config" % displayName]
      elif displayName in plistObj:
        plistDict[displayName] = plistObj[displayName]
      else:
        ## Here for GUI export, processed plists
        for configName in plistObj:
          ## See if the configName is a defined service.
          ##type(configName)
          isService = False
          ##print "Comparing '%s':" % configName
          for serviceName,displayName in self.servicesMap.iteritems():
            testConfigName = "%s Config" % displayName
            ##print "  Against:%s" % testConfigName

            if configName == testConfigName:
              isService = True
              break
          if isService:
            plistDict[configName] = plistObj[configName]
            self.loadedServices.append(serviceName)
          elif configName: 
            self.logger("loadFromFile() did not load config:"
              + "'%s', it is not registered!" % configName,"error")
    else:
      self.logger("Could not find file at path:'%s'" % filePath)
      return False
          
       
    if len(plistDict) > 0:
      self.plist = plistDict
      self.isLoaded = True

    return True
                                
  def valueForKeyPath(self,keyPath=""):
    """Returns value for key"""
    
    try:
      aliasValue = valueForKeyPath(keyPath)
      return aliasValue
    except:
      self.logger("No alias registered for keyPath:%s" % keyPath,"debug")
      pass
    
    name = self.name
    displayName = self.displayName

    currentValue = self.plist["%s Config" % displayName]

    if not keyPath:
      return currentValue

    keyArray = keyPath.split(".")
    
    
    for key in keyArray:
      try:
        currentValue = currentValue[key]
      except Exception, err:
        self.logger("Keypath: %s does not exist!" % keyPath,"error")
        self.logger("Exception: %s" % err,"debug")
        return False
        
    return currentValue
    
      
  def backupSettings(self):
    """ Perform our server admin backup"""
    if not self.isLoaded:
      self.load()  
    
    backupPath = self.backupPath
    name = self.name
    if not self.baseName:
      self.baseName = "sa_%s" % name
    baseName = self.baseName
      
    displayName = self.displayName
    serverAdminPath = self.serverAdminPath
    
    if not name or not displayName or not backupPath:
      self.logger("backupSettings() could not perform backup: name,"
      + "displayName, or backupPath not set!","error")    
    if not os.path.isdir(os.path.dirname(backupPath)):
      self.logger("backupSettings() could not perform backup: Directory '%s'"
      " does not exist!" % os.path.dirname(backupPath),"error")
    if not os.path.exists(backupPath):
      try:
        os.mkdir(backupPath)
      except:
        self.logger("backupSettings() failed creating directory:'%s', cannot continue!" % backupPath,"error")
        return False
        
    if not os.path.isfile(serverAdminPath):
      self.logger("backupSettings() Could not find serveradmin at path:'%s', cannot continue!" % serverAdminPath,"error")
      return False
    
    ## Set our backup filename. Example: sa_afp_20091228_2243
    if self.useTimeStamps:
      if self.timeStamp:
        backupFileName = "%s_%s.plist" % (baseName,self.timeStamp)
      else:
        backupdt = datetime.datetime.today()
        backupFileName = "%s_%02d%02d%02d_%02d%02d.plist" % (baseName,
                                                        backupdt.year,
                                                        backupdt.month,
                                                        backupdt.day,
                                                        backupdt.hour,
                                                        backupdt.minute)
    else:
      backupFileName = "%s.plist" % baseName
    
    backupFile = os.path.join(backupPath,backupFileName)
                                                        
    ## We have passed sanity checks. 
    self.logger("Backing up %s to '%s'" % (name,backupFile))
    
    ## fetch our plist
    plistDict = self.plist
    
    if not self.plist or len(self.plist) == 0:
      self.logger("backupSettings() Object contains no data","error")

    if not os.path.exists(backupFile) or self.overWriteExistingFiles:
      try:
        plistlib.writePlist(plistDict,backupFile)
      except:
        self.logger("Unknown error writing file:'%s'" % backupFile)
        return False
    else:
      self.logger("Could not backup, file already exists at:'%s'" % backupFile,"error")
      return False
    
    ## Check for our 'latest.plist' file
    if self.useTimeStamps:
      latestFile = os.path.join(backupPath,"latest.plist")
      if os.path.lexists(latestFile):
        try:
          os.remove(latestFile)
        except IOError, strerror:
          self.logger("Could remove file latest.plist! Error:'%s'" % (plist,strerror))
          return False
        except:
          self.logger("An unknown error occured reading data from plist","error")
          return False
      try:
        os.link(backupFile,latestFile)
      except IOError, strerror:
        self.logger("Could not create hard link to latest.plist! Error:'%s'" % (plist,strerror))
        return False
      except:
        self.logger("An unknown error occured reading data from plist","error")
        return False
    
    return True
  
  def restoreSettings(self):
    """ Perform our server admin restore"""
    if not self.isLoaded:
      self.load()  

    backupPath = self.backupPath
    name = self.name
    if not self.baseName:
      self.baseName = "sa_%s" % name
    baseName = self.baseName

    displayName = self.displayName
    serverAdminPath = self.serverAdminPath
  
  def getRunningServiceList(self=""):
    """ Function which returns a list of names of running services """
    
    runningServices = []
    serverAdminPath = self.serverAdminPath
    
    self.logger("Determining running services for Server Admin", "detailed")
    
    ## Check running userid, if it's not root, exit
    if not os.geteuid() == 0:
      self.logger("Server Admin must be run as root!","error")
      return False
    
    if not os.path.isfile(serverAdminPath):
      self.logger("Could not find serveradmin at path:'%s', cannot backup Server Admin!" % serverAdminPath,"error")
      return False
    
    for name,displayName in self.servicesMap.iteritems():
      if name == "info":
        runningServices.append(name)
        continue
      saCMD = subprocess.Popen('"%s" -x status "%s"' % (serverAdminPath,name),shell=True,stdout=subprocess.PIPE,universal_newlines=True)
      saCMD_STDOUT, saCMD_STDERR = saCMD.communicate()
      if len(saCMD_STDOUT) == 0:
        ##self.logger("backupSettings() '%s -x settings \"%s\"'  returned null string! " % (serverAdminPath,name),"error")
        self.logger("serveradmin: could not determine status for:'%s'!" % name,"warning")
        continue
      else:
        ## Create a plist object from our output.
        try:
          plistObj = plistlib.readPlistFromString(saCMD_STDOUT)
          if "state" in plistObj:
            if plistObj["state"] == "RUNNING":
              runningServices.append(name)
        except:
          self.logger("serveradmin: could not read status XML for:'%s'!" % name,"error")
    
    ## If we have any file-sharing based services, make sure we backup shares
    if ("afp" or "ftp" or "nfs" or "smb") in runningServices:
      runningServices.append("sharing")
    
    if len(runningServices) == 0:
      self.logger("serveradmin: found no running services!","error")
    
    return runningServices

class xsanService(baseService):
  '''Our Xsan root object. This object is responsible for performing and 
  organizing backups for the Xsan Service'''
  
  xsanConfigDir="/Library/Filesystems/xsan"
  backupPaths = ["config/",
                  "/etc/systemserialnumbers/xsan",
                ]
    
  isMetadataController = False
  
  def __init__(self,name="xsan",backupPath=""):
    '''Our construct'''
    self.isMetadataController = False
    self.xsanConfigDir="/Library/Filesystems/xsan"
    self.servicesMap = { "xsan" : "Xsan" }
    baseService.__init__(self,name,backupPath)
    self.canPrune = True
    self.debug = False
    self.plist = {}

  def loadFromPath(self,path):
    """ Loads our object from a specified path. If a file is provided, it will
    be passed to self.loadFromFile(), if a directory is provided, we attempt
    to determine the appropriate subfile, and pass that to self.loadFromFile()"""
    
    name = self.name
    displayName = self.displayName
    
    loadError = False
    
    if not os.path.exists(path):
      self.logger("Path: '%s' does not exist, cannot continue!","error")
      return False
      
    ## Get our latest directory from path.
    if os.path.exists(os.path.join(path,"xsan_latest")):
      path = os.path.join(path,"xsan_latest")
    
    ## Load our config.plist file
    configPlistFile = os.path.join(path,"config","config.plist")
    if os.path.isfile(configPlistFile):
      try:
        self._loadXsanConfigFromFilePath(configPlistFile)
      except Exception,err:
        self.logger("loadFromPath() error loading config.plist file. Error: %s"
             % err,"error")
        loadError = True
    
    ## Load all volume.cfg files
    cfgFileList = glob.glob(os.path.join(path,"config","*.cfg"))
    for cfgFile in cfgFileList:
      try:
        self._loadXsanVolumeConfigFromFilePath(cfgFile)
      except Exception,err:
        self.logger("loadFromPath() error loading volume config file: %s. "
          "Error: %s" % (cfgFile,err),"error")
        loadError = True

    plistFileList = glob.glob(os.path.join(path,"config","*-auxdata.plist"))
    for plistFile in plistFileList:
      try:
        self._loadXsanVolumeAuxDataFromFilePath(plistFile)
      except Exception,err:
        self.logger("loadFromPath() error loading volume auxdata file: %s. "
            "Error: %s" % (plistFile,err),"error")
      loadError = True

      
    ## Load cvlabel file if found
    cvLabelFilePath = os.path.join(path,"cvlabel_output.txt")
    if os.path.isfile(cvLabelFilePath):
      try:
        self._loadXsanCVLabelFromFilePath(cvLabelFilePath)
      except Exception,err:
        self.logger("loadFromPath() error loading volume cvlabel file: "
            "%s. Error: %s" % (cvLabelFilePath,err),"error")
        loadError = True

    return not loadError
  
  def _loadXsanConfigFromFilePath(self,filePath):
    """Loads data into our local plist var based upon an Xsan config.plist file.
    This data is stored at self.plist["config"]"""
    
    if not "Clients" in self.plist:
      self.plist["Clients"] = {}
    clientList = self.plist["Clients"]

    if not "Serials" in self.plist:
      self.plist["Serials"] = {}
    serialList = self.plist["Serials"]
    
    if not "Info" in self.plist:
      self.plist["Info"] = {}
    infoList = self.plist["Info"]
      
    self.logger("Loading information from config.plist file at:%s" % filePath,"debug")

    ## Read in the plist file with plistlib  
    try:
      plistObj = plistlib.readPlist(filePath)
    except Exception, err:
      raise RuntimeError("_loadXsanConfigFromFile() Error Reading File: '%s' error: %s" % (filePath,err))
    
    ## Read in computer information
    try:
      for computer in plistObj["computers"]:
        myComputer = {}
        computerName = computer["name"]
        if not computerName in clientList:
          myComputer["config.plist"] = computer 
          myComputer["hostname"] = computer["legacyHostName"]
          myComputer["name"] = computer["name"]
          myComputer["primaryIP"] = computer["ipAddresses"][0]
          myComputer["metaIP"] = computer["ipAddresses"][1]
          myComputer["role"] = "client"
          myComputer["uuid"] = computer["uuid"]
          clientList[computerName] = myComputer
        else:
          self.logger("Computer with name: %s has already been defined!" % computerName,"debug")
          myComputer = clientList[computerName]
          if not myComputer["hostname"] == computer["legacyHostName"]:
            self.logger("Computer hostname mismatch: updating %s to %s" % (myComputer["hostname"],computer["legacyHostName"]),"warning")
            myComputer["hostname"] = computer["legacyHostName"]
          if not myComputer["name"] == computer["name"]:
            self.logger("Computer name mismatch: updating %s to %s" % (myComputer["name"],computer["name"]),"warning")
            myComputer["name"] = computer["name"]
          if not myComputer["primaryIP"] == computer["primaryIP"]:
            self.logger("Computer Primary IP mismatch: updating %s to %s" % (myComputer["primaryIP"],computer["primaryIP"]),"warning")
            myComputer["primaryIP"] = computer["primaryIP"]
          if not myComputer["metaIP"] == computer["metaIP"]:
            self.logger("Computer metadata IP mismatch: updating %s to %s" % (myComputer["metaIP"],computer["metaIP"]),"warning")
            myComputer["metaIP"] = computer["metaIP"]
    except Exception, err:
      raise RuntimeError("_loadXsanConfigFromFile() Error Reading Computer information: %s" % err)

    ## Read in serialNumber information
    try:
      for serialNumberEntry in plistObj["serialNumbers"]:
        mySerial = {}
        serialNumber = serialNumberEntry["license"]
        if serialNumber in serialList:
          mySerial = serialList[serialNumber]
          mySerial["license"] = serialNumber
          if not "organization" in mySerial:
            mySerial["organization"] = serialNumberEntry["organization"]
          if not "registeredTo" in mySerial:
            mySerial["registeredTo"] = serialNumberEntry["registeredTo"]
        else:
          mySerial["license"] = serialNumber
          mySerial["organization"] = serialNumberEntry["organization"]
          mySerial["registeredTo"] = serialNumberEntry["registeredTo"] 
          serialList[serialNumber] = mySerial  
                 
    except Exception, err:
      raise RuntimeError("_loadXsanConfigFromFile() Error Reading Serial Number information: %s" % err)
    
    ## Read in generic information
    if "metadataNetwork" in plistObj:
      if "metadataNetwork" in infoList and not infoList["metadataNetwork"] == plistObj["metadataNetwork"]:
        self.logger("_loadXsanConfigFromFile() metadataNetwork conflicts with"
                      " previously defined setting. Current value:"
                      " %s New Value: %s" % (infoList["metadataNetwork"],
                                              plistObj["metadataNetwork"])
                      ,"warning")
      infoList["metadataNetwork"] = plistObj["metadataNetwork"]

    if "ownerEmail" in plistObj:
      if "ownerEmail" in infoList and not infoList["ownerEmail"] == plistObj["ownerEmail"]:
        self.logger("_loadXsanConfigFromFile() ownerEmail conflicts with"
                      " previously defined setting. Current value:"
                      " %s New Value: %s" % (infoList["ownerEmail"],
                                              plistObj["ownerEmail"])
                      ,"warning")
      infoList["ownerEmail"] = plistObj["ownerEmail"] 

    if "sanName" in plistObj:
      if "sanName" in infoList and not infoList["sanName"] == plistObj["sanName"]:
        self.logger("_loadXsanConfigFromFile() sanName conflicts with"
                      " previously defined setting. Current value:"
                      " %s New Value: %s" % (infoList["sanName"],
                                              plistObj["sanName"])
                      ,"warning")
      infoList["sanName"] = plistObj["sanName"] 
    return True
    
    
    
  def _loadXsanCVLabelFromFilePath(self,filePath):
    """Loads data into our local plist var based upon an Xsan cvlabel output.
        This data is stored at self.plist["LUNs"]"""
    
    if "LUNs" in self.plist:
      LUNlist = self.plist["LUNs"]
    else:
      self.plist["LUNs"] = {}
      LUNlist = self.plist["LUNs"]
      
    self.logger("Loading information from cvlabel output at:%s" % filePath,"debug")
    
    cvLabelFH = open(filePath,"r")
    for row in cvLabelFH:
      myLun = {}
      reMatch = re.search("^(\/dev\/.*)\ \[(.*)\] acfs \"(.*)\""
                    + ".*Controller\#: \'(.*)\' Serial\#: \'(.*)\' "
                    + "Sectors: (.*)\. SectorSize: (.*?)\.",row)
      myLun["deviceNode"] = reMatch.groups()[0]
      myLun["deviceType"] = reMatch.groups()[1]
      lunLabel = reMatch.groups()[2]
      myLun["label"] = lunLabel      
      myLun["controller"] = reMatch.groups()[3]
      myLun["serial"] = reMatch.groups()[4]
      myLun["sectors"] = int(reMatch.groups()[5])
      myLun["sectorSize"] = int(reMatch.groups()[6])
      myLun["size"] = myLun["sectors"] * myLun["sectorSize"]
      if lunLabel in LUNlist:
        self.logger("LUN with label: %s has already been defined" % lunLabel,"debug")
        try:
          for key,value in myLun:
            if key in LUNlist[lunLabel] and not LUNlist[lunLabel][key] == value:
              self.logger("LUN with label: %s has already had key: %s set to value: %s, changing to %s" % (lunLabel,key,LUNlist[lunLabel][key],value),"warning")
            LUNlist[lunLabel][key] = value
        except:
          self.logger("Error readining myLun:%s" % myLun,"warning")
          
      else:
        LUNlist[lunLabel] = myLun
      
    
    self.plist["LUNs"] = LUNlist
    return True
      
  def _loadXsanVolumeConfigFromFilePath(self,filePath):
    """Loads data into our local plist var based upon the specified
    Xsan volume.cfg files found at filePath. This function will also read in 
    any found volume-auxdata.plist file as well, if found.
    This data is stored at self.plist["volumes"]["volumeName"]"""

    if "Volumes" in self.plist:
      volumeList = self.plist["Volumes"]
    else:
      self.plist["Volumes"] = {}
      volumeList = self.plist["Volumes"]
      
    self.logger("Loading information from Xsan Volume config file:%s" % filePath,"debug")
    
    volumeName = os.path.splitext(os.path.basename(filePath))[0]

    myVolumeData = {}
    myVolumeData["global"] = {}

    myVolumeData["volumeName"] = volumeName

    ## Read the volume.cfg file
    cvLabelFH = open(filePath,"r")
    currentSection = myVolumeData["global"]
    for row in cvLabelFH:
      myLun = {}
      
      ''' Do a search for new section header [StripeGroup "test"], if found
      iterate currentSection ( == i.e.  myVolumeData["global"] 
                                      or ["StripeGroup"]["test"])
      '''
      sectionMatch = re.search("^\[(.*?)\s*?\"(.*?)\"\]",row)
      try:
        sectionGroup = sectionMatch.groups()[0]
        sectionName = sectionMatch.groups()[1]
        if not sectionGroup in myVolumeData:
          myVolumeData[sectionGroup] = {}
        if not sectionName in myVolumeData[sectionGroup]:
          myVolumeData[sectionGroup][sectionName] = {}
        ## iterate currentSection, as mentioned
        currentSection = myVolumeData[sectionGroup][sectionName]
        continue
      except:
        pass
      
      ## Do a search for non-commented key value pairs   
      try:
        reMatch = re.search("^([^\#].*?)\s{1,4}(.*)$",row)
        key = reMatch.groups()[0]
        value = reMatch.groups()[1]
        ## add them to currentSection
        if key == "Node":
          if not key in currentSection:
            currentSection[key] = []
          reMatch = re.search("^\"(.*?)\".*$",value)
          nodeName = reMatch.groups()[0]
          currentSection[key].append(nodeName)
        else:
          currentSection[key] = value
        
            
      except:
        self.logger("_loadXsanVolumeConfigFromFilePath() Skipping line:\n%s" 
                    % row ,"debug")
    
    if not volumeName in volumeList:
      volumeList[volumeName] = myVolumeData
    else:
      self.logger("Volume with name: %s already defined, merging records","detailed")
      myNewVolumeData = self.mergeTrees(myVolumeData,volumeList[volumeName])
      volumeList[volumeName] = myNewVolumeData
    
    return volumeList[volumeName]
      
 
  def _loadXsanVolumeAuxDataFromFilePath(self,filePath):
    """Loads data into our local plist var based upon the specified
    Xsan volume-auxdata.plist file found at filePath.
    This data is stored at self.plist["volumes"]["volumeName"]""" 
    
    if "Volumes" in self.plist:
      volumeList = self.plist["Volumes"]
    else:
      self.plist["Volumes"] = {}
      volumeList = self.plist["Volumes"]
      
    self.logger("Loading information from Xsan Volume config file:%s" % filePath,"debug")
    
    reMatch = re.search("^(.*?)-auxdata.plist",os.path.basename(filePath))
    volumeName = reMatch.groups()[0]

    myVolumeData = {}
    myVolumeData["auxData"] = {}
    myVolumeData["volumeName"] = volumeName
    
    auxData = myVolumeData["auxData"]

    ## Read in the plist file with plistlib  
    try:
      plistObj = plistlib.readPlist(filePath)
    except Exception, err:
      raise RuntimeError
      
    ## Read in volume information
    try:
      auxData["Config"] = plistObj["Config"]
      auxData["FailoverPriorities"] = plistObj["FailoverPriorities"]
    except Exception, err:
      raise RuntimeError("_loadXsanVolumeAuxDataFromFilePath() Error Reading Computer information: %s" % err)

    if volumeName in volumeList:
      mergedVolumeData = self.mergeTrees(volumeList[volumeName],myVolumeData)
      volumeList[volumeName] = mergedVolumeData
    else:
      volumeList[volumeName] = myVolumeData
    return True
    
  def _calculateVolumeSize(self,volumeName):
    """Returns total volume size for passed volume name. We determine this by
    analyzing the volume configuration and aggregating any LUNs defined as nodes
    in non-metadata and journal stripe groups"""
    ## calculate the size from the volume configuration
    
    self.logger("_calculateVolumeSize() calculating size for volume:'%s'"%volumeName)
    
    dataNodes = []
    LUNs = {}

    ## Get our stripegroup nodes.
    try:
      stripeGroups = self.valueForKeyPath("Volumes.%s.StripeGroup" % volumeName)
      for stripeGroupName,stripeGroupData in stripeGroups.iteritems():
        if (stripeGroupName == "MetadataAndJournal"
          or stripeGroupName == "Journal"
          or stripeGroupName == "Metadata"):
            continue
        if "Node" in stripeGroupData:
          for node in stripeGroupData["Node"]:
            self.logger("Found node:%s for stripegroup:%s" % (node,stripeGroupName))
            dataNodes.append(node)
            if not node in LUNs:
              LUNs[node] = {'label':node}
      
      for node in dataNodes:
        disks = self.valueForKeyPath("Volumes.%s.Disk" % volumeName)
        if not node in disks:
          self.logger("Could not find disktype for node:'%s'" % node,"error")
        self.logger("Found disktype:'%s' for node:'%s'" % (disks[node]["Type"],node),"error")
        myLun = LUNs[node]
        diskType = disks[node]["Type"].strip("\"")
        myLun["Type"] = diskType
        diskType = self.valueForKeyPath("Volumes.%s.DiskType" % volumeName)
        myLun["sectorSize"] = diskType[node]["SectorSize"]
        myLun["sectors"] = diskType[node]["Sectors"]
        myLun["size"] =  myLun["sectors"] * myLun["sectorSize"]

    except Exception,err:
      self.logger("Could not load LUN information for volume:'%s' Error:%s" % (volumeName,err),"error")
      raise RuntimeError(self.lastError)

    volumeSize = 0
    try:
      for label,lun in LUNs.iteritems():
        volumeSize += lun["size"]
    except:
      self.logger("Error calculating size for volume:'%s'" % volumeName,"error")
      raise RuntimeError(self.lastError)

    return volumeSize
  
  def valueForAliasKeyPath(self,keyPath=""):
    """Returns a value for keyPath based upon a specific keyPath alias
    This function primarily serves as an override method for valueForKeyPath
    where manipulation of stored data is replied (concatanation of fields,
    mathematics, etc..."""
      
    keyPathArray = keyPath.split(".")
    if keyPathArray[0] == "Volumes":
      if len(keyPathArray) == 3:
        if keyPathArray[2] == "size":
          volumeName = keyPathArray[1]
          self.logger("valueForAliasKeyPath(): calculating size for volume:'%s'" % volumeName,"debug")    
          return self._calculateVolumeSize(volumeName)
            
        try:
          newKeyPath = "Volumes.%s.global.%s" % (keyPathArray[1],keyPathArray[2])
          theValue = self.valueForKeyPath(newKeyPath)
        except: 
          newKeyPath = "Volumes.%s.auxData.Config.%s" % (keyPathArray[1],keyPathArray[2])
          theValue = self.valueForKeyPath(newKeyPath)

      else:
        if keyPathArray[2] == "cfg":
          try:
            newKeyPath = "Volumes.%s.global.%s" % (keyPathArray[1],
                                                  ".".join(keyPathArray[3:]))
            theValue = self.valueForKeyPath(newKeyPath)
          except:
            newKeyPath = "Volumes.%s.auxData.Config.%s" % (keyPathArray[1],
                                                  ".".join(keyPathArray[3:]))
            theValue = self.valueForKeyPath(newKeyPath)

                                                  
      self.logger("valueForAliasKeyPath: returning keyPath: %s from keyPath: %s" % (newKeyPath,keyPath),"debug")    
      return theValue
    else:
      raise RuntimeError("No alias for keypath: %s" % keyPath)

    
  def valueForKeyPath(self,keyPath):
    """Returns value for key"""
    
    try:
      aliasValue = self.valueForAliasKeyPath(keyPath)
      return aliasValue
    except:
      self.logger("No alias registered for keyPath:%s" % keyPath,"debug")
      pass
    
    keyArray = keyPath.split(".")
    myPlist = self.plist
    
    if len(keyArray) == 0:
      return myPlist
    
    self.logger("valueForKeyPath() hit for keyPath: %s" % keyPath,"debug")
        
    dataTypeDict = myPlist
    currentItem = dataTypeDict
    
    self.logger("valueForKeyPath() keyArray len: %s" % len(keyArray),"debug")

    if len(keyArray) == 0:
      return currentItem
    
    for key in keyArray:
      ## If the current item is an array and our key is not an integer
      ## then grab the first value
      self.logger("valueForKeyPath: processing key element: '%s'" % key,"debug")
      if type(currentItem) == type([]):
        try:
          intKey = int(key)
          currentItem = currentItem[intKey]
          continue
        except:
          currentItem = currentItem[0]
        
      try:
        currentItem = currentItem[key]
      except Exception, err:
        ## Todo: restructure this so that we toss an exception if key doesn't exist
        ##self.logger("Keypath: %s does not exist!" % keyPath,"error")
        ##self.logger("Exception: %s" % err,"debug")
        raise RuntimeError("Keypath: %s does not exist!" % keyPath)
    return currentItem
    
  def getRunningServiceList(self=""):
    if os.path.exists(self.xsanConfigDir):
      return ["xsan"]
    else:
      return []  

  def backupSettings(self):
    '''Function which performs our backup'''

    backupPath = self.backupPath
    name = self.name
    displayName = self.displayName
    baseName = self.baseName
    if not baseName:
      baseName = name
      
    xsanConfigDir = self.xsanConfigDir
    
    errorOccured = False
    
    if not os.path.exists(self.xsanConfigDir):
      self.logger("Cannot perform backup: Xsan is not installed!","error")
      self.logger("  - no directory exists at '%s'" % self.xsanConfigDir,"debug")
      return False
    if not name or not displayName or not backupPath:
      self.logger("backupSettings() could not perform backup: name,"
      + "displayName, or backupPath not set!","error")    
    if not os.path.isdir(os.path.dirname(backupPath)):
      self.logger("backupSettings() could not perform backup: Directory '%s'"
      " does not exist!" % os.path.dirname(backupPath),"error")
    if not os.path.exists(backupPath):
      try:
        os.mkdir(backupPath)
      except:
        self.logger("backupSettings() failed creating directory:'%s', cannot continue!" % backupPath,"error")
        return False
        
    ## Set our backup filename. Example: sa_afp_20091228_2243
    if self.useTimeStamps:
      if self.timeStamp:
        backupFolderName = "%s_%s" % (baseName,self.timeStamp)
      else:
        backupdt = datetime.datetime.today()
        backupFolderName = "%s_%02d%02d%02d_%02d%02d" % (baseName,
                                                        backupdt.year,
                                                        backupdt.month,
                                                        backupdt.day,
                                                        backupdt.hour,
                                                        backupdt.minute)
    else:
      backupFolderName = "%s" % name
      
    backupTargetDir = os.path.join(backupPath,backupFolderName)
    if not os.path.exists(backupTargetDir):
      try:
        os.mkdir(backupTargetDir)
      except:
        self.logger("backupSettings() failed creating directory:'%s',"
                      "cannot continue!" % backupTargetDir,"error")
        return False
    
    ## We have passed sanity checks. 
    self.logger("Backing up %s to '%s'" % (name,backupTargetDir))
    
    ## Iterate through all of our backupPaths and copy them over
    for backupItem in self.backupPaths:
      self.logger(" - hit backupItem: '%s'" % backupItem,"debug")
      
      if backupItem[0:1] == "/":
        backupItemList = [backupItem]
      else:
        backupItemList = glob.glob(os.path.join(xsanConfigDir,backupItem))
      ##self.logger(" * matched arrays: '%s'" % backupItemList,"debug")
      ## If it's a directory, make sure there's no trailing solodus
      if backupItem[-1:] == "/":
          backupItem = backupItem[:-1]
      
      
      for backupItemPath in backupItemList:
        self.logger("   - file match: '%s'" % backupItemPath,"debug")
        ## recreate our relative path
        if backupItemPath[-1:] == "/":
          backupItemPath = backupItemPath[:-1]
          
        itemPathArray = os.path.split(backupItem)
        
        if len(itemPathArray) == 1:
          myDirString = ""
          myName = itemPathArray[0]
          myRelPath = myName
        else:
          myDirString = itemPathArray[0]
          myName = itemPathArray[1]
          
          if myDirString[0:1] == "/":
            myRelPath = os.path.join(myDirString,myName)
            myDirString = myDirString[1:]
          else:
            myRelPath = os.path.join(myDirString,myName)


        targetItemDir = os.path.join(backupTargetDir,myDirString)
        targetItemPath = os.path.join(targetItemDir,myName)
    
        if not os.path.exists(targetItemDir):
          try:
            self.logger("Creating folder: %s" % targetItemDir,"debug")
            os.makedirs(targetItemDir)
          except:
            self.logger("Failed creating directory:'%s',"
                          "cannot continue!" % targetItemDir,"error")
            return False

        self.logger("backupTargetDir:%s, myDirString:%s, myName:%s" % (backupTargetDir,myDirString,myName),"debug2")
        
        if os.path.exists(backupItemPath):
          self.logger("Backing up %s" % myRelPath,"detailed")
          try:
            if os.path.isdir(backupItemPath):
              shutil.copytree(backupItemPath,targetItemPath)
            else:
              shutil.copy2(backupItemPath,targetItemPath)
            self.logger(" - Finished","detailed")

          except Exception, err:
            self.logger("An error occurred copying '%s' to '%s'. Error: %s" % (backupItemPath,targetItemPath,err),"error")
            errorOccured = True
          
        else:
          self.logger("No file found at '%s'" % backupItemPath,"warning")
          errorOccured = True

          
          

    ## Perform our ad-hoc backups, get a cvlabel -l output
    cvlabelPath = os.path.join(self.xsanConfigDir,"bin/cvlabel")
    cvlabelCMDString = "%s -ls" % cvlabelPath
    
    self.logger("Backing up '%s' output" % cvlabelCMDString)
    
    cvlabelCMD = subprocess.Popen(cvlabelCMDString,shell=True,stdout=subprocess.PIPE,universal_newlines=True)
    cvlabelCMD_STDOUT, cvlabelCMD_STDERR = cvlabelCMD.communicate()
    
    cvlabelDidWrite = False
    if cvlabelCMD_STDOUT:
      try:
        cvlabelFilePath = os.path.join(backupTargetDir,"cvlabel_output.txt")
        cvlabelFH = codecs.open(cvlabelFilePath,"w","utf-8")
        cvlabelFH.write(cvlabelCMD_STDOUT)
        cvlabelFH.close()
        cvlabelDidWrite = True
      except Exception, err:
        self.logger("An error occured writing cvlabel output! Error:%s" % err,"debug")
        errorOccured = True
    else:
      self.logger("cvlabel produced no output!","error")
      errorOccured = True
    
    ## Create a symlink for our latest file
    if self.useTimeStamps:
      latestDirName="%s_latest" % baseName
      self.logger("Updating %s" % latestDirName,"detailed")
      
      latestDirPath = os.path.join(backupPath,latestDirName)
      if os.path.lexists(latestDirPath):
        if os.path.isfile(latestDirPath) or os.path.islink(latestDirPath):
          try:
            os.unlink(latestDirPath)
          except Exception,err:
            self.logger("Couldn't remove link %s! Error:%s" % (latestDirName,err),"error")
            return False     
        else:
            self.logger("Unexpected directory found at: %s" % (latestDirPath),"error")
            return False
            
      try:
        self.logger("linking %s to %s" % (backupTargetDir,latestDirName),"detailed")
        os.symlink(os.path.basename(backupTargetDir),latestDirPath)
      except IOError, strerror:
        self.logger("Could not create symlink to %s! Error:'%s'" % (latestDirName,strerror))
        return False
      except Exception, err:
        self.logger("An error occured creating symlink for %s: %s" % (latestDirName,err),"error")
        return False
    
    return True

    
class systemProfilerService(baseService):
  '''Our Xsan root object. This object is responsible for performing and 
  organizing backups for the Xsan Service'''
  
  systemProfilerCMDPath="/usr/sbin/system_profiler"
  servicesMap = { "profile" : "System Profile" }
  systemProfilerDataTypes = ["SPHardwareDataType",
                        "SPEthernetDataType",
                        "SPFibreChannelType",
                        "SPNetworkDataType",
                        "SPHardwareRAIDDataType",
                        "SPMemoryDataType",
                        "SPPCCardDataType",
                        "SPPCIDataType",
                        "SPPowerDataType",
                        "SPSASDataType",
                        "SPAirPortDataType",
                        "SPNetworkLocationDataType",
                        "SPSoftwareDataType"
                        ]
  
  
  isMetadataController = False
  
  def __init__(self,name="profile",backupPath=""):
    '''Our construct'''
    self.servicesMap = { "profile" : "System Profile" }
    self.baseName = "system_profiler"
    baseService.__init__(self,name,backupPath)
    self.plist = []
    self.canPrune = True

  def loadFromPath(self,path):
    """ Loads our object from a specified path. If a file is provided, it will
    be passed to self.loadFromFile(), if a directory is provided, we attempt
    to determine the appropriate subfile, and pass that to self.loadFromFile() """
    
    name = self.name
    displayName = self.displayName
    
    if not os.path.exists(path):
      self.logger("Path: '%s' does not exist, cannot continue!","error")
      return False
    
    if os.path.isfile(path):
      return self.loadFromFile(filePath=path)
    
    plistFileList = glob.glob(os.path.join(path, "*.plist"))
    if len(plistFileList) == 0:
      self.logger("No plist files could be found at path: '%s', cannot continue!" % path,"error")
      return False
    for file in plistFileList:
      filePath = file
      fileName = os.path.splitext(file)
      if fileName == "%s_latest.plist" % self.name or fileName == "latest.plist":
        break
      elif fileName == "sa_global.plist":
        break

    return self.loadFromFile(filePath=filePath)
    
  def loadFromFile(self,filePath):
    """ Loads our object from serveradmin """
    
    name = self.name
    displayName = self.displayName
    
    ## initialize our dict
    if os.path.isfile(filePath):
      try:
        plistObj = plistlib.readPlist(filePath)
        plist = []
        plist = plistObj
      except Exception, err:
        raise RuntimeError("loadFromFile() Error Reading File: '%s' error: %s" % (filePath,err))
      
    else:
      self.logger("Could not find file at path:'%s'" % filePath)
      return False
          
       
    if len(plist) > 0:
      self.plist = plist
      self.isLoaded = True

    return True

  def valueForKeyPath(self,keyPath):
    """Returns value for key"""
    
    try:
      aliasValue = valueForKeyPath(keyPath)
      return aliasValue
    except:
      self.logger("No alias registered for keyPath:%s" % keyPath,"debug")
      pass
    
    keyArray = keyPath.split(".")
    myPlist = self.plist
    
    if len(keyArray) == 0:
      return myPlist
    
    self.logger("valueForKeyPath() hit for keyPath: %s" % keyPath,"debug")
    
    dataTypeName = keyArray.pop(0)
    try:
      dataTypeIndex = int(self.systemProfilerDataTypes.index(dataTypeName))
    except:
      self.logger("Datatype: %s does not exist!" % dataTypeName,"error")
      return False
        
    dataTypeDict = myPlist[dataTypeIndex]["_items"]
    currentItem = dataTypeDict
    
    if len(keyArray) == 0:
      return currentItem
    
    for key in keyArray:
      ## If the current item is an array and our key is not an integer
      ## then grab the first value
      self.logger("valueForKeyPath: processing key element: '%s'" % key,"debug")
      if type(currentItem) == type([]):
        try:
          intKey = int(key)
          currentItem = currentItem[intKey]
          continue
        except:
          currentItem = currentItem[0]
        
      try:
        currentItem = currentItem[key]
      except Exception, err:
        self.logger("Keypath: %s does not exist!" % keyPath,"error")
        self.logger("Exception: %s" % err,"debug")
        return False
    return currentItem

  def backupSettings(self):
    '''Function which performs our backup'''

    backupPath = self.backupPath
    name = self.name
    if not self.baseName:
      self.baseName = name
    baseName = self.baseName
    displayName = self.displayName
    
    if not name or not displayName or not backupPath:
      self.logger("backupSettings() could not perform backup: name,"
      + "displayName, or backupPath not set!","error")    
    if not os.path.isdir(os.path.dirname(backupPath)):
      self.logger("backupSettings() could not perform backup: Directory '%s'"
      " does not exist!" % os.path.dirname(backupPath),"error")
    if not os.path.exists(backupPath):
      try:
        os.mkdir(backupPath)
      except Exception,err:
        self.logger("backupSettings() failed creating directory:'%s': %s" % (backupPath,err),"error")
        return False
        
    ## Set our backup filename. Example: sa_afp_20091228_2243
    if self.useTimeStamps:
      if self.timeStamp:
        backupFileName = "%s_%s.plist" % (baseName,self.timeStamp)
      else:
        backupdt = datetime.datetime.today()
        backupFileName = "%s_%02d%02d%02d_%02d%02d.plist" % (baseName,
                                                        backupdt.year,
                                                        backupdt.month,
                                                        backupdt.day,
                                                        backupdt.hour,
                                                        backupdt.minute)
    else:
      backupFileName = "%s.plist" % baseName
      
    backupTargetPath = os.path.join(backupPath,backupFileName)
    
    ## We have passed sanity checks. 
    self.logger("Backing up %s to '%s'" % (name,backupTargetPath))
    
    profilerPlistObj = self.plist
    ## Perform our ad-hoc backups, get a cvlabel -l output
    systemProfilerPath = self.systemProfilerCMDPath
    
    ## Iterate through all of our backupPaths and copy them over
    for dataType in self.systemProfilerDataTypes:
      self.logger(" - Processing data type: '%s'" % dataType,"detailed")
    
      systemProfilerCMDString = "%s -xml %s" % (systemProfilerPath,dataType)
      
      self.logger("    - Running Command:'%s' " % systemProfilerCMDString,"debug")
      
      systemProfilerCMD = subprocess.Popen(systemProfilerCMDString,shell=True,stdout=subprocess.PIPE,universal_newlines=True)
      systemProfilerCMD_STDOUT, systemProfilerCMD_STDERR = systemProfilerCMD.communicate()
      
      if systemProfilerCMD_STDOUT:
        ## Create a plist object from our output.
        plistObj = plistlib.readPlistFromString(systemProfilerCMD_STDOUT)
        profilerPlistObj.append(plistObj[0])
        
          
    self.plist = profilerPlistObj
    
    self.logger("Saving plist to:'%s'" % backupTargetPath,"detailed")
    try:
      plistlib.writePlist(profilerPlistObj,backupTargetPath)
    except Exception, err:
      self.logger("Cannot save plist to '%s':%s" % (backupTargetPath,err),"error")
    
    ## Check for our 'latest.plist' file
    if self.useTimeStamps:
      latestFileName = "%s_latest.plist" % self.baseName
      self.logger("Updating %s" % latestFileName,"detailed")

      latestFile = os.path.join(backupPath,latestFileName)
      if os.path.lexists(latestFile):
        try:
          os.remove(latestFile)
        except IOError, strerror:
          self.logger("Couldn't remove file %s! Error:'%s'" % (latestFileName,strerror))
          return False
        except Exception,err:
          self.logger("An error occured removing %s: %s" % (latestFileName,err),"error")
          return False
      try:
        self.logger("linking %s to %s" % (backupTargetPath,latestFile),"detailed")
        os.link(backupTargetPath,latestFile)
      except IOError, strerror:
        self.logger("Could not create hard link to %s! Error:'%s'" % (latestFileName,strerror))
        return False
      except Exception, err:
        self.logger("An error occured reading data from plist: %s" % err,"error")
        return False
    
    return True


class backupController(baseService):
  '''Our primary backup controller, responsible for assembling backup modules
  and initiating the backups'''
  
  
  name = "backupController"
  registeredServices = {}
  services = []
  failedServices = []
  backedUpServices = []
  runningServices = []
  
  hostname = ""
  restoreFromBackup = False
  backupPath = ""
  singleFileOutput = False
  useSubDirs = True  
  debug = False
  
  def __init__(self,backupPath=""):
    '''Our contsructor, accepts a path'''
    
    self.backedUpServices = []
    self.runningServices = []
    self.registeredServices = {}
    self.hostname = ""
    self.debug = False
    self.plist = {}
    
    return baseService.__init__(self,backupPath=backupPath)
  
  def registerService(self,serviceList,serviceClass):
    '''Registers an instantiated service object of class serviceClass to
    service name defined in serviceList, for single service classes, serviceList
    can be a string, but will typically be an array of strings'''
    ## If we're passed a string, turn it into a 
    if type(serviceList) == type(""):
      serviceList = [serviceList]

    registrationError = False
    try:
      for service in serviceList:
        if not service in self.registeredServices:
          ## Create an entry for our service containing an instance of our class
          self.logger("Registering service %s to class %s " % (service,serviceClass.__name__),"debug")
          self.registeredServices[service] = serviceClass(name=service)
          if not self.debug:
            self.registeredServices[service].echoLogs = False
        else:
          self.logger("Could not register service: %s, service with same name "
                        "already registered!" % service,"error")
          registrationError = True
    except Exception,err:
      self.logger("Could not process provided services: %s" % err,"error")
      self.logger("  Class: %s " % self.__class__,"error")

      return False
      
    return not registrationError
  
  def setServices(self,serviceList):
    '''Function which is used to establishes which services will be backed
    up. '''
    
    services = []
    if type(serviceList) == type(""):
      serviceList = [serviceList]
    for service in serviceList:
      if service in self.registeredServices.keys() and not service in services:
        services.append(service)
      elif service in services:
        self.logger("Service: %s is already registered, skipping" % service,"detailed")
      elif  service == "running" or service == "all":
        continue
      else:
        self.logger("Service: %s is not registered, skipping" % service,"warning")
        continue
    
    self.services = services
          
    return 
    
  def getRunningServiceList(self):
    '''Returns a list of running services'''
    ## Iterate through our registered services
    testedClasses = []
    runningServiceList = []
    for serviceName,serviceObj in self.registeredServices.iteritems():
      if serviceObj.__class__ in testedClasses:
        continue
      testedClasses.append(serviceObj.__class__)
      myServices = serviceObj.getRunningServiceList()
      if myServices:
        runningServiceList.extend(myServices)
    
    self.runningServices = runningServiceList
    return runningServiceList

  def connectToSQL(self):
    """Open a connection to sqlite db and save the connection at self.sqlConn"""
    sqlConn = ""
    if not self.backupPath:
      self.logger("Backup path not set, cannot create SQL connection!","error")
      return False
      
    dbPath = os.path.join(self.backupPath,".backupHistoryDB")
    if dbPath and not os.path.exists(dbPath):
      if os.path.exists(os.path.dirname(dbPath)):
        try:
          sqlConn = sqlite3.connect(dbPath)
          myCursor = sqlConn.cursor()
          myCursor.execute("CREATE TABLE backupHistory(backupStatus,backupTimeStamp,backedUpServices,runningServices)")
          sqlConn.commit()
          myCursor.close()
        except Exception,err:
          self.logger("An error occured creating sqlite db at path: %s  Error:%s" % (dbPath,err),"error")
          raise
    else:
      try:
        sqlConn = sqlite3.connect(dbPath)
      except Exception, err:
        self.logger("An error occured opening sqlitedb at: %s Error:%s" % (dbPath,err))
        raise
        
    return sqlConn

  def valueForAliasKeyPath(self,keyPath=""):
    """Returns a value for keyPath based upon a specific keyPath alias
    This function primarily serves as an override method for valueForKeyPath
    where manipulation of stored data is replied (concatanation of fields,
    mathematics, etc..."""
      
    if keyPath == "runningServices":
      serviceArray = []
      for service in self.runningServices:
        serviceArray.append(self.registeredServices[service].displayName)
      return serviceArray
        
    elif keyPath == "profile.SPHardwareDataType.processorSummary":
      ## Get CPU data
      try:
        numCPUs = self.valueForKeyPath("profile.SPHardwareDataType.number_processors")
        cpuSpeed = self.valueForKeyPath("profile.SPHardwareDataType.current_processor_speed")
        cpuType = self.valueForKeyPath("profile.SPHardwareDataType.cpu_type")
      except:
        raise RuntimeError("Error reading data from profile.SPHardwareDataType!","error")
      return "%s x %s (%s)" % (numCPUs,cpuSpeed,cpuType)

    return baseService.valueForAliasKeyPath(self,keyPath)
    
    
  def valueForKeyPath(self,keyPath):
    """Returns a value for a dot (.) separated keypath, which denotes a reference
    to a backed up setting value. The first element of the keypath should reference
    a registered service (self.registeredServices). 
    Example: valueForKeyPath("afp.guestAccess")
    queries settings for service "afp" and attribute "guestAccess" 
    returns True or False
    """
    
    try:
      aliasValue = self.valueForAliasKeyPath(keyPath)
      return aliasValue
    except:
      self.logger("No alias registered for keyPath:%s" % keyPath,"debug")
      pass
    
    keyPathArray = keyPath.split(".")
    if len(keyPathArray) == 1:
      key = keyPathArray[0]
      if key in self.info:
        return self.info[key]
      if key == "sabackup":
        return self.info
    
    serviceName = keyPathArray.pop(0)
    
    if serviceName in self.registeredServices:
      serviceObj = self.registeredServices[serviceName]
      return serviceObj.valueForKeyPath(".".join(keyPathArray))
    else:
      raise RuntimeError("Service: %s is not registered!" % serviceName,"error")
      return 

  def loadFromPath(self, backupPath):
    return self.loadFromBackup(backupPath)
  
  def loadFromBackup(self, backupPath):
    """Loads service objects from on-disk backups"""
    
    if backupPath:
      backupBasePath = backupPath
    else:
      backupBasePath = self.backupPath
    
    serverAdminLatestFilePath = os.path.join(backupBasePath,"sa_global.plist")
    
    hostname = ""
    try:
      myPlistObj = plistlib.readPlist(serverAdminLatestFilePath)
      hostname = myPlistObj["sabackup"]["hostname"]
      self.hostname = hostname
      self.logger("Loading backups for hostname:'%s' from path:'%s'" % (hostname,serverAdminLatestFilePath))

    except Exception, err:
      self.logger("Failed loading sa_global.plist file at:'%s' Error:%s" 
        % (serverAdminLatestFilePath,err),"error")  
      raise RunTimeError("test");
    
    ## Iterate through our services and load them from file
    myServices = {} 
    
    for serviceName in self.services:
      theService = self.registeredServices[serviceName]      
      if theService.__class__.__name__ == "saService":
        serviceBackupPath = os.path.join(backupBasePath,"serveradmin",serviceName)
      else:
        serviceBackupPath = os.path.join(backupBasePath,serviceName)
      
      self.logger("Loading Service Name: %s from path: %s" % (serviceName,serviceBackupPath))
      if theService.loadFromPath(serviceBackupPath):
        self.logger(" - Service successfully loaded!")
      else:
        self.logger(" - Service failed to load: %s" % theService.lastError)
    return True

  def backupSettings(self):
    """Our main function to perform a backup"""
    
    singleFileOutput = self.singleFileOutput
    backupBasePath = self.backupPath
    useSubDirs = self.useSubDirs
    useTimeStamps = self.useTimeStamps
    pruneBackups = self.pruneBackups
    pruneOptions = self.pruneOptions
    
    serverAdminPlist = {}  ## Plist for globalling storing all serveradmin backups
    serverAdminLatestFilePath = os.path.join(backupBasePath,"sa_global.plist")
    
    ## write some basic information to our serveradmin plist
    ## Gather basic information
    hostname = platform.uname()[1]
    shortname = hostname.split(".")[0]
    osversion = platform.mac_ver()[0]
    arch = platform.mac_ver()[2]
    isServer = os.path.exists("/System/Library/CoreServices/serverversion.plist")
    isXsan = os.path.exists("/Library/Filesystems/Xsan")
    OSserialNumber = ""
    HWserialNumber = ""
    
    ## Read in serialnumber
    if isServer:
      snPath = "/etc/systemserialnumbers/xsvr"
      if os.path.exists(snPath):
        try:
          fileHandle = open(snPath)
          OSserialNumber = fileHandle.readline()
          fileHandle.close()
        except:
          print "ERROR: Could not read OS X Server serial number data at %s!" % snPath
          
    sabackupDict = {}
    sabackupDict["hostname"] = hostname
    sabackupDict["shortname"] = shortname
    sabackupDict["osversion"] = osversion
    sabackupDict["arch"] = arch
    sabackupDict["isServer"] = isServer
    sabackupDict["osxsserialnumber"] = OSserialNumber
    
    self.info = sabackupDict
    
    serverAdminPlist["sabackup"] = sabackupDict
    
    
    ## iterate through our services and back them up.
    myServices = {}
    failedServices = []
    
    for serviceName in self.services:
      if serviceName == "running" or serviceName == "all" or serviceName == "backup":
        continue
      
      theService = self.registeredServices[serviceName]
      self.logger("Backing up Service Name: %s" % serviceName)
      
      if not singleFileOutput:
        if useSubDirs:
          if theService.__class__.__name__ == "saService":
            serviceBackupPath = os.path.join(backupBasePath,"serveradmin",serviceName)
          else:
            serviceBackupPath = os.path.join(backupBasePath,serviceName)
          ## Create the backup path if it doesn't exist
        else:
          serviceBackupPath = backupBasePath
        
        ## Create our base backup folder if it doesn't exist (and isn't in /Volumes)
        if not os.path.exists(backupBasePath) \
        and os.path.exists(os.path.dirname(backupBasePath)) \
        and not os.path.dirname(backupBasePath) == "/Volumes":
          try:
            os.mkdir(backupBasePath)
          except Exception,err:
            self.logger("Could not create directory:'%s'" % err)
            return 2
        elif not os.path.exists(backupBasePath):
          self.logger("Could not create directory: %s" % backupBasePath,"error")
          return 2

        ## Create our service specific folder, if it doesn't exist
        if not os.path.exists(serviceBackupPath):
          try:
            os.makedirs(serviceBackupPath)
          except Exception,err:
            print "Could not create directory:'%s'" % err
            return 2
        
      
        self.logger("   - Backing up service: '%s' to '%s'" % (serviceName,serviceBackupPath),"detailed")   
        theService.setBackupPath(serviceBackupPath)
        myServices[serviceName] = theService
        syslog.syslog(syslog.LOG_NOTICE,"sabackup: Backing up configuration for service: '%s' to '%s'" % (serviceName,serviceBackupPath))
        theService.useTimeStamps = useTimeStamps
        theService.overWriteExistingFiles = self.overWriteExistingFiles
        theService.timeStamp = self.timeStamp
        if theService.backupSettings():
          syslog.syslog(syslog.LOG_NOTICE,"sabackup: - %s configuration successfully backed up!" % serviceName)
          self.logger("     Successfully backed up!")
          if pruneBackups:
            if theService.canPrune:
              self.logger("   - Pruning Backups!","detailed")
              theService.setPruneOptions(pruneOptions)
              ## Temporarily enable logging on the service
              echoLogs = theService.echoLogs
              theService.echoLogs = True
              theService.prune()
              theService.echoLogs = echoLogs
            else:
              self.logger("     Service doesn't support pruning!","detailed")
        else:
          syslog.syslog(syslog.LOG_ERR,"sabackup: - %s configuration backup failed!" % serviceName)
          failedServices.append(theService)      
          self.logger("     Backup failed! Error:'%s'" % theService.lastError,"error")
      
        ## Aggregate our saServices into one plist
        if theService.__class__.__name__ == "saService":
          key = "%s Config" % theService.displayName
          if not len(theService.plist) > 0:
            self.logger("Plist for service:%s is empty!" % theService.displayName,"detailed")
            continue
          else:
            if key in theService.plist:
              serverAdminPlist[key] = theService.plist[key]
            else:
              self.logger("Key: %s does not exist in plist for service: %s" % (key,theService.displayName),"detailed")
      else:
        ## Todo: fix it so that single-file backups operate more cleanly
        ## This may need a member var supportsSingleFileOutput = True|False
        self.logger("SINGLE FILE BACKUP CURRENTLY BROKEN!!","error")
        return False
        print "   - Gathering data for service: '%s'" % (serviceName)   
        theService = saService(serviceName)
        theService.load()
        myServices[serviceName] = theService 
      ## unset our object
      del theService

    ## Write out our global dicts
    self.logger("   - Updating latest serveradmin file at path %s" % serverAdminLatestFilePath,"detailed")
    try:
      plistlib.writePlist(serverAdminPlist,serverAdminLatestFilePath)
    except IOError, strerror:
      self.logger("Could not write plist file to '%s'! Error:'%s'" % (serverAdminLatestFilePath,strerror),"error")
    except:
      self.logger("An unknown error occured writing plist to '%s'" % serverAdminLatestFilePath,"error")

    self.failedServices = failedServices
      
    if len(failedServices) > 0:
      backupSuccess = False
    else: 
      backupSuccess = True
    
    backupTimeStamp = self.timeStamp
    backedUpServices = ",".join(self.services)
    runningServices = ",".join(self.getRunningServiceList())
    sqlTuple = (backupSuccess,backupTimeStamp,backedUpServices,runningServices)
    try:
      self.logger("   - Updating SQL database.")
      sqlConn = self.connectToSQL()
      myCursor = sqlConn.cursor()
      myCursor.execute("INSERT INTO backupHistory values (?,?,?,?)",sqlTuple)
      sqlConn.commit()
      myCursor.close()
    except Exception, err:
      self.logger("Error writing SQL: %s" % err,"error")
      
    return backupSuccess
    
  def restoreSetting(self):
    """Our main function to restore settings from a backup"""
    
    backupBasePath = self.backupPath
    serverAdminPlist = {}  ## Plist for globalling storing all serveradmin backups
    serverAdminLatestFilePath = os.path.join(backupBasePath,"sa_global.plist")
    
    
class backupSummary(backupController):
  '''Class which is responsible for reading in a number of sabackup outputs
  and providing an aggregate summary of these servers'''
    
  clientData = {}   ## dict keyed by truncated hostname
  serviceData = {}  ## dict keyed by service name
  servers = []      ## array of server hostnames
  backupPath = ""   ## Path to our backup directory to scan
  
  def __init__(self,backupPath=""):
    self.clientData = {}
    self.serviceData = {}
    self.echoLogs = True
    self.debug = False
    self.backupController = ""
    self.name="Backup Summary"
    
    baseService.__init__(self,backupPath=backupPath)

    
  
  def load(self,backupPath=""):
    '''Method which loads all backups found in the specified backup
    directory designated by backupPath'''
  
    ## Make sure we have a good backup directory
    if backupPath and not self.setBackupPath(backupPath):
      self.logger("Could not load, failed to set backup directory:"
        + "'%s'" % backupPath,"error")
      return False
    elif not backupPath and self.backupPath:
      backupPath = self.backupPath
    else:
      self.logger("Could not load, no backup directory specified!","error")
      return False
    
    ## Scan the directory, get a list of .sparseimage files
    ## todo: need to flush this out to support .dmg files
    ## todo: need to flush this out to support directory-based backups as well
    
    dmgList = glob.glob(os.path.join(backupPath, "*.sparseimage"))
    
    ## Iterate through each diskImage and analyze
    loadCount = 0
    for dmgFile in dmgList:
    
      self.logger("Processing backups on image:%s" % dmgFile)
      ## Mount the disk image

      theDiskImage = diskImage(path=os.path.join(backupPath,dmgFile))
      
      self.logger(" - mounting disk image","detailed")
      theDiskImage.mount()
      
      ## load the backup set
      self.logger(" - loading backup set","detailed")
      try:
        if self.loadBackupSet(backupPath=theDiskImage.mountpoint):
          loadCount += 1
      except Exception,err:
        self.logger("Failed loading backups from image: %s Error: %s" % (dmgFile,err),"error")
        raise
      
      ## unmount the image
      self.logger(" - unmounting disk image","detailed")
      theDiskImage.unmount()
    
    self.logger("Successfully loaded %s backup(s)" % loadCount)
    
    return loadCount > 0
          
  def loadBackupSet(self,backupPath):
    '''Reads in a single backup instance and loads appropriate member vars'''
    
    ## Normalize the path
    backupPath = os.path.abspath(os.path.abspath(os.path.expanduser(backupPath)))
    
    ## Client Dictionary
    clientDict = {}
    
    ## check for a good directory
    if not os.path.exists(backupPath):
      self.logger("Could not load, directory: '%s' does not exist!","error")
      return False
    
    ## Read in the backupHistoryDB
    try:
      ## Get running services list
      clientController = backupController(backupPath=backupPath)
      try:
        for key,value in self.registeredServices.iteritems():
          ##self.logger("Registering clientController with service: %s with class: %s" % (key,value.__class__.__name__),"debug")
          clientController.registerService(key,value.__class__)
      except Exception,err:
        self.logger("Fatal error registering services with clientController! Error:%s" % (err),"error")

      sqlConn = clientController.connectToSQL()
      myCursor = sqlConn.cursor()
      
      ## Search for an existing record with the exact filename, if we fail, search for a subset
      myCursor.execute("SELECT * FROM backupHistory WHERE backupStatus = 1 ORDER BY backupTimeStamp DESC LIMIT 1")
      myRow = myCursor.fetchone()
      myCursor.close()
      
      self.logger("SQL Result Running Services: %s" % myRow[3],"debug")
      self.logger("SQL Result Backed up services: %s" % myRow[2],"debug")

      backedUpServices = myRow[2].split(",")    
      runningServices = myRow[3].split(",")
      
      clientController.backedUpServices = backedUpServices
      clientController.runningServices = runningServices

    except Exception,err:
      raise RuntimeError("Could not load data from backupHistoryDB: %s" % err,"error")

    ## read in generic information from sa_global.plist
    ## todo: pull this data from profile data instead
    saGlobalPath = os.path.join(backupPath,"sa_global.plist")
    try: 
      saGlobalPlist = plistlib.readPlist(saGlobalPath)
      saBackupPlist = saGlobalPlist["sabackup"]
      hostname = saBackupPlist["hostname"]  
      clientController.info = saBackupPlist
      clientDict["serveradmin"] = saGlobalPlist   
    except Exception,err:
      raise RuntimeError("Error reading basic sabackup info from sa_global.plist: %s" % err)
  
    clientController.setServices(runningServices)
    clientController.loadFromBackup(backupPath)
    
    clientDict["backedUpServices"] = backedUpServices
    clientDict["runningServices"] = runningServices
    clientDict["controller"] = clientController
  
    for serviceName in runningServices:
      if not serviceName in self.serviceData:
        self.serviceData[serviceName] = {}
      self.logger("backupSummary() Updating serviceData service: %s for client:%s"
                  %(serviceName,hostname),"debug")
      self.serviceData[serviceName][hostname] = clientController

    self.logger("backupSummary() Registering clientData for client:%s" % hostname,"debug")
    self.clientData[hostname] = clientDict
    
    return True
    
  def valuesForKeysForIdentifier(self,keys,identifier):
    """Returns a dictionary of requested keys, wrapped in an array"""
    
    ## Determine our identifier. First check to see if it matches a registered
    data = []
    
    if type(keys) == type(""):
      keys = [keys]
    
    if identifier == "servers":
      target = "servers"
      for clientName,clientDict in self.clientData.iteritems():
        controller = clientDict["controller"]
        if controller.valueForKeyPath("isServer"):
          clientData = {}
          for key in keys:
            clientData[key] = controller.valueForKeyPath(key)
          data.append(clientData)
      return data
  
    if identifier == "xsanVolumes":
      xsanService = self.registeredServices['xsan']
      if not "Volumes" in xsanService.plist:
        xsanService.plist["Volumes"] = {}
      xsanVolumes = xsanService.plist["Volumes"]
      
      ## Build our Xsan volume data
      for clientName,clientController in self.serviceData['xsan'].iteritems():
        for volumeName,volumeDict in clientController.valueForKeyPath("xsan.Volumes").iteritems():
          
          if volumeName in xsanVolumes:
            xsanVolumes[volumeName] = xsanService.mergeTrees(xsanVolumes[volumeName],volumeDict)
          else:
            xsanVolumes[volumeName] = volumeDict;
          
      ## Iterate through our volumes and output the appropriate keys
      data = []
      for volumeName,volumeDict in xsanVolumes.iteritems():
        clientData = {}
        for key in keys:
          keyPath = "Volumes.%s.%s" %(volumeName,key)
          self.logger("valuesForKeysForIdentifier() querying "
                 "key:'%s'" % (keyPath))
          clientData[key] = xsanService.valueForKeyPath(keyPath)
        data.append(clientData)
      return data

    ## Check for a client specific identifier
    for registeredHostname in self.clientData.keys():
      if identifier == registeredHostname:
        controller = self.clientData[registeredHostname]["controller"]
        clientData = {}
        for key in keys:
          clientData[key] = controller.valueForKeyPath(key)
        data.append(clientData)
      return data


  def buildDictFromPagesTableHeader(self,tableHeaders):
    """Returns a dictionary keyed off of values in tableHeaders, iterated
    accross loaded client data"""
    return
    
  def buildDictFromPagesTableHeaderForHostame(self,tableHeaders,hostname):
    """Returns a dictionary keyed off of values in tableHeaders, solely for
    the client defined by hostname"""
    return

  def buildDictFromPagesTableHeaderForServiceName(self,tableHeaders,serviceName):
    """Returns a dictionary keyed off of values in tableHeaders, iterated accross
    all clients registered for serviceName"""
    return
    
  
  def outputPagesFile(self,filePath,templateFilePath=""):
    """Loader method which outputs a pages file based upon the defined 
    template"""
    
    return self.outputPagesFile_APS(filePath=filePath,templateFilePath=templateFilePath)
    
      
  def outputPagesFile_APS(self,filePath,templateFilePath=""):
    """Generates a pages file based upon the APS template file"""
    
    ## Define our support vars
    templateFilePath = "/usr/local/share/pypages/templates/pagesTemplate.pages"
    myDoc = pages.PagesDoc(filePath=filePath,templateFile=templateFilePath)
    
    ########
    ##  Begin Document Creation ######
    ##########
    
    ####
    ## System Configuration ####
    ######
    
    myDoc.addElementToDOM(myDoc.newParagraphNode(text="System Configuration"))
    myDoc.addElementToDOM(myDoc.newParagraphNode(text=""))
    myDoc.addElementToDOM(myDoc.newParagraphNode(text=""))
    
    ####
    ## Basic Server Information ##
    ######
    
    myDoc.addElementToDOM(myDoc.newParagraphNode(text="Basic Server Information\n"))
    myDoc.addElementToDOM(myDoc.newParagraphNode(text=""))

    tableHeaders = []
    tableHeaders.append({"displayName":"Server",
                          "dataKey":"hostname",
                          "width" : 100 })
    tableHeaders.append({"displayName":"OS Version",
                          "dataKey":"osversion",
                          "width" : 50})
    tableHeaders.append({"displayName":"IP",
                          "dataKey":"profile.SPNetworkDataType.IPv4.Addresses.0",
                          "width" : 75 })
                          
    ## Generate our dictionary of values based on tableHeaders
    dataKeys = []
    for tableHeader in tableHeaders:
      if not tableHeader["dataKey"] in dataKeys:
        dataKeys.append(tableHeader["dataKey"])
    
    tableData = self.valuesForKeysForIdentifier(dataKeys,"servers")
    
    myDoc.addNewTableToDOM(tableData=tableData,tableHeaders=tableHeaders)
    
    ####
    ## Server & OS Serial Numbers ##
    ######
    
    myDoc.addElementToDOM(myDoc.newParagraphNode())
    myDoc.addElementToDOM(myDoc.newParagraphNode())
    myDoc.addElementToDOM(myDoc.newParagraphNode(text="Server & OS Serial Numbers"))
    myDoc.addElementToDOM(myDoc.newParagraphNode(text=""))

    tableHeaders = []
    tableHeaders.append({"displayName":"Server",
                          "dataKey":"hostname",
                          "width" : 100 })
    tableHeaders.append({"displayName":"Serial Number",
                          "dataKey":"profile.SPHardwareDataType.serial_number",
                          "width" : 100 })
    tableHeaders.append({"displayName":"OS X Serial Number","dataKey":"osxsserialnumber","width" : 150})


    ## Generate our dictionary of values based on tableHeaders
    dataKeys = []
    for tableHeader in tableHeaders:
      if not tableHeader["dataKey"] in dataKeys:
        dataKeys.append(tableHeader["dataKey"])
    
    tableData = self.valuesForKeysForIdentifier(dataKeys,"servers")
    
    myDoc.addNewTableToDOM(tableData=tableData,tableHeaders=tableHeaders)
    
    
    ####
    ## Server Hardware and Services Overview ##
    ######
    
    myDoc.addElementToDOM(myDoc.newParagraphNode())
    myDoc.addElementToDOM(myDoc.newParagraphNode())
    myDoc.addElementToDOM(myDoc.newParagraphNode(text="Server Hardware and Services Overview"))
    myDoc.addElementToDOM(myDoc.newParagraphNode(text=""))

    tableHeaders = []
    tableHeaders.append({"displayName":"Server",
                          "dataKey":"hostname",
                          "width" : 100 })
    tableHeaders.append({"displayName":"Processor Info",
                          "dataKey":"profile.SPHardwareDataType.processorSummary",
                          "width" : 100 })
    tableHeaders.append({"displayName":"Memory",
                          "dataKey":"profile.SPHardwareDataType.physical_memory",
                          "width" : 100})
    tableHeaders.append({"displayName":"Running Services",
                          "dataKey":"runningServices",
                          "width" : 150})

    ## Generate our dictionary of values based on tableHeaders
    dataKeys = []
    for tableHeader in tableHeaders:
      if not tableHeader["dataKey"] in dataKeys:
        dataKeys.append(tableHeader["dataKey"])
    
    tableData = self.valuesForKeysForIdentifier(dataKeys,"servers")
    
    myDoc.addNewTableToDOM(tableData=tableData,tableHeaders=tableHeaders)
    

    myDoc.addElementToDOM(myDoc.newParagraphNode())
    myDoc.addElementToDOM(myDoc.newParagraphNode())
    
    myDoc.writeXML()
    return myDoc.packFile()

    

  def outputSummary(self,name=""):
    """ Outputs a text summary for the service, accepts a service serviceName as a parameter """
    
    outputText = ""
    serviceList = []
    if not self.isLoaded:
      if not self.load():
        self.logger("outputSummary() Could not load object! Cannot"
        + " continue!","error")
        return False
     
    ## Build our serviceList, which determines which summaries are output
    ## If we're passed an argument, use that as 
    if name and name != "all":
      serviceList.append(name)
    elif not name and self.name:
      serviceList.append(self.name)
    else:
      serviceList = self.loadedServices
            
    outputText = ""
    ## iterate through our services and output summary.
    for serviceName in serviceList:    
      displayName = self.servicesMap[serviceName]
      if not displayName:
        self.logger("outputSummary() could not continue, serviceName or displayName"
          + " not specified, cannot continue!","error")
      
      configName = "%s Config" % displayName
      
      if configName in self.plist:
        plistDict = self.plist[configName]
      else:
        self.logger("outputSummary() '%s' is not present in loaded XML"
          + ", cannot continue!","error") 
        return False
      
      outputText += "%s Configuration:\n\n" % displayName
      ##
      if serviceName is "info":
        pass
      elif serviceName is "afp":
        try: 
          if "guestAccess" in plistDict:
            outputText += "  Guest Access:    %s\n" % plistDict["guestAccess"]
          if "authenticationMode" in plistDict:
            outputText += "  Authentication Mode:  "
            authMode = plistDict["authenticationMode"]
            if authMode == "standard_and_kerberos":
              outputText += "Any"
            if authMode == "standard":
              outputText += "Standard"
            if authMode == "kerberos":
              outputText += "Kerberos"
            outputText += "\n"
          if "maxConnections" in plistDict:
            if plistDict["maxConnections"] == -1:
              outputText += "  Max Connections:  Unlimited\n"
            else:
              outputText += "  Max Connections:  %s\n" % plistDict["maxConnections"]
          
          if "guestAccess" in plistDict and plistDict["guestAccess"]:
            if plistDict["maxGuests"] == -1:
              outputText += "  Max Guest Connections:  Unlimited\n"
            else:
              outputText += "  Max Guest Connections:  %s\n" % plistDict["maxGuests"]

          if "idleDisconnectOnOff" in plistDict and plistDict["idleDisconnectOnOff"]:
            outputText += "  Idle Disconnect:  %s\n" % plistDict["idleDisconnectOnOff"]
            outputText += "    Disconnect Time:  %s hrs\n" % plistDict["idleDisconnectTime"]
            outputText += "    Disconnect:\n"
            if "idleDisconnectFlag" in plistDict:
              for key,value in plistDict["idleDisconnectFlag"].iteritems():
                outputText += "     %s:  %s\n" % (key,value)
            if "idleDisconnectMsg" in plistDict and plistDict["idleDisconnectMsg"]:
              outputText += "    Disconnect Message:\n####\n%s\n####\n" % plistDict["idleDisconnectMsg"]
          
        except:
          self.logger("Error outputing summary for %s" % displayName,"error")
              
      elif serviceName is "backup":
        pass
      elif serviceName is "dhcp":
        pass
      elif serviceName is "dns":
        try: 
          for view in plistDict["views"]:
            if view["name"] is "com.apple.ServerAdmin.DNS.public":
              applePublicView = view
          
          primaryZones = view["primaryZones"]
          reverseZones = view["reverseZones"]
          secondaryZones = view["secondaryZones"]
          
          if "primaryZones" in view and len(view["primaryZones"]) > 0:
            outputText += "  Primary Zones:\n"
            for zone in primaryZones:
              outputText += "    %s\n" % zone["name"]
            
          if "reverseZones" in view and len(view["reverseZones"]) > 0:
            outputText += "\n  Reverse Zones:\n"
            for zone in reverseZones:
              outputText += "    %s\n" % zone["name"]

          if "secondaryZones" in view and len(view["secondaryZones"]) > 0:
            outputText += "\n  Secondary Zones:\n"
            for zone in secondaryZones:
              outputText += "    %s\n" % zone["name"]
          
          if "forwarders" in plistDict and len(plistDict["forwarders"]) > 0:
            outputText += "\n  DNS Forwarders: "
            i=0
            for forwarder in plistDict["forwarders"]:
              if i > 0:
                outputText += ", "
              outputText += forwarder
              i+=1
            outputText += "\n"
        except:
          self.logger("Error outputing summary for %s" % displayName,"error")
          return False
      elif serviceName is "ipfilter":
        pass
      elif serviceName is "ftp":
        pass
      elif serviceName is "calendar":
        pass
      elif serviceName is "jabber":
        pass
      elif serviceName is "mail":
        pass
      elif serviceName is "mysql":
        if "databaseLocation" in plistDict:
          outputText += "  Database Location:  %s\n" % plistDict["databaseLocation"]
        if "allowNetwork" in plistDict:
          outputText += "  Allow Network:  %s\n" % plistDict["allowNetwork"]
      elif serviceName is "nat":
        pass
      elif serviceName is "dirserv":
        try: 
          odconfig = plistDict["LDAPServerType"]
          ##outputText += "  Server Type:   %s%s\n" % (odconfig[0:1].capitalize(),odconfig[1:])
          outputText += "  Server Type:   %s\n" % odconfig.title()
          if "LDAPSettings" in plistDict and "LDAPSearchBase" in plistDict["LDAPSettings"]:
            searchBase = plistDict["LDAPSettings"]["LDAPSearchBase"]
            outputText += "    LDAP Search Base:   %s\n" % searchBase
          if "kerberizedRealmList" in plistDict and "defaultRealm" in plistDict["kerberizedRealmList"]:
            defaultRealm = plistDict["kerberizedRealmList"]["defaultRealm"]
            outputText += "    Kerberos Realm:   %s\n" % defaultRealm
          
          if "hasMissingKerberosServices" in plistDict and plistDict["hasMissingKerberosServices"]:
            outputText += "    Services Kerberized:   False\n"       
          elif "hasMissingKerberosServices" in plistDict:
            outputText += "    Services Kerberized:   True\n"       
          
          if "LDAPSettings" in plistDict and "useSSL" in plistDict["LDAPSettings"]:
            usesSSL = plistDict["LDAPSettings"]["useSSL"]
            outputText += "    Uses SSL:     %s\n" % usesSSL
        except:
          self.logger("Error outputing summary for %s" % displayName,"error")
          return False
        
      elif serviceName is "netboot":
        pass
      elif serviceName is "nfs":
        if "nbDaemons" in plistDict:
          outputText += "  NFS Daemons:  %s\n" % plistDict["nbDaemons"]
        if "useTCP" in plistDict:
          outputText += "  Use TCP:  %s\n" % plistDict["useTCP"]
        if "useUDP" in plistDict:
          outputText += "  Use UDP:  %s\n" % plistDict["useUDP"]
      elif serviceName is "pcast":
        pass
      elif serviceName is "print":
        pass
      elif serviceName is "qtss":
        pass
      elif serviceName is "radius":
        pass
      elif serviceName is "smb":
        ##try: 
        if "adminCommands" in plistDict and "serverRole" in plistDict["adminCommands"]:
          outputText += "  Server Role:  %s\n" % plistDict["adminCommands"]["serverRole"].title()
        if "adminCommands" in plistDict and "homes" in plistDict["adminCommands"]:
          outputText += "  Map User Home Directories: %s\n" % plistDict["adminCommands"]["homes"]          
        if "workgroup" in plistDict:
          outputText += "  Workgroup:  %s\n" % plistDict["workgroup"]
        if "server string" in plistDict:
          outputText += "  ServerString:  %s\n" % plistDict["server string"]
        if "domain master" in plistDict:
          outputText += "  Domain Master Browser: %s\n" % plistDict["domain master"]
        if "map to guest" in plistDict:
          if plistDict["map to guest"] == "Never":
            outputText += "  Guest Access:  False\n"
          else:
            outputText += "  Guest Access:  True\n"
        if "ntlm auth" in plistDict:
          if plistDict["ntlm auth"] == "YES":
            outputText += "  NTLM Auth:  True\n"
          else:
            outputText += "  NTLM Auth:  False\n"
        if "lanman auth" in plistDict:
          if plistDict["lanman auth"] == "YES":
            outputText += "  LANMAN Auth:  True\n"
          else:
            outputText += "  LANMAN Auth:  False\n"
        if "use spnego" in plistDict:
          outputText += "  Use SPNEGO:  %s\n" % plistDict["use spnego"]
        if "maxConnections" in plistDict:
          if plistDict["maxConnections"] == -1:
            outputText += "  Max Connections:  Unlimited\n"
          else:
            outputText += "  Max Connections:  %s\n" % plistDict["maxConnections"]
        
        if "guestAccess" in plistDict and plistDict["guestAccess"]:
          if plistDict["maxGuests"] == -1:
            outputText += "  Max Guest Connections:  Unlimited\n"
          else:
            outputText += "  Max Guest Connections:  %s\n" % plistDict["maxGuests"]

        if "idleDisconnectOnOff" in plistDict and plistDict["idleDisconnectOnOff"]:
          outputText += "  Idle Disconnect:  %s\n" % plistDict["idleDisconnectOnOff"]
          outputText += "    Disconnect Time:  %s hrs\n" % plistDict["idleDisconnectTime"]
          outputText += "    Disconnect:\n"
          if "idleDisconnectFlag" in plistDict:
            for key,value in plistDict["idleDisconnectFlag"].iteritems():
              outputText += "     %s:  %s\n" % (key,value)
          if "idleDisconnectMsg" in plistDict and plistDict["idleDisconnectMsg"]:
            outputText += "    Disconnect Message:\n####\n%s\n####\n" % plistDict["idleDisconnectMsg"]
          
        ##except:
        ##  self.logger("Error outputing summary for %s" % displayName,"error")
        ##   return False
              
      elif serviceName is "swupdate":
        try:
          outputText += "  Automatically download Updates From Apple: %s\n" % plistDict["autoMirror"]
          outputText += "  Auto Enable Updates From Apple: %s\n" % plistDict["autoEnable"]
          outputText += "  Automatically Purge Old Updates: %s\n" % plistDict["PurgeUnused"]
          outputText += "  Network Port: %s\n" % plistDict["portToUse"]
          if plistDict["limitBandWidth"]:
            outputText += "  Bandwidth Limit: %s kbps\n" % plistDict["valueBandwidth"]
        except:
          self.logger("Error outputing summary for %s" % displayName,"error")
        
      elif serviceName is "vpn":
        pass

      elif serviceName is "web":
        try:
          outputText += "  Apache Base Version:  %s\n" % plistDict["ApacheMode"]
          if "Sites" in plistDict and len(plistDict) > 0:
            outputText += "  Configured Sites:\n"
            for site in plistDict["Sites"]:
              if site["ServerName"]:
                siteDescription = "    Site Name: %s\n" % site["ServerName"]
              else:
                siteDescription = "    Default Site:\n"              
              if "HostDescription" in site:
                siteDescription += "    Description:  %s\n" % site["HostDescription"]
              if "enabled" in site:
                siteDescription += "    Enabled:  %s\n" % site["enabled"]  
              if "VirtualHostRealID" in site:
                virtualHostRealID = site["VirtualHostRealID"]
                siteDescription += "    IP/Port:  %s\n" % virtualHostRealID[0:virtualHostRealID.rfind("_")]
              
              if "ServerAlias" in site and len(site["ServerAlias"]) > 0:
                siteDescription += "    Server Aliases: "
                count = 0
                for alias in site["ServerAlias"]:
                  if count > 0:
                    siteDescription += ","
                  siteDescription += alias
                  count+=1
                siteDescription += "\n"
              
              if "DocumentRoot" in site:
                siteDescription += "    Directory:  %s\n" % site["DocumentRoot"]
              
              siteDescription += "\n    Services:\n"
              if "calendar" in site:
                siteDescription += "      Calendar:  %s\n" % site["calendar"]
              if "mailingListArchive" in site:
                siteDescription += "      Mail Archive:  %s\n" % site["mailingListArchive"]
              if "WebMail" in site:
                siteDescription += "      WebMail:  %s\n" % site["WebMail"]
              if "weblog" in site:
                siteDescription += "      Weblog:  %s\n" % site["weblog"]
              if "wikiAndWeblog" in site:
                 siteDescription += "      Wiki:    %s\n" % site["wikiAndWeblog"]
              if "wikiAndWeblog" in site and site["wikiAndWeblog"] and "repositoryPath" in plistDict:
                siteDescription += "    Wiki Datastore: %s\n" % plistDict["repositoryPath"]

              outputText += "%s\n" % siteDescription
              
          else:
            outputText += "   No Sites Conifgured!\n"
        except:
          self.logger("Error outputing summary for %s" % displayName,"error")
          return False

      elif serviceName is "webobjects":
        pass
      elif serviceName is "xgrid":
        pass
      elif serviceName is "sharing":
        pass
      outputText += "\n"
      
    return outputText




class osxsharepoint:
  """Our sharepoint class, used for interpretting configured sharepoints"""
  pathToPlist = ""
  plistObj = ""
  outputdir = ""
  
  serviceName = ""
  directory_path = ""
  scope = "master"
  
  sharepoints = {}
  
  lastMSG = ""
  lastError = ""
  log = []
  
  def __init__(self, plist=""):
    """ Our constructor. If passed a path to a valid plist, read it in. """
    if plist:
      self.loadFromPlist(plist)

  def logger(self, logMSG, logLevel="normal"):
    """(very) Basic Logging Function, we'll probably migrate to msg module"""
    if logLevel == "error" or logLevel == "normal" or self.debug:
      print "%s: %s" % (self.name, logMSG)
      self.lastMSG = logMSG
    if logLevel == "error":
      self.lastError = logMSG
    self.log.append({"logLevel" : logLevel, "logMSG" : logMSG})
    
  def printLogs(self, logLevel="all"):
    """output our logs"""
    for log in self.log:
      if logLevel == "all" or logLevel == log["logLevel"]:
        print "%s:%s:%s" % (self.name,log["logLevel"], log["logMSG"])

  def loadFromPlist(self,plist):
    """ Loads data from plist at pathtoplist. Returns plistlib object """
    if not plist:
      self.logger("No plist data provided, cannot continue!","error")
      return False
    
    plistObj = ""
    
    if not os.path.isfile(plist):
      self.logger("Specified plist is not a path, interpreting as string","error")
      try:
        plistObj = plistlib.readPlistFromString(plist)
      except IOError, strerror:
        self.logger("Could not access plist:'%s' Error:'%s'" % (plist,strerror))
        return False
      except:
        self.logger("An unknown error occured reading data from plist","error")
        return False
    else: 
      self.logger("Loading plist file at path: '%s'" % plist,"error")
      try:
        plistObj = plistlib.readPlist(plist)
        self.pathToPlist = plist
      except IOError, strerror:
        self.logger("Could not access plist:'%s' Error:'%s'" % (plist,strerror))
        return False
      except:
        self.logger("Could not read plist from file, cannot continue!","error")
        return False
    
    if not plistObj:
      self.logger("Could not generate plist, cannot continue!","error")
      return False
    else:
      self.plistObj = plistObj

    ## Passed sanity checks, plist should be loaded at this point

    ## determine if this is a master list,indicated by the scope attribute
    if "scope" in plistObj:
      if plistObj["scope"] == "master":
        self.scope = "master"
        self.name = "global"
        
        self.logger("Loading sharepoints from master plist!")
        if "sharepoints" in plistObj:
          for sharepointData in plistObj["sharepoints"]:
            if "name" in sharepointData:
              self.logger("Loading sharepoint: %s" % sharepointData["name"])
              mySharePoint = osxsharepoint(sharepointData)
              if mySharePoint:
                self.sharePoints[sharepointData["name"]] = mySharePoint.plistObj
            else:
              self.logger("Sharepoint does not have 'name' attribute, skipping!","error")
              continue
              
        else:
          self.logger("Master plist contains no sharepoints!","error")
          return False
          
      else:
        self.logger("Malformed plist found, plist defines non-master scope!","error")
        return False
    else:
      ## Here if we are not a master sharepoint.
      if "name" in plistObj and "directory_path":
        self.logger("Loading sharepoint:%s" % plistObj["name"][0])
        self.name = plistObj["name"][0]
        self.directory_path = plistObj["directory_path"][0]
        self.plistObj = plistObj
        self.scope = "sharepoint"
      else:
        self.logger("Sharepoint plist does not have 'name' or 'directory_path' attribute, cannot load!","error")
        return False
    return True
        
  def plistForShareName(self, name):
    """ Attempts to generate plist for share with serviceName from loaded plistObj. Returns plistlib object """
    if serviceName in self.sharepoints:
      theShare = self.sharepoints["name"]
    if theShare.plistObj:
      return theShare.plistObj
    else:
      self.logger("Could not find appropriate plistlib object for share:'%s'" % name,"error")
      return False
    
  def sharesFromPath(self,dirPath):
    """ Returns a dictionary of osxsharepoint objects read in from plist files 
    residing at dirpath, keyed by share name. It collates all share data 
    into a single plistlib object and saves it at self.plistObj """
    
    sharepoints = dict()
    
    plistDict = dict( 
          scope = "master",
          serviceName = "global",
          sharepoints = []
    )

    if not os.path.exists(dirPath):
      self.logger("Could not read shares! folder path:'%s' does not exist!" % dirPath,"error")
    
    importFileList = glob.glob(os.path.join(dirPath, "*.plist"))
    for theFilePath in importFileList:
      theSharePoint = osxsharepoint(theFilePath)
      if theSharePoint.name and theSharePoint.directory_path and theSharePoint.plistObj:
        print "Share name:%s type:%s" % (theSharePoint.name, type(theSharePoint.name))
        sharepoints[theSharePoint.name] = theSharePoint
        plistDict["sharepoints"].append(theSharePoint.plistObj)
      else:
        ##self.logger("Plist '%s' did not load properly, skipping!" % theFilePath,"error")
        continue
      
    self.logger("Successfully loaded %s of %s files from path:'%s'" % (len(sharepoints),len(importFileList),dirPath),"error")
    self.plistObj = plistDict
    self.sharepoints = sharepoints
    
    return sharepoints
    
  def backupSettings(self):
    """Perform our backup"""
    backupPath = self.backupPath
    
    if not backupPath:
      self.logger("Could not perform backup: backupPath not set!","error")    
    
    if not os.path.isdir(os.path.dirname(backupPath)):
      self.logger("backupSettings() could not perform backup: Directory '%s'"
      " does not exist!" % os.path.dirname(backupPath),"error")
    if not os.path.exists(backupPath):
      try:
        os.mkdir(backupPath)
      except:
        self.logger("Failed creating directory:'%s', cannot continue!" % backupPath,"error")
        
    if not os.path.isdir(backupPath):
      self.logger("Non-directory found at backup path:'%s', cannot continue!" % backupPath,"error")
      return False
    
    ## Set our backup filename. Example: sa_afp_20091228_2243
    backupFileName = "sharepoints_%s%s%s_%s%s.xml" % (backupdt.year,backupdt.month,backupdt.day,backupdt.hour,backupdt.minute)
    backupFile = os.path.join(backupPath,backupFileName)
                                                        
    ## We have passed sanity checks. 
    self.logger("Backing up sharepoint settings to '%s'" % backupFile)
    
    if self.plistObj:
      return plistlib.writePlistToPath(self.plistObj,backupFile)
      
  def writePlistToPath(self,filepath,overwrite=False):
    """ Writes data saved in plistObj to dirpath"""
    
    if os.path.exists(filepath):
      self.logger("Cannot save plist! File or directory exists '%s'" % filepath,"error")
      return False
          
    if not os.path.isdir(os.path.dirname(filepath)):
      self.logger("Cannot save plist! Directory path does not exist '%s'" % filepath,"error")
      return False
    
    plistObj = self.plistObj
    
    self.logger("Saving plist to:'%s'" % filepath)
    try:
      plistlib.writePlist(plistObj,filepath)
    except:
      self.logger("Cannot save plist to '%s', an unknown error occured." % filepath,"error")

class odService:
  """OD class, used to perform OD Archives"""
  odPath = ""		## Path to the OD Archive
  odPassword = ""	## Password for OD Archive sparseimage
  serveradmin = "/usr/sbin/serveradmin"    
 
  lastMSG = ""
  lastError = ""
  log = []

  def __init__(self, odPath, odPassword):
    print "Running OD Service init"
    if odPath:
      self.odPath = odPath
    if odPassword:
      self.odPassword = odPassword
 
  def logger(self, logMSG, logLevel="normal"):
    """(very) Basic Logging Function, we'll probably migrate to msg module"""
    if logLevel == "error" or logLevel == "normal" or self.debug:
      ## print "diskImage: %s" % logMSG
      self.lastMSG = logMSG
    if logLevel == "error":
      self.lastError = logMSG
    self.log.append({"logLevel" : logLevel, "logMSG" : logMSG}) 

  def printLogs(self, logLevel="all"):
    """output our logs"""
    for log in self.log:
      if logLevel == "all" or logLevel == log["logLevel"]:
        print "%s:%s:%s" % (self.name,log["logLevel"], log["logMSG"])


  def createArchive(self,odPath,odPassword):
    """
    Here's what needs to get passed to serveradmin
    /usr/sbin/serveradmin command
    dirserv:backupArchiveParams:archivePassword = $archive_password
    dirserv:backupArchiveParams:archivePath = $archive_file
    dirserv:command = backupArchive
    """
    ## Set the file name for the archive
    Timestamp = datetime.datetime.today()
    fileName = "%s/%d%02d%02d" % (odPath,
                  Timestamp.year,
                  Timestamp.month,
                  Timestamp.day)
    
    ## Make sure that OD is a running service
    odStatus = subprocess.Popen('serveradmin -x status dirserv', shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    odStatus_STDOUT, odStatus_STDERR = odStatus.communicate()
    if len(odStatus_STDOUT) == 0:
      self.logger("serveradmin: could not determine status for Open Directory!")
      return 2
    else:
      ## Create a plist object from our output.
      try:
        plistObj = plistlib.readPlistFromString(odStatus_STDOUT)
        if "state" in plistObj:
          if plistObj["state"] == "RUNNING":
      ## If it's running, create the archive
            archiveCommand = subprocess.Popen('serveradmin command', shell=True, stdin=subprocess.PIPE)
            archiveCommand.communicate("dirserv:backupArchiveParams:archivePassword = %s\ndirserv:backupArchiveParams:archivePath = %s\ndirserv:command = backupArchive" % (odPassword,fileName))
            archiveCommand_STDOUT, archiveCommand_STDERR = archiveCommand.communicate()

            if not archiveCommand.returncode == 0:
              self.logger("Failed to create OD Archive: Error:%s" % (archiveCommand_STDERR))
              return False
            else:
              self.logger("Successfully created OD Archive: %s" % (archiveCommand_STDOUT))
              return True
          else:
            print "OD archive was specified, but OD services are not running"
      except:
        self.logger("serveradmin: could not read status XML for Open Directory")
    

class diskImage:
  """Our diskimage class, used to manipulate disk images"""
  path = ""      ## Full path to the disk image file.
  type = ""
  size = ""
  fs = ""
  volname = ""
  mountpoint = ""
  hdiutil = ""
      
  lastMSG = ""
  lastError = ""
  log = []
  
  def __init__(self, path = ""):
    if path:
      self.path = path
    ## make sure we have hdiutil
    hdiutil = "/usr/bin/hdiutil"
    if os.path.isfile(hdiutil):
      self.hdiutil = hdiutil
    else:
      self.logger("Failed to set hdiutil path: '%s' does not exist" % hdiutil,"error")     
    
  
  def logger(self, logMSG, logLevel="normal"):
    """(very) Basic Logging Function, we'll probably migrate to msg module"""
    if logLevel == "error" or logLevel == "normal" or self.debug:
      ## print "diskImage: %s" % logMSG
      self.lastMSG = logMSG
    if logLevel == "error":
      self.lastError = logMSG
    self.log.append({"logLevel" : logLevel, "logMSG" : logMSG}) 
  
  def printLogs(self, logLevel="all"):
    """output our logs"""
    for log in self.log:
      if logLevel == "all" or logLevel == log["logLevel"]:
        print "%s:%s:%s" % (self.name,log["logLevel"], log["logMSG"])
        
  def setPath(path):
    if (os.path.exists(path)):
      self.path = path
    
  def mount(self, path = "", mountpoint = ""):
    """ Mounts specified disk image """
    if not path and self.path:
      path = self.path
    if path and os.path.isfile(path):
      hdiutilCMD = ""
    else:
      self.logger("Could not mount disk image at path:'%s', file not found!","error")
    
    ## make sure we have hdiutil
    hdiutil = self.hdiutil
    if not hdiutil:
      self.logger("Failed to mount disk image, hdiutil could not be found","error")
      return False
    
    ## print "Running Command: '%s' attach '%s' -puppetstrings" % (hdiutil,path)
    hdiutilCMD = subprocess.Popen("'%s' attach '%s' -puppetstrings -plist" % (hdiutil,path),shell=True,stdout=subprocess.PIPE,universal_newlines=True)
    hdiutilCMD_STDOUT, hdiutilCMD_STDERR = hdiutilCMD.communicate()
    
    if hdiutilCMD.returncode == 0:
      ## Here if hdiutil attach succeeded, attempt to read mountpoint from xml
      try: 
        plistObj = plistlib.readPlistFromString(hdiutilCMD_STDOUT)
        sysEntities = plistObj["system-entities"]
        for entity in sysEntities:
          if "mount-point" in entity:
            mountpoint = entity["mount-point"]
            break
      except:
        self.logger("Error reading hdiutil output XML, an unknown error occured!")
        
      
      if not mountpoint:
        self.logger("Mounted Disk Image, but could not determine mountpoint from XML, an unknown error occured!")

      self.mountpoint = mountpoint      
      self.logger("Mounted Disk Image at path:'%s'" % mountpoint)
      
      return True

    else:
      self.logger("Failed to mount disk image:'%s' hdiutil exitcode:%s Error:%s" % (path,hdiutilCMD.returncode,hdiutilCMD_STDERR),"error")
      return False
          
  def unmount(self, mountpoint = ""):
    """ Method which unmounts the disk image as denoted by self.mountpoint """      
    if not mountpoint and self.mountpoint:
      mountpoint = self.mountpoint
    elif not mountpoint and not self.mountpoint:
      self.logger("Cound not unmount volume, no mountpoint specified!","error")
      return False
      
    ## make sure we have hdiutil
    hdiutil = self.hdiutil
    if not hdiutil:
      self.logger("Failed to create disk image: hdiutil could not be found!","error")
      return False
    
    
    ## print "Running Command: '%s' create -type '%s'  -size '%s' -fs '%s' -volname '%s' '%s' -puppetstrings" % (hdiutil,type,size,fs,volname,path)
    hdiutilCMD = subprocess.Popen("'%s' detach '%s'" % (hdiutil,mountpoint),shell=True,stdout=subprocess.PIPE,universal_newlines=True)
    hdiutilCMD_STDOUT, hdiutilCMD_STDERR = hdiutilCMD.communicate()
    
    if not hdiutilCMD.returncode == 0:
      self.logger("Failed to unmount disk image:'%s' hdiutil exitcode:%s Error:%s" % (mountpoint,hdiutilCMD.returncode,hdiutilCMD_STDERR),"error")
      return False
    else:
      self.logger("Unmounted Disk Image at path:'%s'" % mountpoint)
      return True
    
    

  def createDMG(self,type = "",size = "",fs = "",volname = "", path = ""):
    """ Method to create a disk image, models hdiutil's interface """
    
    print "volname:'%s' path:'%s'" % (volname,path)
    
    ## Resolve pertinent variables.
    if not type and self.type:
      type = self.type
    elif not type:
      type = "SPARSE"
    if not size and self.size:
      size = self.size
    elif not size:
      size = "1g"
    if not fs and self.fs:
      fs = self.fs
    elif not fs:
      fs = "HFS+"
    if not volname and self.volname:
      volname = self.volname
    elif not volname:
      volname = "Disk Image HD"
    
    if not path and self.path:
      path = self.path
    elif not path:
      path = os.getcwd()
    
    if not os.path.isdir(os.path.dirname(path)):
      self.logger("Failed to create disk image: '%s' path does not exist","error")
      return False
      
    ## make sure we have hdiutil
    hdiutil = self.hdiutil
    if not hdiutil:
      self.logger("Failed to create disk image: hdiutil could not be found!","error")
      return False
    
    ## print "Running Command: '%s' create -type '%s'  -size '%s' -fs '%s' -volname '%s' '%s' -puppetstrings" % (hdiutil,type,size,fs,volname,path)
    hdiutilCMD = subprocess.Popen("'%s' create -type '%s'  -size '%s' -fs '%s' -volname '%s' '%s' -puppetstrings" % (hdiutil,type,size,fs,volname,path),shell=True,stdout=subprocess.PIPE,universal_newlines=True)
    hdiutilCMD_STDOUT, hdiutilCMD_STDERR = hdiutilCMD.communicate()
    
    
    
    if not hdiutilCMD.returncode == 0:
      self.logger("Failed to create disk image:'%s' hdiutil exitcode:%s Error:%s" % (path,hdiutilCMD.returncode,hdiutilCMD_STDERR),"error")
      return False
    else:
      self.logger("Created Disk Image at path:'%s'" % path)
      return True


######################### END CLASSES ###############################


######################### MAIN SCRIPT START #############################

def main():
  
  ## Register our services
  myController = backupController()
  myController.registerService(saService().servicesMap.keys(),saService)
  myController.registerService("profile",systemProfilerService)
  myController.registerService("xsan",xsanService)
  
  ## Set Static vars
  action = "backup"
  configFilePath = "/Library/Preferences/com.318.sabackup.plist"
  
  outputFile = ""
  outputDir = ""
  singleFileOutput = False
  useDiskImage = False
  doNotUseDiskImage = False
  restoreFromBackup = False
  odArchive = True
  odPassword = ""
  diskImageName = "%s_sabackup.sparseimage" % os.path.splitext(os.uname()[1])[0]
  useSubDirs = True
  myServices = {}
  serviceList = []  
  registeredServices = myController.registeredServices.keys()
  useTimeStamps = True
  overWriteExistingFiles = False
  pruneBackups = False
  pruneOptions = {"maxAge" : 30, "minCopies" : 1, "maxCopies" : 0}

  ## parse our passed parameters
  try:
    optlist, list = getopt.getopt(sys.argv[1:],':hvfp',["outputdir=",
      "outputfile=","service=","services=","target=","appendField=",
      "usedmg","nodmg","nosubdirs","usetimestamps","notimestamps",
      "help","version","force","prune","maxage=","mincopies=","maxcopies=",
      "plist=","odarchive","odpassword="])
  except getopt.GetoptError:
    print "Syntax Error!"
    helpMessage()
    return 1
  
  ## If no parameters are passed, read from preferences
  if len(optlist) < 1:
    helpMessage()
    return 1
  
  ## Read in our options, if there are any
  for opt in optlist:
    if opt[0] == '-h' or opt[0] == "--help":
      helpMessage()
      sys.exit(0)
    elif opt[0] == '-v' or opt[0] == "--version":
      print ("sabackup   Version %s  Build %s " % (version,build)
        + "\n     Written by Beau Hunter, 318 Inc."
        + " \n     Copyright (C) 2011" )
      return 0
    elif opt[0] == "--odarchive":
      odArchive = True
    elif opt[0] == "--odpassword":
      odPassword = opt[1]
    elif opt[0] == '-f' or opt[0] == "--force":
      overWriteExistingFiles = True
    elif opt[0] == "--outputfile":
      outputFile = opt[1]        
    elif opt[0] == "--outputdir":
      outputDir = opt[1]
    elif opt[0] == "--usedmg":
      useDiskImage = True
    elif opt[0] == "--nodmg":
      useDiskImage = False
      doNotUseDiskImage = True
    elif opt[0] == "--nosubdirs":
      useSubDirs = False
    elif opt[0] == "--service":
      serviceList.append(opt[1])
    elif opt[0] == "--services":
      serviceList.extend(opt[1].strip(" ").split(","))
    elif opt[0] == "--usetimestamps":
      useTimeStamps = True
    elif opt[0] == "--notimestamps":
      useTimeStamps = False
    elif opt[0] == "-p" or opt[0] == "--prune":
      pruneBackups = True
    elif opt[0] == "--maxage":
      pruneOptions["maxAge"] = opt[1]
    elif opt[0] == "--mincopies":
      pruneOptions["minCopies"] = opt[1]
    elif opt[0] == "--maxcopies":
      pruneOptions["maxCopies"] = opt[1]
    elif opt[0] == "--plist":
      configFilePath = opt[1]
      if not os.path.isfile(configFilePath):
        print "No config file found at: '%s'!" % configFilePath
        helpMessage()
        return False
  
      ## Convert our plist to xml (in case it's binary)
      subprocess.call("/usr/bin/plutil -convert xml1 '%s'" % configFilePath,shell=True,universal_newlines=True)
  
      ## Create our plist parser
      myPlist = plistlib.readPlist(configFilePath)
      
      if "outputfile" in myPlist:
        outputFile = myPlist["outputfile"]
      if "outputdir" in myPlist:
        outputDir = myPlist["outputdir"]
      if "usedmg" in myPlist:
        useDiskImage = myPlist["usedmg"]
      if "nodmg" in myPlist and myPlist["nodmg"]:
        doNotUseDiskImage = True
      if "nosubdirs" in myPlist:
        if myPlist["nosubdirs"]:
          useSubDirs = False
      if "services" in myPlist:
        serviceList = myPlist["services"]
      if "notimestamps" in myPlist:
        useTimeStamps = myPlist["notimestamps"]
      if "usetimestamps" in myPlist:
        useTimeStamps = myPlist["usetimestamps"]
      if "prunebackups" in myPlist:
        pruneBackups = myPlist["prunebackups"]
      if "maxage" in myPlist:
        pruneOptions["maxAge"] = myPlist["maxage"]
      if "mincopies" in myPlist:
        pruneOptions["minCopies"] = myPlist["mincopies"]
      if "maxcopies" in myPlist:
        pruneOptions["maxCopies"] = myPlist["maxcopies"]
      break
#    elif opt[0] == "--restore":
#      print "--restore is unimplemented!"
#      return 1
#    elif opt[0] == "--restoreFrom":
#      print "--restore is unimplemented!"
#      return 1
    else:  
      print "Unknown Option: %s" % opt[0]
      helpMessage()
      return 1
      
  ## check for root
  if not os.geteuid() == 0:
    print "sabackup: must be run as root!"
    return 1

  print "Backup Routine started."
  print "*  Running Backup Preflight"
    

  ## Validate passed arguments
  if outputFile and outputDir:
    if outputFile[0:1] == "/":
      outputFile = os.path.join(outputDir,outputFile[1:])
    else:
      outputFile = os.path.join(outputDir,outputFile)
  elif not outputFile and not outputDir:
    print "Syntax Error: No destination specified!"
    helpMessage()
    return 2
  
  if pruneBackups:
    if not useSubDirs:
      print "Warning: Backup pruning requires directory based backups, it is" \
      " not supported when outputing to a plist file or when --nosubdirs is specified!"
      pruneBackups = False
    if not useTimeStamps:
      print "Warning: Backup pruning requires directory based backups with " \
      " --usetimestamps set to True!"
      pruneBackups = False
  
  if outputFile:
    if os.path.isdir(outputFile):
      print "Could not use specified outputfilepath! '%s' is a directory!" % outputFile
      return 2
    elif not os.path.exists(os.path.dirname(outputFile)):
      if os.path.exists(os.path.dirname(os.path.dirname(outputFile))) and \
        not os.path.dirname(outputFile) == "/Volumes":
        try:
          os.mkdir(os.path.dirname(outputFile))
        except IOError:
          print "Could not create directory, access denied:'%s'" % outputDir
          return 2
        except:
          print "Could not create directory:'%s'" % outputDir
          return 2
    
    ## check the fileextension to try to determine output type
    if outputFile.endswith(".plist"):
      if useDiskImage:
        print "Specified option usedmg but destination file is a .plist! Cannot continue!"
        return False
      useDiskImage = False
      useSubDirs = False
      singleFileOutput = True
    elif outputFile.endswith(".dmg") or outputFile.endswith(".sparseimage"):
      if doNotUseDiskImage:
        print "Specified a image-based target file but option 'nodmg' was specified! Cannot continue!"
        return False
      elif not doNotUseDiskImage:
        useDiskImage = True
        
    ## if we are set to use timestamps, modify the filename accordingly.
    if useTimeStamps and not useDiskImage:
      backupdt = datetime.datetime.today()
      outputFile = "%s_%d%02d%02d%02d%02d%02d" % (os.path.splitext(outputFile)[0],
                    backupdt.year,
                    backupdt.month,
                    backupdt.day,
                    backupdt.hour,
                    backupdt.minute,
                    os.path.splitext(outputFile[1]))
    ## Set our target file, used from here-on out 
    backupTarget = outputFile
    
  elif outputDir:
    if os.path.exists(outputDir) and os.path.isfile(outputDir):
        print "File exists at specified directory:'%s', cannot continue" % outputDir
        return 2
    elif not os.path.exists(outputDir):
      if (os.path.exists(os.path.dirname(outputDir)) and not
      os.path.dirname(outputDir) == "/Volumes"):
        try:
          os.mkdir(outputDir)
        except Exception, err:
          print "Could not create directory:'%s'" % err
          return 2
      elif not os.path.isdir(os.path.dirname(outputDir)):
        print "ERROR: Backup directory: '%s' does not exist and could not be created, cannot continue!" % outputDir
        return 2
      elif os.path.dirname(outputDir) == "/Volumes":
        print "ERROR: Destination Volume: '%s' is not mounted, cannot continue!" % os.path.dirname(outputDir)
        return 2
      else:
        print "Could not use specified directory:'%s', path does not exist!" % opt[1]
        return 2
      
    ## At this point, we either have a valid destination directory, or we've bailed
    if useDiskImage and not doNotUseDiskImage:
      backupTarget = os.path.join(outputDir,diskImageName)
    else:
      backupTarget = outputDir
  else:
    print "ERROR: Problem resolving destination, cannot continue!"
    return 2

  ## if our disk image doesn't exist, create it.
  if useDiskImage and not doNotUseDiskImage:
    saDMGpath = backupTarget
    type="SPARSE"
    volname="sabackup"
    print "   - Mounting disk image: '%s'" % saDMGpath
    try:
      saDMG = diskImage(saDMGpath)
    except:
      print "ERROR: An unknown error occured mounting image, cannot continue!"
      return 3
    
    if not os.path.exists(saDMGpath):
      print "   - No disk image found at path '%s', creating!" % saDMGpath
      if not saDMG.createDMG(type=type,volname=volname,path=saDMGpath):
        print "ERROR: Disk image creation failed, cannot complete backup!!"
        return 3
      else:
        print "    - Image Created!"

    if not saDMG.mount():
      print "ERROR: Failed to mount disk image, cannot complete backup!!" 
      return 3
    else:
      print "   - Disk Image Mounting Completed!"
    
    ## Update the backup target to the 
    backupTarget = saDMG.mountpoint
    
  ## if we have not specified a backup target yet, bail out
  if not backupTarget:
    print "ERROR: Could not determine backup target, cannot continue!" 
    return 2

  ## Our dictionary that serves as the root for our final sa_global output
  globalDict = {}

## If odArchive is set, make sure we have a password defined
  if odArchive:
    if not odPassword:
      print "ERROR: OD Archive is specified, but archive password is not set, cannot continue!"
      return 2
## Create the OD Archive
    try:
      odDMG = odService(outputDir,odPassword)
    except:
      print "ERROR: An error occurred while creating OD Archive"
    print "   - Running OD Archive"
    if not odDMG.createArchive(outputDir,odPassword):
      print "ERROR: An error occured creating OD Archive, cannot continue!"
      return 3
    else:
      print "     - OD Archive created"


  ## Gather basic information
  hostname = platform.uname()[1]
  shortname = hostname.split(".")[0]
  osversion = platform.mac_ver()[0]
  arch = platform.mac_ver()[2]
  isServer = os.path.exists("/System/Library/CoreServices/serverversion.plist")
  isXsan = os.path.exists("/Library/Filesystems/Xsan")
  OSserialNumber = ""
  HWserialNumber = ""
  
  ## Read in serialnumber
  if isServer:
    snPath = "/etc/systemserialnumbers/xsvr"
    if os.path.exists(snPath):
      try:
        fileHandle = open(snPath)
        OSserialNumber = fileHandle.readline()
        fileHandle.close()
      except:
        print "ERROR: Could not read OS X Server serial number data at %s!" % snPath
        
  sabackupDict = {}
  sabackupDict["hostname"] = hostname
  sabackupDict["shortname"] = shortname
  sabackupDict["osversion"] = osversion
  sabackupDict["arch"] = arch
  sabackupDict["isServer"] = isServer
  sabackupDict["osxsserialnumber"] = OSserialNumber
  
  globalDict["sabackup"] = sabackupDict
  
  ## If no services were specified, determine running services
  if not serviceList or len(serviceList) == 0:
    print "   - Determining Active Services..."
    serviceList = myController.getRunningServiceList()
    if serviceList and len(serviceList) > 0:
      print "     - Found Running Services: %s" % serviceList
    else:
      print "   - Error: No Running Services found!"
  
  ## If specfied "all" in servicelist, use all registeredService
  elif "all" in serviceList:
    serviceList = registeredServices
  
  ## if we specified "runnning" as a service, append all registered services
  ## to our serviceList
  elif "running" in serviceList:
    serviceList.extend(myController.getRunningServiceList())
  
  print "*  Preflight Finished."
  print "*  Running backups!"


  ## Set appropriate variables on our backup controller
  myController.restoreFromBackup = restoreFromBackup
  myController.useSubDirs = useSubDirs
  myController.useTimeStamps = useTimeStamps
  
  backupdt = datetime.datetime.today()
  timeStamp = "%02d%02d%02d_%02d%02d" % (backupdt.year,
                                        backupdt.month,
                                        backupdt.day,
                                        backupdt.hour,
                                        backupdt.minute)
                                        
  myController.timeStamp = timeStamp
  myController.overWriteExistingFiles = overWriteExistingFiles
  
  ## Pruning
  myController.setPruneOptions(pruneOptions)
  myController.pruneBackups = pruneBackups
  
  
  myController.setServices(serviceList)
  myController.setBackupPath(backupTarget)
  
  
  backupStatus = myController.backupSettings()
  

  print "*  serveradmin backups complete"    
  '''
  if not singleFileOutput:
    globalFileName = "sa_global.plist"
    globalFilePath = os.path.join(backupTarget,"sa_global.plist")
  else:
    globalFileName = os.path.basename(backupTarget)
    globalFilePath = backupTarget
    
  print "  - writing plist %s" % globalFilePath
  ## Check for our 'latest.plist' file
  if os.path.exists(globalFilePath):
    try:
      os.remove(globalFilePath)
    except IOError, strerror:
      print "Could remove file %s! Error:'%s'" % (globalFileName,strerror)
      return False
    except:
      print "An unknown error occured removing global plist: '%s'" % globalFileName
      return False
  
  for name,serviceObj in myServices.iteritems():
    key = "%s Config" % serviceObj.displayName
    if len(serviceObj.plistDict) == 0:
      print "Plist for service:%s is empty!" % serviceObj.displayName
      continue
    else:
      if key in serviceObj.plistDict:
        globalDict[key] = serviceObj.plistDict[key]
      else:
        print "Key: %s does not exist in plist for service: %s" % (key,serviceObj.displayName)
        continue
  try:
    plistlib.writePlist(globalDict,globalFilePath)
  except IOError, strerror:
    print "Could not write plist file to '%s'! Error:'%s'" % (globalFilePath,strerror)
  except:
    print "An unknown error occured writing plist to '%s'" % globalFilePath
'''
  print "*  Backup routine complete."
  print "*  Cleaning up..."

  if useDiskImage:
    if saDMG.unmount():
      print "   - Unmounted Disk Image at mountpoint:'%s'" % saDMG.mountpoint
    else:
      print "   - Failed to unmount volume at '%s', hdiutil Error:%s" % (saDMG.mountpoint,saDMG.lastError)
      
  print "*  Cleanup complete."

  if len(myController.services) == 0:
    print "Backup Failed - No services were found to backup!"
    return 8
  elif len(myController.failedServices) == 0:
    print "Backup Finished - All services were successfully backed up!"
    return 0
  elif len(myController.failedServices) == len(myController.services):
    print "Backup Failed - All services failed to backup!"
    return 9
  else:
    print "Backup Complete: The following services failed to backup:"
    for service in myController.failedServices:
      print " %s - %s" % (service.name,service.lastError)
    return 10

if __name__ == "__main__":
  sys.exit(main())
    

