{-# LANGUAGE StaticPointers, FlexibleInstances #-}
import Haste.App
import Haste.DOM
import Haste.Events
import Haste.Ajax

import System.Directory
import Data.List
import Filemanip

instance Node Server

-- `appendChildren parent children` adds a list of children to a parent element
appendChildren :: Elem -> [Elem] -> Client ()
appendChildren parent children = sequence_ [appendChild parent c | c <- children]

-- Server sanity-check function: Prints to CLI
greet :: RemotePtr (String -> Server ())
greet = static (native $ remote $ liftIO . putStrLn)

-- Get log files from the server
getFiles :: RemotePtr (Server [FilePath])
getFiles = static (remote . liftIO $ listDirectory "./data")

-- File name extension slicing
sliceExt :: FilePath -> String
sliceExt filename = takeWhile (/='.') filename

-- Helper sanitize function. Very rigid as of now.
sanitize :: FilePath -> FilePath
sanitize f = if f == "./data" then "./data" else "?"
 
-- Put files retrieved from the server into the browser
putFiles :: [FilePath] -> Client ()
putFiles [] = return ()
putFiles (file:filelist) = do
  withElem "list" $ \list -> do
    li <- newElem "li" `with` [ attr "class" =: "list-item" ] 
    name <- newElem "span" `with` [ attr "id" =: (sliceExt file), prop "innerHTML" =: (sliceExt file ++ "   ") ]
    add <- newElem "a" `with` [ attr "href" =: "#", attr "id" =: file, prop "innerHTML" =: "Add" ]
    spacing <- newElem "span" `with` [ prop "innerHTML" =: "     " ]
    -- Remember to change this to a .pdf relative file path once features are implemented!
    dl <- newElem "a" `with` [ attr "href" =: ("./data/" ++ file) , prop "innerHTML" =: "Download" ]
    appendChild list li
    appendChildren li [name, add, spacing, dl]
    putFiles filelist

putFiles' :: FilePath -> Client ()
putFiles' file = do
  withElem "list" $ \list -> do
    li <- newElem "li" `with` [ attr "class" =: "list-item" ] 
    name <- newElem "span" `with` [ attr "id" =: (sliceExt file), prop "innerHTML" =: (sliceExt file ++ "   ") ]
    add <- newElem "a" `with` [ attr "href" =: "#", attr "id" =: file, prop "innerHTML" =: "Add" ]
    spacing <- newElem "span" `with` [ prop "innerHTML" =: "     " ]
    -- Remember to change this to a .pdf relative file path once features are implemented!
    dl <- newElem "a" `with` [ attr "href" =: ("./data/" ++ file) , prop "innerHTML" =: "Download" ]
    appendChild list li
    appendChildren li [name, add, spacing, dl]

-- Takes a filename, and creates a log entry form
appendForm :: Elem -> Client ()
appendForm filetag = withElems ["appendForm","appendTitle"] $ \[aF,aT] -> do
  filem <- getFirstChild filetag
  case filem of 
    Just x -> do 
      filename <- getProp x "innerHTML"
      setProp aT "innerHTML" ("Add your log entry to " ++ filename ++ " using the form below")
      setAttr aF "id" filename
      putForm aF "Date:" "date" 
      putForm aF "Task type:" "typetask"
      putForm aF "Status:" "status"
      putForm aF "Comments:" "comments"
      putForm aF "Supporting Documents:" "doc"
      -- Submission buttom
      submit <- newElem "input" `with` [ attr "type" =: "submit", attr "value" =: "Submit" ]
      appendChild aF submit
      -- implement below TODO
    Nothing -> return ()

-- Helper input creation function
formEntry :: String -> String -> Client Elem
formEntry attr1 attr2 = do 
  newElem "input" `with` [ attr "text" =: attr1, attr "name" =: attr2 ]

putForm :: Elem -> String -> String -> Client ()
putForm formelem msg id = do
  span <- newElem "span" `with` [ prop "innerHTML" =: msg ]
  br <- newElem "br"
  date <- formEntry "input" id
  br2 <- newElem "br"

  appendChildren formelem $ [span,br,date,br2]

-- Takes a filename, a list of log headers, and creates a new latex project log file
-- This is (obviously) done server-side. Also, pdflatex should be run
-- after appending (temporarily for now, as this is not so efficient)
-- createLog :: RemotePtr (String -> [String] -> Server ()) 

-- Takes a filepath, a list of log entries, and appends to the latex project log file
-- Also done server-side
-- writeLog :: RemotePtr (FilePath -> [String] -> Server ())

-- Takes a filename, and creates a log creation form
-- ?

-- Creates a form for creating a new log when clicked
creationForm :: Elem -> Client ()
creationForm elem = do
  -- create the form
  putForm elem "Project Log Name" "projName"
  putForm elem "Author name" "author"
  putForm elem "Members (seperated by commas)" "members"
  submit <- newElem "input" `with` [ attr "type" =: "submit", attr "value" =: "Submit" ]
  appendChild elem submit

-- Run the application
main = runApp [start (Proxy :: Proxy Server)] $ do
  -- fetch stored tex files. Sanitize the input first!
  files <- dispatch getFiles
  mapM_ putFiles' files

  ul <- elemsByQS document "ul#list"
  case ul of
    (el:_) -> mapQS_ document "#list li" $ \el -> do (el `onEvent` Click $ \_ -> do appendForm el)
    _      -> return ()

  withElems ["btn","formNew","formNewF"] $ \[btn,header,fm] -> do
    btn `onEvent` Click $ \_ -> do
      setProp header "innerHTML" "Create your Project Log using the form below"
      creationForm fm

  -- withElem "appendForm"      
  return ()