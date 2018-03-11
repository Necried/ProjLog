module Filemanip
( appendToFile
, createFile
) where

import System.Directory
import System.IO
import System.Process

-- A log header
data LogHeader = LogHeader { projName :: String,
                             author :: String,
                             members :: [String]
                           } deriving (Read, Show)

-- A log entry data-type
data LogEntry = LogEntry { date :: String
                         , originator :: String
                         , typetask :: String
                         , status :: String
                         , comments :: String
                         , doc :: String
                         } deriving (Read, Show)

appendToFile :: FilePath -> LogEntry -> IO ()
appendToFile file entry = do
  -- Assuming FilePath argument is without directory and extension
  let filename = "data/" ++ file ++ ".tex"
  handle <- openFile filename ReadMode  
  (tempName, tempHandle) <- openTempFile "data" "temp"  
  contents <- hGetContents handle 
  hPutStr tempHandle $ (unlines . takeWhile (/= "\\end{tabularx}") . lines) contents
  let a = (date entry) ++ " & "
      b = (originator entry) ++ " & "
      c = (typetask entry) ++ " & "
      d = (status entry) ++ " & "
      e = (comments entry) ++ " & "
      f = (doc entry) ++ "\\\\\n\\hline"
  hPutStrLn tempHandle $ a ++ b ++ c ++ d ++ e ++ f
  hPutStr tempHandle $ (unlines . dropWhile (/= "\\end{tabularx}") . lines) contents
  hClose handle  
  hClose tempHandle  
  removeFile filename  
  renameFile tempName filename
  callProcess "pdflatex" ["-output-directory","files",filename]
  return ()

createFile :: LogHeader -> IO ()
createFile header = do
  let filename = "data/" ++ (projName header) ++ ".tex"
  fileExists <- doesFileExist filename
  if fileExists then do putStrLn "File already exists!" -- Error message to webapp
  else do
  copyFile "data/template.tex" filename
  withFile filename AppendMode $ \handle -> do
    hPutStrLn handle (projName header ++ "}")
    hPutStrLn handle ("\\author{" ++ (author header) ++ "}")

    -- Create Title and Author
    hPutStr handle "\\date{\\today}\n\\begin{document}\n\\maketitle\n"

    -- Team members
    hPutStrLn handle "\\section{Team Members}"
    hPutStrLn handle "\\begin{itemize}"
    mapM_ (listItem handle) $ members header
    hPutStrLn handle "\\end{itemize}"

    -- Skeleton table
    hPutStrLn handle "\\newpage\n\\section{Logs}"
    createTable handle

    -- Closing functions
    hPutStr handle "\\end{document}"
    hClose handle

listItem :: Handle -> String -> IO ()
listItem handle member = do
  hPutStrLn handle ("\\item " ++ member)

createTable :: Handle -> IO ()
createTable handle = do
  hPutStrLn handle "\\begin{table}[h]"
  hPutStrLn handle "\\begin{tabularx}{\\textwidth}{|X|X|X|X|X|X|X|}"
  hPutStrLn handle "\\hline"
  hPutStrLn handle "Timestamp & Originator & Type & Status & Comments & Supporting Documents\\\\\n\\hline"
  hPutStrLn handle "\\end{tabularx}\n\\end{table}"

