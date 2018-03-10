module Filemanip
( createFile ) where

import System.Directory
import System.IO

-- A log header
data LogHeader = LogHeader { projName :: String,
                             author :: String,
                             members :: [String]
                           } deriving (Read, Show)

{- appendtoFile :: FilePath -> LogEntry -> IO ()
appendtoFile filename entry = do
  return () -}

createFile :: LogHeader -> IO ()
createFile header = do
  let filename = (projName header) ++ ".tex"
  copyFile "temp2.tex" filename
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
    hPutStr handle "\\end{document}"
    hClose handle
    return ()

listItem :: Handle -> String -> IO ()
listItem handle member = do
  hPutStrLn handle ("\\item " ++ member)