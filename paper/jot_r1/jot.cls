% Journal of Object Technology 
%
% LaTeX style class
% Version: 2.6, 2022/04/28
%
% Credits
% 
% Olivier Flückiger (author short bio fix)
%
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{jot}[2022/05/28, v2.6]

\AtEndOfClass{\RequirePackage{microtype}\ifthenelse{\boolean{displaylineno}}{\linenumbers}{}}

\RequirePackage[switch,pagewise]{lineno}
\RequirePackage{xifthen}

\newboolean{displaycopyright}
\newboolean{displaylineno}
\setboolean{displaylineno}{false}
\DeclareOption{lineno}{\setboolean{displaylineno}{true}}
\DeclareOption{10pt}{\PassOptionsToClass{\CurrentOption}{extarticle}}
\DeclareOption{twocolumn}{\PassOptionsToClass{\CurrentOption}{extarticle}}
\DeclareOption{twosided}{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ExecuteOptions{10pt,twocolumn,twosided}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ProcessOptions*
\LoadClass{extarticle}

\RequirePackage[utf8]{inputenc}
\RequirePackage[english]{babel}
\RequirePackage{amsmath,amsfonts,amssymb}
\RequirePackage{mathpazo}
\RequirePackage[scaled]{helvet}
\RequirePackage{times}
\RequirePackage[T1]{fontenc}
\RequirePackage[colorlinks=true,allcolors=blue]{hyperref}
\RequirePackage{url}

\RequirePackage{lettrine}
\RequirePackage{titling}
\RequirePackage{xstring}
\RequirePackage{breakurl}


% JOT details command

\let\jot@maketitle\maketitle
\renewcommand{\maketitle}{%
    \urlstyle{APACrm}
    \jot@maketitle
    \thispagestyle{firststyle}
    \marginmark
    \firstpagefootnote
}
%\let\url\relax
%\renewcommand{\url}[1]{\href{#1}{#1}}
%\AtBeginDocument{}
\AtBeginDocument{}

\@onlypreamble{\jotdetails}     % \jotdetails{key=value}
                                % possible keys:
                                % year, volume, number, doi, url, dates received/published/revised...

\newcommand\jot@doiderefaddress{http://dx.doi.org/}
\newcommand\jot@doijournalprefix{10.5381}

% Initialize properties to default values

\let\jot@year\@empty
\let\jot@volume\@empty
\let\jot@number\@empty
\let\jot@articleno\@empty
\let\jot@received\@empty
\let\jot@published\@empty
\let\jot@revised\@empty
\let\jot@license\@empty
\newcommand{\jot@declaredfirstpage}{1}
\let\jot@doi\@empty
\newcommand{\jot@url}{\jot@journaladdress}

\newcommand{\jot@lastauthor}{}

% Declare keys for \jotdetails
\define@key{jot@details@keys}{year}{\renewcommand{\jot@year}{#1}}
\define@key{jot@details@keys}{volume}{\renewcommand{\jot@volume}{#1}}
\define@key{jot@details@keys}{number}{\renewcommand{\jot@number}{#1}}
\define@key{jot@details@keys}{articleno}{\renewcommand{\jot@articleno}{#1}}
\define@key{jot@details@keys}{received}{\renewcommand{\jot@received}{#1}}
\define@key{jot@details@keys}{published}{\renewcommand{\jot@published}{#1}}
\define@key{jot@details@keys}{revised}{\renewcommand{\jot@revised}{#1}}
\define@key{jot@details@keys}{license}{\renewcommand{\jot@license}{#1}}
\define@key{jot@details@keys}{firstpage}{\renewcommand{\jot@declaredfirstpage}{#1}}
\define@key{jot@details@keys}{doi}{\renewcommand{\jot@doi}{#1}}
\define@key{jot@details@keys}{doisuffix}{\renewcommand{\jot@doi}{\jot@doijournalprefix/#1}}
\define@key{jot@details@keys}{url}{\renewcommand{\jot@url}{#1}}

% argument is a comma seperated list of the type "volume=6,year=8,..."
% If we have details of section we are interested in, process it

\newcommand{\jotdetails}[1]{\setkeys{jot@details@keys}{#1}}

\newcommand{\watermarkfont}{\color{watermarkcolor}\normalfont\fontsize{10}{12}\selectfont}
\newcommand{\aheaderfont}{\color{headercolor}\normalfont\sffamily\bfseries\fontsize{10}{12}\selectfont}
\newcommand{\headerfont}{\color{white}\normalfont\sffamily\bfseries\fontsize{10}{12}\selectfont}
\newcommand{\runningfont}{\normalfont\sffamily\fontsize{10}{12}\selectfont}

\newcommand{\titlefont}{\color{headercolor}\normalfont\sffamily\bfseries\fontsize{21}{23}\selectfont}
\newcommand{\datesfont}{\normalfont\sffamily\itshape\fontsize{8}{10}\selectfont}
\renewcommand\UrlFont{\color{urlcolor}\sffamily}

\let\texttt\relax
\newcommand{\texttt}[1]{{\fontfamily{cmtt}\selectfont #1}}
\def\verbatim@font{\fontfamily{cmtt}\fontsize{8}{10}\selectfont}%
\def\listing@font{\fontfamily{cmtt}\fontsize{8}{10}\selectfont}

\newcommand{\absfont}{\normalfont\sffamily\linespread{1.2}\fontsize{10}{12}\selectfont}
\newcommand{\keywordsfont}{\normalfont\sffamily\linespread{1.2}\fontsize{8}{10}\selectfont}
\newcommand{\copyrightfont}{\normalfont\sffamily\fontsize{8}{10}\selectfont}

% hyperlink colors

\RequirePackage{hyperref}
\hypersetup{colorlinks,linkcolor={urlcolor},citecolor={urlcolor},allcolors={urlcolor}}  

\RequirePackage{datetime}

\newdateformat{monthyeardate}{\monthname[\THEMONTH] \THEYEAR}

\RequirePackage{enumitem} 
\setlist[itemize]{noitemsep}

% Author and affiliation

\RequirePackage{authblk}
\setlength{\affilsep}{0.1em}
\renewcommand\Authfont{\color{authorcolor}\normalfont\sffamily\bfseries\fontsize{9}{13}\selectfont}
\renewcommand\Affilfont{\color{authorcolor}\normalfont\sffamily\fontsize{8}{10}\selectfont}

\renewcommand\AB@affilsepx{\\ \protect\Affilfont}
\renewcommand\Authsep{, }
\renewcommand\Authand{ and }
\renewcommand\Authands{, and }

% Article category color scheme
%
% color scheme 1
\newcommand*{\articletype}[1]{%
    \ifthenelse{\equal{#1}{manual}}{\newcommand*{\articletypename}{MANUAL}\definecolor{headercolor}{RGB}{143, 45, 86}}{} 
    \ifthenelse{\equal{#1}{regular}}{\newcommand*{\articletypename}{RESEARCH ARTICLE}\definecolor{headercolor}{RGB}{27,105,116}}{}
    \ifthenelse{\equal{#1}{editorial}}{\newcommand*{\articletypename}{EDITORIAL}\definecolor{headercolor}{RGB}{33, 131, 128}}{}
    \ifthenelse{\equal{#1}{column}}{\newcommand*{\articletypename}{COLUMN}\definecolor{headercolor}{RGB}{147, 84, 177}}{}
    \ifthenelse{\equal{#1}{tobedecided}}{\newcommand*{\articletypename}{TOBEDECIDED}\definecolor{headercolor}{RGB}{52, 196, 148}}{}
}
% color scheme 2
% \newcommand*{\articletype}[1]{%
%     \ifthenelse{\equal{#1}{manual}}{\newcommand*{\articletypename}{MANUAL}\definecolor{headercolor}{RGB}{160, 102, 171}}{}
%     \ifthenelse{\equal{#1}{regular}}{\newcommand*{\articletypename}{RESEARCH ARTICLE}\definecolor{headercolor}{RGB}{109, 101, 107}}{}
%     \ifthenelse{\equal{#1}{editorial}}{\newcommand*{\articletypename}{EDITORIAL}\definecolor{headercolor}{RGB}{54,117,174}}{}
%     \ifthenelse{\equal{#1}{column}}{\newcommand*{\articletypename}{COLUMN}\definecolor{headercolor}{RGB}{169,192,42}}{}
%     \ifthenelse{\equal{#1}{tobedecided}}{\newcommand*{\articletypename}{TOBEDECIDED}\definecolor{headercolor}{RGB}{130,0,0}}{}
% }
  
% Graphics, tables and other formatting
\RequirePackage{graphicx,xcolor}
\RequirePackage{colortbl}
\RequirePackage{booktabs}
\RequirePackage{tikz}
\RequirePackage{algorithm}
\RequirePackage[noend]{algpseudocode}
\RequirePackage{changepage}
\RequirePackage[left=48pt,%
                right=42pt,%
                top=48pt,%
                bottom=60pt,%
                headheight=15pt,%
                headsep=10pt,%
                letterpaper,twoside]{geometry}%
\RequirePackage[labelfont={bf,sf},%
                labelsep=space,%
                figurename=Figure,%
                singlelinecheck=off,%
                justification=RaggedRight]{caption}
\setlength{\columnsep}{24pt} % Distance between the two columns of text
\setlength{\parindent}{12pt} % Paragraph indent

% Set document color scheme
\definecolor{watermarkcolor}{gray}{0.5} % 50% black for hrules
\definecolor{authorcolor}{RGB}{0,0,0} % Base color
\definecolor{urlcolor}{RGB}{59,90,198} % unused
% color2 defined by the specific article type style file

% Bibliography
% NEW: to show DOIs
\RequirePackage{apacite} % NEW: to show DOIs
\usepackage{natbib} 
\bibpunct{(}{)}{;}{author-year}{}{,}
\renewcommand{\cite}{\citep}
%\bibpunct{(}{)}{,}{a}{,}{;}

%\bibliographystyle{apalike}
%% NEW: to show DOIs, instead of apalike:  
\bibliographystyle{apacite} 

\addto{\captionsenglish}{\renewcommand{\refname}{References}}
\setlength{\bibsep}{0.0pt}




% Table style
\arrayrulecolor{authorcolor} % Set the color of the horizontal rules
\renewcommand{\arraystretch}{1.5} % Increased line spacing
\captionsetup[table]{position=below} % Reduce spacing below caption

% Algorithm style
% \makeatletter
\newcommand\fs@coloruled{\def\@fs@cfont{\bfseries}\let\@fs@capt\floatc@coloruled
  \def\@fs@pre{\kern2pt}%
  \def\@fs@post{\kern2pt{\color{headercolor}\hrule}\relax}%
  \def\@fs@mid{\kern2pt{\color{headercolor}\hrule}\kern2pt}%
  \let\@fs@iftopcapt\iftrue}
% \makeatother

\floatstyle{coloruled}
\restylefloat{algorithm}

% Headers and footers
\RequirePackage{fancyhdr}  % custom headers/footers
\RequirePackage{lastpage}  % Number of pages in the document
\pagestyle{fancy}          % Enables the custom headers/footers

\fancypagestyle{firststyle}{
    \fancyhead[R]{{\watermarkfont Journal of Object Technology |} \aheaderfont \articletypename}
    \fancyfoot[R]{\watermarkfont\small An AITO publication}
}

% \fancypagestyle{firststyle}{
%     \fancyhead[R]{{\watermarkfont Journal of Object Technology |} \aheaderfont \articletypename}
%     \fancyfoot[R]{\watermarkfont\small An AITO publication}
% }


\newcommand{\headerbox}[1]{\par\noindent\colorbox{headercolor}
{\parbox{\dimexpr\textwidth-2\fboxsep\relax}{#1}}}

% Headers
\fancyhead[LO,RE,LE,RO]{} % Blank headers for non-title pages.
% Footers
\lfoot{}
\cfoot{}
\rfoot{}
% \makeatletter
%\fancyhead[LE]{\thepage\ \hspace{2em} \@runningauthor \hspace{0.2em}}
\fancyfoot[LE]{\runningfont\thepage\ \hspace{2em} \@runningauthor \hspace{0.2em}\leftmarginmark}

%\fancyhead[RO]{\@runningtitle \hspace{2em} \thepage\ }
\fancyfoot[RO]{\runningfont\@runningtitle \hspace{2em} \thepage\ }
% \makeatother
\fancyfoot[LO,RE]{}
%\fancyfoot[RE]{\jot@volume:\jot@number}
\renewcommand{\headrulewidth}{0pt}% % No header rule
\renewcommand{\footrulewidth}{0pt}% % No footer rule


\setcounter{secnumdepth}{3}
\setcounter{tocdepth}{0}

% Section/subsection/paragraph set-up
\RequirePackage[explicit]{titlesec}
%\renewcommand{\thesubsection}{\thesection.\arabic{subsection}}

\newboolean{firstoccurrencesection}
\setboolean{firstoccurrencesection}{true}

\let\sec\section
\let\section\relax

\def\section{\@ifstar\@foo\@@foo}
\def\@foo#1{\sec*{#1}}
%\def\@@foo#1{\sec{#1 unstarred}}
\def\@@foo#1{%
    \ifthenelse{\boolean{firstoccurrencesection}}{\vspace{-0.6cm}\sec{#1}\setboolean{firstoccurrencesection}{false}}{\sec{#1}}
}

%\newcommand{\section@nostar}[1]{\ifthenelse{\boolean{firstoccurrencesection}}{\vspace{-1.7cm}\sec{#1}\setboolean{firstoccurrencesection}{false}}{\sec{#1}} 
%\newcommand{\section@star}[1]{\sec*{#1}}


\titleformat{\section}
  {\large\sffamily\bfseries}
  {\thesection.}
  {0.5em}
  {#1}
  []
\titleformat{name=\section,numberless}
  {\large\sffamily\bfseries}
  {}
  {0em}
  {#1}
  []
\titleformat{name=\subsection}
  {\sffamily\bfseries}
  {\thesubsection.}
  {0.5em}
  {#1}
  []
\titleformat{\subsubsection}[runin]
  {\sffamily\bfseries\itshape}
  {\thesubsubsection.}
  {.5em}
  {#1}
  []
\titleformat{\paragraph}[runin]
  {\sffamily\small\bfseries}
  {}
  {0em}
  {#1}
  

% Article Sectioning

\titlespacing*{\section}{0pc}{3ex \@plus4pt \@minus3pt}{5pt}
\titlespacing*{\subsection}{0pc}{2.5ex \@plus3pt \@minus2pt}{2pt}
\titlespacing*{\subsubsection}{0pc}{2ex \@plus2.5pt \@minus1.5pt}{12pt}
\titlespacing*{\paragraph}{0pc}{1.5ex \@plus2pt \@minus1pt}{12pt}

% Article meta data additional fields

\newcommand{\runningauthor}[1]{\def\@runningauthor{#1}}
\newcommand{\correspondingauthor}[1]{\runningauthor{#1}}
\newcommand{\keywords}[1]{\def\@keywords{#1}}
\newcommand{\runningtitle}[1]{\def\@runningtitle{#1}}
\newcommand{\keywordname}{KEYWORDS} 

% Header

\newcommand{\marginmark}{
    \begin{textblock}{2}(209,9) 
        \begin{tikzpicture}
            \fill[color=headercolor] (0,0) rectangle (1.5,26.4); %8.55
        \end{tikzpicture}
    \end{textblock}
    \begin{textblock}{2}(12,9.8) 
        \thelogo
    \end{textblock}
    %\begin{textblock}{2}(12,276.6) 
    % \begin{textblock}{2}(12,276.6) 
    %     \begin{tikzpicture}
    %         \fill[color=headercolor] (0,0) rectangle (2,0.3);
    %     \end{tikzpicture}
    % \end{textblock}
}

\newcommand{\leftmarginmark}{
    \begin{textblock}{2}(14,277) 
        \begin{tikzpicture}
            \fill[color=headercolor] (0,0) rectangle (2,0.3);
        \end{tikzpicture}
    \end{textblock}
}

\def\jot@abstract{abstract}
\long\def\abstract#1\end#2{\def\two{#2}\ifx\two\jot@abstract
\long\gdef\theabstract{\ignorespaces#1}
\def\go{\end{abstract}}\else
#1\end{#2}
\let\go\relax\fi
\go}

% Set environment for abstract content and styling
\newcommand{\abscontent}{
\noindent
{%
\parbox{\dimexpr\linewidth}{%
    %% v1.8: turn on line numbers
	\ifthenelse{\boolean{displaylineno}}{\internallinenumbers}{}%
    {\absfont\bfseries ABSTRACT} \absfont \theabstract
}%
\vskip10pt%
\noindent
\parbox{\dimexpr\linewidth-2\fboxsep\relax}{%
 %% v1.8: turn on line numbers
\ifthenelse{\boolean{displaylineno}}{\internallinenumbers}{}%
{\keywordsfont\bfseries\keywordname}\hspace*{0.1em} \keywordsfont \@keywords%
}%
}%
}%

% JOT logo
%

\newcommand{\thelogo}{
%	\newwrite\tempfile
%	\immediate\openout\tempfile=logo.base64
%	\immediate\write\tempfile{\logoraw}
%	\immediate\closeout\tempfile
%	\immediate\write18{base64 -d logo.base64 > logo.png}
%	\includegraphics[width=4cm]{logo.png}
	\includegraphics[width=4cm]{logo/logo.png}
}

\newcommand{\logoraw}{iVBORw0KGgoAAAANSUhEUgAACncAAAOECAYAAAB5ePYkAAAgAElEQVR4nOzdf9B3dV3n8dfND/khigIJ5I9ULDCFo0cCFS2FUlKy3HQz++WalTvZrqVbHlpbcaxjlrXO7JTVlLlqZbqVRehUNkk1ItGRA+SPUtPQ1AwBRZBfN/vHde3qfXtzc99wne/7XOf7eMycuWZumLmeM3zv7x+H13w+O7pLLr4tAAAAbAev6U897YXVEQAAADCl227zvy8BAAAOqA4AAAAAAAAAAAAA4EuMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEYOqg7YR3+f5LrqCAAAYNFOSnJsdQQAAAAAAADAdhl3Pq8/9bRLqyMAAIDl6i65+LeT/EB1BwAAAAAAAIBr2QEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEaMOwEAAAAAAAAAAABmxLgTAAAAAAAAAAAAYEYOqg4AAAAAANgq/TjcI8l9khyd5F5JDt/8R0cm2ZHk0M1nd9ckuSnJ9Uk+n+RzSa7+f0/XtDunLQcAAAAA+BLjTgAAAABgW+jH4bgkD958HrT58wFJjs3GmPPoJAdP8Kt39uPwb0k+meTTST6W5KObzz8n+WDXtNdM8HsBAAAAgDVl3AkAAACwm34cXpI9n+y3XV3UNe07qiNgX/XjcN8kpyZ5eJKTk3x9kockOawo6YAkx20+e7Q5/vxAksuTXJbk0iSXd017w0oK2db6cXhWkpOqO2BNfbFr2ldWRwAAAMDujDsBAAAAvtJLsnGF81K8JolxJ7PUj8MRSU5Pcsbmz0dl4yTO7eY+m883ftmf3dqPw5jk4iQXJXlX17QfLWhj/p6V5NurI2BNXZvEuBMAAIDZMe4EAAAAAFamH4fDszHkPCvJNyd5RJIDS6Omc2CSdvN5fpL043BlkguT/FmSP+ua9lN1eQAAAADAXBl3AgAAAACT6sfhIUmemuQpSZ6Q5G6lQbXun+R7Np/043BZkvOTvC3J33VNe1thGwAAAAAwE8adAAAAAMCW68fh5CTPTPL0JA8vzpmzUzafc5N8sh+HP0jy5iR/2zXtztIyAAAAAKCMcScAAAAAsCX6cTghybOzcSrlicU529HxSX508/l4Pw6/l+T1XdNeUZsFAAAAAKyacScAAAAAcKf143BEku9K8twkjy3OWZL7JXlxkhf343BJkt9K8qauaT9XmwUAAAAArIJxJwAAAACw3/pxaJK8IMmzkhxRnLN0p24+r+rH4Y1JfqVr2suLmwAAAACACRl3AgAAAAD7pB+Hg5J8Z5IfS3JGcc46OiLJ85M8vx+HdyZ5dZJ3dE17W20WAAAAALDVjDsBAAAAgL3avHr9B5P8eJKvKc5hw1mbzz/049AneXPXtLcUNwEAAAAAW8S4EwAAAADYo81R5wuSvDjJ0cU57NnDkrwxyXn9OLwiyRuNPAEAAABg+zPuBAAAAAB2YdS5LZ2Q5HVJun4czk3yB65rBwAAAIDt64DqAAAAAABgHvpxOKIfh5ck+WiSPoad29HXJXlrkvf04/DE6hgAAAAA4M5xcicAAAAArLl+HA5K8iNJXpbkmNoatsg3JPnLfhzekaTrmvbS6iAAAAAAYN85uRMAAAAA1lg/DuckuTzJ/4ph5xKdnWTox+G1/TgcVR0DAAAAAOwbJ3cCAAAAwBrqx6FJ8uokZ1W3MLkd2TiZ9Zn9OPx0kl/vmnZncRMAAAAAsBdO7gQAAACANdKPw1H9OLw2yXtj2Llujkryq0ku7sfh9OoYAAAAAOD2ObkTAAAAANZAPw47kjwnyavi+vV196gk7+7H4TeS/FTXtNdUBwEAAAAAu3JyJwAAAAAsXD8OX5vkL5P8Vgw72bAjyQ8n+Yd+HL6jOgYAAAAA2JWTOwEAAABgofpxODDJi5Kcl+TQ4hzm6auT/GE/Dr+T5L90TXtVdRAAAAAA4OROAAAAAFikfhxOSvK3SX4+hp3csWcnuawfh6dWhwAAAAAATu4EAAAAgEXpx2FHkh9L8sokhxXnsL18dZLz+3H41SQ/0TXtF6uDAAAAAGBdObkTAAAAABaiH4djk1yQ5DUx7OTO+89JLunH4eTqEAAAAABYV8adAAAAALAA/TicneTyJGdXt7AID0tycT8Oz6sOAQAAAIB15Fp2AAAAANjG+nE4MMl5Sc5NsqM4h2U5NMlv9OPwTUme3zXtF6qDAAAAAGBdOLkTAAAAALapzWvY35nkp2PYyXS+N8m7+3F4SHUIAAAAAKwL404AAAAA2Ib6cTg9yd8n+abqFtbCyUn+rh+Hb60OAQAAAIB1YNwJAAAAANtMPw7PTXJhkvtWt7BW7pXk/H4cXlQdAgAAAABLd1B1AAAAAACwb/pxODDJq5L8RHULa+uAJL/Yj8NJSX60a9qbqoMAAAAAYImc3AkAAAAA20A/DndP8kcx7GQenpfkgn4cjqwOAQAAAIAlMu4EAAAAgJnrx+G4bFzDfk51C3yZs5L8dT8O96sOAQAAAIClMe4EAAAAgBnbvP76oiRtdQvswclJLurH4aHVIQAAAACwJMadAAAAADBT/Th8Q5K/TvI11S2wF/dNcmE/DqdVhwAAAADAUhh3AgAAAMAM9eNwZpJ3JjmmugX2wTFJ3rn5uQUAAAAA7iLjTgAAAACYmX4cvi3J+UnuUd0C++GIJOcbeAIAAADAXWfcCQAAAAAz0o/D05L8nySHVbfAnXBYkgs2P8cAAAAAwJ1k3AkAAAAAM7E5iHtrkoOrW+AuOCTJW/txOKs6BAAAAAC2K+NOAAAAAJgBw04W5uAkf+KKdgAAAAC4c4w7AQAAAKBYPw5PjmEny3NYkvP7cXh0dQgAAAAAbDfGnQAAAABQqB+HM5L8YQw7WabDkry9H4eTq0MAAAAAYDsx7gQAAACAIv04NEkuyMYADpbqXkn+rB+HB1WHAAAAAMB2YdwJAAAAAAX6cXhgknckuWdxCqzCcdk4wfPo6hAAAAAA2A6MOwEAAABgxTYHbu/IxuAN1sWJSf64Hwcn1QIAAADAHTDuBAAAAIAV6sfhkCR/nI2hG6ybxyZ5XT8OO6pDAAAAAGDOjDsBAAAAYEU2B22vy8bADdbVdyU5rzoCAAAAAObMuBMAAAAAVudnknx3dQTMwEv7cfB3AQAAAABux0HVAQAAAACwDvpxeEaSl1V3LNz1ST6a5JNJ/n3z+XSSzye5Jcl1m//etUmOSHJgkkOSHJbk8CTHJDk2ydGbPx+c5J4rq18/v9mPw/u7pr20OgQAAAAA5sa4EwAAAAAm1o/DKUl+u7pjQa5L8t4klyS5PMmHknyoa9pPbvUv6sfh6CQP2XxOTvKozefeW/271tBhSd7Wj8OpXdN+pjqm2O8lMXLdeo9O8uTqiC30wWx8VthaX6wOAAAAgD0x7gQAAACACfXjcFSSP0py9+qWbewzSf48yV8keXeSf+yaducqfnHXtFcluSrJe778z/txeHCSxyU5a/O57yp6FugBSd7Uj8PZq/pvOkdd0xrsTaAfhxdmWePOD3RN+7LqCAAAAGA1jDsBAAAAYCL9OOxI8oYkD6pu2YaGJG9J8vYkl3VNe1txzy66pv1Iko8k+d9J0o/DSUmemuSZSU4vTNuOviXJuUleUR0CAAAAAHNh3AkAAAAA03lpkqdUR2wj/5DkjUne0jXth6tj9kfXtB9I8oEkr+7H4QHZGHl+X5KmNGz7OK8fh7/umvZd1SEAAAAAMAfGnQAAAAAwgX4cHp/kf1R3bAM3Z+OEzl/pmvZvq2O2Qte0/5Lk1dkYep6W5EeSPCvJ4aVh83ZAkt/tx+ERXdP+W3UMAAAAAFQ7oDoAAAAAAJamH4d7J/mdeP+2N1cl+e9J7tc17fcsZdi5u65pL+6a9geT3C8bV49fVZw0Z8dnY+B5YHUIAAAAAFTzchkAAAAAtt6vZ2PMx1e6KkmX5IFd0/7supzS2DXt1V3T9knun+SFSa4sTpqrM5O8uDoCAAAAAKoZdwIAAADAFurH4YeSPKO6Y4auz8Y19Q/smvaVXdNeVx1UoWvaG7qmfU2SE5P8VJJri5Pm6OX9OJxcHQEAAAAAlYw7AQAAAGCL9ONwYpL/Wd0xQ29I8nVd0758XUedu9sceb4qyQlJXpPkluKkOblbkjf043BwdQgAAAAAVDHuBAAAAIAt0I/DQUnelOTw6pYZeW+S07um/f6uaT9RHTNHXdNe1TXtC5M0Sf6mumdGmiQvq44AAAAAgCrGnQAAAACwNV6U5FHVETPxxSQvSXJa17QXV8dsB13Tvi/JNyZ5XpLPFufMxUv6cXh0dQQAAAAAVDDuBAAAAIC7qB+Hk5KcV90xExcmOaVr2p/vmtZV4/uha9rbuqb9zSRfn+RPq3tm4IAkr+/H4dDqEAAAAABYNeNOAAAAALgL+nE4IMlvJDmkuqXYrUlemuTMrmn/qTpmO+ua9tNd056T5PlJvlDdU+zrknTVEQAAAACwasadAAAAAHDXvCDJ46ojiv1zksd1TfuKrmlvrY5Ziq5pfy3JI5NcVt1S7CX9OJxYHQEAAAAAq2TcCQAAAAB3Uj8OD0zyc9Udxf40Sds17UXVIUu0eQrqY5K8obql0N2SvLYfhx3VIQAAAACwKsadAAAAAHDn/XKSu1dHFOqTfHvXtNdUhyxZ17TXd037/Ul+NMnN1T1FnpDk+6ojAAAAAGBVjDsBAAAA4E7ox+HJSb6juqPIDUm+q2vac13Dvjpd0/5Kkqck+Vx1S5FX9+NwVHUEAAAAAKyCcScAAAAA7Kd+HO6W5DXVHUWuTvKkrml/vzpkHXVN+xdJzkhyZXVLgWOSvLw6AgAAAABWwbgTAAAAAPbff01yYnVEgSuTPK5r2r+pDllnXdNekeTRSa6obinw/H4cTqqOAAAAAICpGXcCAAAAwH7ox+H4JD9T3VHgw0ke2zXt+6pDSLqm/dckZ2b9Bp4HJvmF6ggAAAAAmJpxJwAAAADsnz7JEdURK/bhJE/omvbj1SF8Sde0n0ny+CQXV7es2Dn9OJxVHQEAAAAAUzLuBAAAAIB91I/Dw5N8f3XHihl2zljXtNckeVKSS6tbVuyX+nHwfhsAAACAxfLyCwAAAAD23c8m2VEdsUKfSPJEw85565r22mwMPD9c3bJCpyT5T9URAAAAADAV404AAAAA2Af9ODw2ydOqO1bo2iRnd017ZXUId2zzivazsjHIXRf/ox+Hu1VHAAAAAMAUjDsBAAAAYN+8sjpghW5M8rSuaa+oDmHfdU37sSTfmuS66pYVuX+S51ZHAAAAAMAUjDsBAAAA4A704/CUJI+v7lih53ZNe2F1BPuva9rLkzw7yc7qlhU51+mdAAAAACyRcScAAAAA3LGfrQ5YoV/qmvZ3qiO487qm/ZMkXXXHiji9EwAAAIBFMu4EAAAAgL3ox+HsJI+o7liRv0zyk9UR3HVd074qye9Xd6yI0zsBAAAAWBzjTgAAAADYu3OrA1bkE0me2TXtrdUhbJnnJflQdcQKOL0TAAAAgMUx7gQAAACA29GPw+OSPL66YwV2Jvmermk/Wx3C1uma9vNJnpnkxuqWFfjJfhy87wYAAABgMbzsAgAAAIDb99PVASvyc13Tvqs6gq3XNe2lSX68umMFHpTkP1RHAAAAAMBWMe4EAAAAgD3ox+GRSc6u7liB9yQ5rzqCSb02yTuqI1bgJ6oDAAAAAGCrGHcCAAAAwJ79t+qAFbgxyXO6pr2lOoTpdE17W5LnJbmmumVij+nH4YzqCAAAAADYCsadAAAAALCbfhyOT/KM6o4VeGnXtB+ojmB6XdN+IskLqjtWwOmdAAAAACyCcScAAAAAfKUfSXJwdcTE/j7JL1dHsDpd074pydurOyb29H4cTqiOAAAAAIC7yrgTAAAAAL5MPw53y8a4c8l2Jvkh17GvpRck+WJ1xIR2ZPl/fwEAAABYA8adAAAAALCr70xyXHXExF7bNe17qyNYva5pP5LkFdUdE3vO5kgbAAAAALYt404AAAAA2NWPVQdM7KokL62OoNQvJPnH6ogJfVWS76iOAAAAAIC7wrgTAAAAADb14/DIJI+p7pjYuV3TfrY6gjpd096U5CerOybmanYAAAAAtjXjTgAAAAD4kudUB0zsg0l+qzqCel3Tvi3JhdUdEzqzH4eHVEcAAAAAwJ1l3AkAAAAASfpxODjJs6s7JnZu17S3VEcwGy+qDpjYD1cHAAAAAMCdZdwJAAAAABuemuSY6ogJXZTkD6sjmI+uaS9J8ubqjgl9bz8O3oEDAAAAsC15sQUAAAAAG36gOmBiP9M17W3VEczOy5Ms9XNxfJInVkcAAAAAwJ1h3AkAAADA2uvH4ZhsnNy5VO/pmvbPqyOYn65p35fk96s7JvTd1QEAAAAAcGcYdwIAAADAxgDs4OqICfXVAczakk/vfEY/DodURwAAAADA/jLuBAAAAIDkP1YHTOiyJH9cHcF8bZ7eeUF1x0SOTPKU6ggAAAAA2F/GnQAAAACstX4c7pPkjOqOCf1S17RLPZWRrfOL1QETenZ1AAAAAADsL+NOAAAAANbd05PsqI6YyGeS/F51BPPXNe1fJRmqOyZyTj8Oh1VHAAAAAMD+MO4EAAAAYN09vTpgQr/WNe2N1RFsG79cHTCRQ5M8qToCAAAAAPaHcScAAAAAa6sfhyOTnFndMZFbk7y2OoJt5S1JrqqOmMi3VQcAAAAAwP4w7gQAAABgnZ2T5ODqiIlc0DXtJ6oj2D42T3l9fXXHRM7px8H7cAAAAAC2DS+zAAAAAFhnT6sOmNDrqgPYln69OmAixyY5rToCAAAAAPaVcScAAAAAa2nzFL+zqjsm8u9Jzq+OYPvpmvaDSS6s7pjIksfcAAAAACyMcScAAAAA6+oRSY6ujpjIG7umvbk6gm3rDdUBEzmnOgAAAAAA9pVxJwAAAADr6purAyb05uoAtrW3JrmpOmICJ/fj8FXVEQAAAACwL4w7AQAAAFhX31IdMJErk7ynOoLtq2vaa5JcUN0xkTOrAwAAAABgXxh3AgAAALB2+nE4NMnjqjsm8pauaW+rjmDb+93qgIk8sToAAAAAAPaFcScAAAAA6+iMJIdWR0zkLdUBLMIFSW6sjpiAkzsBAAAA2BaMOwEAAABYR4+pDpjIvyW5uDqC7a9r2uuSvLO6YwJf24/D/aojAAAAAOCOGHcCAAAAsI4eXR0wkbd3TbuzOoLFeFt1wESeUB0AAAAAAHfEuBMAAACAdXR6dcBE/rQ6gEX5kyS3VUdM4IzqAAAAAAC4I8adAAAAAKyVfhxOSHJMdccEbk3y59URLEfXtJ9Mcml1xwROrQ4AAAAAgDti3AkAAADAulnqqZ2XdE17TXUEi/PO6oAJPKIfh0OqIwAAAABgb4w7AQAAAFg3Sx13/lV1AIu0xNNgD0ryiOoIAAAAANgb404AAAAA1s1Sr2T+q+oAFulvktxUHTGBb6gOAAAAAIC9Me4EAAAAYN08rDpgArdmY4QHW6pr2uuTvKe6YwKnVQcAAAAAwN4YdwIAAACwNvpxuG+SI6s7JvDermmvq45gsd5dHTCBR1YHAAAAAMDeGHcCAAAAsE6+vjpgIhdXB7BoSxx3ntiPw0HVEQAAAABwe4w7AQAAAFgnS7ySPTHuZFpLHHcenOSE6ggAAAAAuD3GnQAAAACsE+NO2E9d0346yZXVHRN4aHUAAAAAANwe404AAAAA1skSx1xfSPLB6ggW773VARNY6tgbAAAAgAUw7gQAAABgnTykOmAC7++admd1BIt3WXXABE6sDgAAAACA22PcCQAAAMBa6MfhkCTHVndM4PLqANbCEj9nTu4EAAAAYLaMOwEAAABYF/evDpjIFdUBrIUlntz5gOoAAAAAALg9xp0AAAAArIulDrneVx3AWvhwklurI7bYMf04HFYdAQAAAAB7YtwJAAAAwLpY6rjzw9UBLF/XtDcn+Zfqjgks9XsBAAAAgG3OuBMAAACAdbHEa9l3JvlYdQRrY4lDYuNOAAAAAGbJuBMAAACAdbHEcefHu6a9qTqCtfFP1QETWOL3AgAAAAALYNwJAAAAwLo4pjpgAv9cHcBaWeK17MadAAAAAMyScScAAAAA6+Lo6oAJfLI6gLXyr9UBEzi+OgAAAAAA9sS4EwAAAIB1cVR1wASWOLZjvj5VHTCBe1cHAAAAAMCeGHcCAAAAsC6WOO78dHUAa+Xj1QETWOL3AgAAAAALYNwJAAAAwLpY4gl9Tu5klT5THTCBJX4vAAAAALAAxp0AAAAALF4/DocmOay6YwLXVAewVq6uDpiAkzsBAAAAmCXjTgAAAADWwVJP5/tcdQDro2vaW5JcX92xxYw7AQAAAJgl404AAAAA1sEh1QETubY6gLWztM/ckdUBAAAAALAnxp0AAAAAsH0tbWjH/C3uM9ePw1LH3wAAAABsY8adAAAAAKyDe1YHTMS17KzajdUBEzisOgAAAAAAdmfcCQAAAMA6WOp7sJ3VAawdnzkAAAAAWIGDqgMAYF0d9eBTn5PkddUdbAuv/+xHLnlOdQQAwDa31HEnrNoST4s9Isk11REAAAAA8OW81AYAAABgHSz1WvYbqgNgARyCAAAAAMDsGHcCAAAAwDbVNe2N1Q0AAAAAAGw9404AAAAA1sHN1QFT6MfhyOoGWIAd1QEAAAAAsDvjTgAAAICvdEh1wBa7qTpgBr5QHTARozRWbYlXmN9WHQAAAAAAuzPuBAAAAPhKh1YHbLHrqwOAxTiiOmACt1YHAAAAAMDujDsBAAAAWAc3VAdM5LDqAFiAz1cHAAAAAMDujDsBAAAAWAc3VgdMZImnKDJv96oOAAAAAIB1YNwJAAAAANvXPasDWDtL/MzdVB0AAAAAALsz7gQAAABgHVxdHTCRI6sDWDuL+8x1TXt9dQMAAAAA7M64EwAAAIDF65r22iQ7qzsmsMRTFJmpfhzunuW9U76hOgAAAAAA9mRpL+IAAAAA7pJ+HHZUNzCZJZ7e+VXVAayV+1QHTGCJ3wsAAAAALNjGmE8AACAASURBVIBxJwAAAMCuFnflMP/fEkdcxp2s0nHVARNY4vcCAAAAAAtg3AkAAACwfNdUB8zEZ6sDJnDf6gDWyvHVARNY4vcCAAAAAAtg3AkAAADAuljiCX1LvCab+Tq2OmACxp0AAAAAzJJxJwAAAADrYokjrvtVB7BWHlAdMIElfi8AAAAAsADGnQAAAAC72lEdMIHPVQfMxL9UB0zggdUBrJUTqgMmYNwJAAAAwCwZdwIAAADs6sjqgAnsrA6YiSurAyZwXD8Oh1dHsDYeXB0wgX+tDgAAAACAPTHuBAAAAGBdLPHkzmSZgzvmaYmftSWOvgEAAABYAONOAAAAgF0dUR0wgeuqA2bi49UBE1niVdnMTD8ORyW5d3XHBJY6+gYAAABgmzPuBAAAANjVQdUBE7ilOmAmljriemh1AGvhlOqAiSz1ewEAAACAbc64EwAAAGBXh1YHTOD66oA56Jr2qiQ3VHdM4OTqANbCw6oDJnBzkk9VRwAAAADAnhh3AgAAAOxqiePOm6oDZuRD1QETeHh1AGthiSPij3dNe1t1BAAAAADsiXEnAAAAwK4OrA6YwHXVATPy/uqACTy0H4eDqiNYvCWOOz9WHQAAAAAAt8e4EwAAAGBX96gOmMAt1QEzssRx58FZ5pXZzMTmeLit7pjA+6oDAAAAAOD2GHcCAAAALN+11QEzstQx1+nVASzaKUkOrY6YwFK/DwAAAABYAONOAAAAgF3dszpgAjurA2bkA9UBEzmtOoBFW+rny7gTAAAAgNky7gQAAADY1eHVARNwcueXfDDLHLs+ujqARVvquPP91QEAAAAAcHuMOwEAAAB2dffqgAlcXx0wF13T3pjkQ9UdE3hoPw5HVkewWN9YHTCBq7um/VR1BAAAAADcHuNOAAAAgF3dozpgi93cNe1N1REzc0l1wAQOyDIHeBTrx+EBSU6o7pjAFdUBAAAAALA3xp0AAAAAu1ra6YdfqA6YoYurAyZyVnUAi3RmdcBELqsOAAAAAIC9Me4EAAAA2NXSrmW/tjpghpZ4cmeSPKE6gEV6QnXARC6qDgAAAACAvTHuBAAAANjVEdUBW+zz1QEzNCS5tTpiAqf043BMdQTL0Y/DjiRPqu6YyFJP8AUAAABgIYw7AQAAAHa1tJM7Xcu+m65pb0hyRXXHBHYkeUp1BIvyyCTHV0dM4Jok/1QdAQAAAAB7Y9wJAAAAsKsjqwO22HXVATP1d9UBEzmnOoBFWepY+OKuaW+rjgAAAACAvTHuBAAAANjVPaoDttjV1QEz9a7qgIk8uR+Hg6sjWIynVgdMxJXsAMD/Ze/ewy+7B3uPf0YSQgjZgsStbGlRYtWyHbQOca2WQ4hbBXWpS1uKnmotpXXQLlp1e9rjVhpKqWuQRDhB6lKXjNWsSlVdJhG3IJlERBMSyfljb53QSDIze+/v2nu/Xs+znokxv73fk5nn9yy/38d3AQDA4Bl3AgAAAPykdRt3nlU6YKCOLx2wIPsmuXPpCFZf23fXTXK70h0L8snSAQAAAABwWYw7AQAAAH7SNUsHzJmTOy9BU9VfS/Ll0h0L8sDSAayFw5JsKR2xAD9K8pHSEQAAAABwWYw7AQAAAGbavrtCklHpjjlzcufPdlzpgAV5QNt3e5SOYOU9uHTAgnyqqervlY4AAAAAgMti3AkAAACww7oNOxPjzktzfOmABblWkruXjmB1zR7J/iulOxbkg6UDAAAAAODyMO4EAAAA2GHdHsmeeCz7pTm+dMACreupiyzHw7Oej2RPjDsBAAAAWBHGnQAAAAA7OLlzgzRVfVqSfy3dsSAPavtun9IRrKzHlA5YkHOTfKJ0BAAAAABcHsadAAAAADus48mdZ5QOGLj3lg5YkKsleVDpCFZP23d3SHLT0h0L8pGmqn9YOgIAAAAALg/jTgAAAIAd1nHc+Z3SAQP3ntIBC/TY0gGspHU9tTNJjikdAAAAAACXl3EnAAAAwA77lw5YgG+XDhi4E5KcVjpiQe7Y9t26nsDIArR9t1+Sh5XuWKAjSwcAAAAAwOVl3AkAAACww7VKB8zZeU1Vf790xJA1VX1RkqNKdyzQk0oHsFIek+QqpSMWpGuq+tTSEQAAAABweRl3AgAAAOxwvdIBc3ZG6YAVsc6PZn9023fXKB3B8LV9t0fWewz8rtIBAAAAALAzjDsBAAAAdjiwdMCcfat0wIo4Lsm6nnC6T5LfKh3BSrhfkhuVjlggj2QHAAAAYKUYdwIAAADssG4nd55eOmAVNFV9btb79M4nt323Z+kIBu8PSwcs0Jeaqj6pdAQAAAAA7AzjTgAAAIAdrl86YM5OKx2wQv6hdMAC3TDJw0tHMFxt390rye1KdyzQ20sHAAAAAMDOMu4EAAAASNL23bWSXLV0x5x9s3TACnl/ku2lIxboWU7v5FI8o3TAgv196QAAAAAA2FnGnQAAAABT49IBC/CN0gGroqnq85O8rXTHAt0kTu/kErR9d0iSO5fuWKDPNFX9udIRAAAAALCzjDsBAAAApm5SOmABvlU6YMW8qXTAgj3D6Z1cXNt3W5K8oHTHgr2hdAAAAAAA7ArjTgAAAICpg0oHLMDXSwesmI8lObV0xALdNMnjSkcwKA9IcrvSEQt0QZI3l44AAAAAgF1h3AkAAAAw9YulAxbAyZ07oanqi5L8XemOBXtO23dXKx1BebNTXP+8dMeCHdNU9XdKRwAAAADArjDuBAAAAJhax3Hn10oHrKDXJrmwdMQCXTvJH5aOYBB+J8kvlI5YsNeXDgAAAACAXWXcCQAAAGy82Ql2NyvdMWdnNFV9bumIVdNU9VeTHFO6Y8H+d9t3NyodQTlt310nyfNKdyzYN5K8p3QEAAAAAOwq404AAACA6el1e5WOmLOvlg5YYa8uHbBgV07y16UjKOovk+xbOmLBXt1U9QWlIwAAAABgVxl3AgAAACST0gELcGrpgBV2TNb/kfb3bvvu0NIRLF/bd7+S5BGlOxbs/CSvKh0BAAAAALvDuBMAAABgPcedTu7cRU1V/yjJa0t3LMHL2767aukIlqftu72zGX+339FU9WmlIwAAAABgdxh3AgAAACS3KR2wAMadu+fVmZ7+t85ukOTFpSNYqucluWnpiCX4m9IBAAAAALC7jDsBAACAjTY7yW4dx51fKR2wypqq/kaSN5XuWILHtX33q6UjWLy2726f5PdLdyxB31T1x0pHAAAAAMDuMu4EAAAANt3/SHKl0hEL8OXSAWvgr0oHLMnr2r67RukIFqftu32SHJHN+HrwX5YOAAAAAIB52IQv5gEAAABcmjuVDliQL5UOWHVNVZ+U5H2lO5bgukn+tnQEC/XybMbj2E9O8o+lIwAAAABgHow7AQAAgE13l9IBC7C9qeozS0esiReXDliSw9q+e1LpCOav7buHJnlM6Y4l+cumqi8oHQEAAAAA82DcCQAAAGys2aOK71i6YwE+XzpgXTRVfVySE0t3LMlftX13m9IRzE/bdwcleVXpjiU5LdNHzwMAAADAWjDuBAAAADbZPZJcsXTEAngk+3y9sHTAklwxydvavrtm6RB2X9t3V01yZJJ9S7csycuaqj63dAQAAAAAzItxJwAAALDJfq10wIIYd87XW5P0pSOW5MZJ3tH23TqOnjdG23dbkvx9kluUblmS7yZ5RekIAAAAAJgn404AAABgI7V9t0eS+5fuWJDPlQ5YJ01VX5jkOaU7lujOSV5eOoLd8uwkh5aOWKIXNVX93dIRAAAAADBPxp0AAADApjokybVKRyzIiaUD1tC7s1n/Xp/Q9t3TSkew89q+e1SS/1O6Y4m+leSlpSMAAAAAYN6MOwEAAIBN9aDSAQvyvSTbSkesm6aqL8pmDeaS5MVt3z2ydASXX9t390ry6tIdS/bnTVWfUzoCAAAAAObNuBMAAADYOG3f7Z3kwaU7FqSfDRGZs6aqj0zyqdIdS/a6tu/uUzqCy9b23e2SvD3JXqVblugrSV5ZOgIAAAAAFsG4EwAAANhEhyXZr3TEgmzSo8NLaEoHLNkeSd7a9t1dS4fws7V9d3CSDyTZp3TLkj2nqeoflo4AAAAAgEUw7gQAAAA20eNKByyQcecCNVX94STvLt2xZFdOclTbd3cvHcJ/Nxt2fijJvqVbluzfkryhdAQAAAAALIpxJwAAALBR2r67VZI7l+5YoK2lAzbA05OcXzpiya6c5Ji27+5bOoQd2r67dabDzv1LtxTwlKaqLywdAQAAAACLYtwJAAAAbJo/LB2wQN9LclLpiHXXVPUXk/x16Y4C9kry9rbvDi8dQtL23d2SHJ/NHHa+o6nqD5aOAAAAAIBFMu4EAAAANkbbdz+X5KGlOxbon5uq/lHpiA3x3CRnlI4oYK8kb2z77hmlQzZZ23cPTvK+bN6j2JPkvCR/UDoCAAAAABbNuBMAAADYJM9NskfpiAX6WOmATdFU9VlJ/qR0R0Ft23evbPtuz9Ihm6btu6cneXOmQ9tN9MKmqk8pHQEAAAAAi2bcCQAAAGyEtu+qJI8o3bFgHy8dsGFelWRr6YiCnpDk/7V9d53SIZug7bu92777+yR/kc39uu5XkrywdAQAAAAALMOmfhEQAAAA2CBt321J8pIkW0q3LNAFST5VOmKTNFX9oySPS/Kj0i0FHZJka9t3tysdss7avrt+ko8meXjplsKe0lT1uaUjAAAAAGAZjDsBAACATfDoJHcpHbFgn2qq+j9LR2yapqpPzHQ4vMmun+Qjbd/93mxIzRy1fXefJCcmmZRuKewfm6p+d+kIAAAAAFgW404AAABgrbV9d70kLy7dsQTHlg7YYH+a6eOiN9kVk7wsyTFt3x1YOmYdtH13pbbvXp7kvUmuWbqnsDOSPLl0BAAAAAAsk3EnAAAAsLbavtsjyRuTXL10yxIcUzpgU81OTH1i6Y6BuFeSf2377gGlQ1ZZ23e3TvLpGDT+2FOaqv5O6QgAAAAAWCbjTgAAABgop9/NxfOTHFI6Ygm+leRfSkdssqaqj810SEyyf5J3tH33rrbvrl86ZpW0fbd323dtkhOS3Kp0z0Ac01T1m0pHAAAAAMCyGXcCAADAcB3d9t0r277bt3TIKmr77mFJnlG6Y0k+0FT1RaUjyJOSfLV0xIAcmuRzbd/97uwUXS5F23d3TXJipp+3/PuaOjvJE0pHAAAAAEAJxp0AAAAwQG3fXTvJrTMdtfxH23ePaPvO/46/nNq++9UkR5TuWKL3lQ4gaar6u0kemcTQdoerJfnrJP/S9t09SscMUdt3N2777p1JPpjkpqV7BuYJTVV/rXQEAAAAAJTgm0IAAAAwTHe/2D8fkOQNmY6jDi3UszJmp9+9K8lepVuW5AdJjikdwVRT1ccneUnpjgE6OMkH2r47uu27W5SOGYK2764xewT7vye5f+meAXpDU9VvKR0BAAAAAKUYdwIAAMAwXdIJd7dK8q627z45O5mSn9L23f2THJvkyqVblujo2YmRDMczk5xUOmKgfj3JZ9u+e8umjjxno87nJDkl00ewX6lo0DB9OcmTSkcAAAAAQEl7lg4AAAAALtE9L+W/u12SY9u+65O8OMlbmqr+4XKyhqntuy1J/iDJC7J5/2fWt5UO4Cc1Vf2Dtu8enuRTMdy7JFuSPCTJQ9q+e3eSFzRV/cnCTQvX9t31kjwxyZOTXL1wzpBdkORhTVV/r3QIAAAAAJS0ad/sAAAAgMGbnWZ33cvxS6skr09yStt3f9z23TUXWzZMbd/tm+TtSf4im/e1jvOSHFU6gv+uqeo+yVNLd6yA+yX5RNt3J7Z99/i27/YpHTRvbd8d0vbd2zI9qfNZMey8LH/SVPWnS0cAAAAAQGlO7gQAAIDhuftO/voDkzw/ybPbvntHktck+aemqi+ae9nAtH33v5K8MpdvDLuOjm6q+pzSEVyypqpf2fbdIZmeUsmlq5K8KsmLZkPItyX5YFPV55fN2jVt390syUOT/EaSXyics0qOTfLC0hEAAAAAMATGnQAAADA8l/ZI9ktzpSQPm11fbvvub5Mc0VT1aXMrG4i2734+SZvksNIthf196QAu0+OT3DoGfpfX1ZI8Znad2fbdu5K8J8nxTVV/t2jZpWj7bo8kk0w/fz84yS3LFq2kU5Mc3lT1haVDAAAAAGAIjDsBAABgQNq+u2KSQ+bwUjfJdPz4vLbv3p/kTUneu+qnPLZ9d5Mkf5jksUn2KJxT2jeTHF06gkvXVPXZbd/dP8mnk6zdI8cXbL/sGHr+qO27Tyc5LslHk3ymqertpcJmn6urJLdNcrckd01yjVI9a+AHSR5Y8s8UAAAAAIbGuBMAAACG5Q5JrjLH19szyb1n13lt370vyVFJjm2q+htzfJ+FafturyT3SPLbmf4+tpQtGozXNlV9QekILltT1Z9r++7RSd5aumWF7ZHp58c7/Pgn2r47OclnkvRJvpTki0m+NM8TPmcjznGmg/mDktw8yW2S3CrJFef1PuTxTVWfUDoCAAAAAIbEuBMAAACGZVcfyX557J3k/rMrbd/1ST6c5GNJPj6kx7e3fXeVJHdM8oDZda2yRYNzUZK/LR3B5ddU9dvavvvzJM8s3bJGbjy7Hnjxn2z7bnuSbyX5TpJvJzk9yXeTnJfkwiRnX+yXXyXTkeaeSfZNsv/FruskOSDJFRb5myAvbar6DaUjAAAAAGBojDsBAABgWBY57vxp1ex6apK0fXdKkhMzPQWvT/IfSb7cVPUPFh3S9t2NkvxSpifi3TnJ7ZPstej3XWHvb6r6K6Uj2GnPSnLLJPctHbLmRrPr5qVDuEzHJvmD0hEAAAAAMETGnQAAADAQbd+NMh03lnKj2XXoxX7uorbvvp5kW5JvJPlmktMyPRHvzExPwDs70xPxzrmE19yS5OpJrpQdg6trJrlBpifu3SjTRx1ffc6/l3X3itIB7Lymqi9q++7wJB/NdMwMm+ykJA9pqvpHpUMAAAAAYIiMOwEAAGA47pbpGHJItiS5/uxiGD6f5KjSEeyapqrPafvuPkk+neS6pXugkNOS3Kep6rNLhwAAAADAUF2hdAAAAADwX5b5SHZW1182VX1h6Qh2XVPVX09y7yTfK90CBXwvya83Vf2V0iEAAAAAMGTGnQAAADAc9ygdwOB9I8kbS0ew+5qqPjHJA5KcX7oFluj8JA9sqvpfSocAAAAAwNB5LDsAAAAMQNt3P5/k50p3MHgvbar6h6UjmI+mqo9r++4RSd6cZEvpHliwC5M8oqnqD5QOAWD4tmxxawQAAODkTgAAABgGj2TnspyR5BWlI5ivpqr/Mcnvlu6AJfid2d93AAAAAOByMO4EAACAYTDu5LI8v6nqc0pHMH9NVb8iSVO6AxboGU1Vv6p0BAAAAACsEuNOAAAAKKztuz2THFK6g0E7Ncn/LR3B4jRV/YIkf1a6Axagaar6haUjAAAAAGDVGHcCAABAebdLsm/pCAbt2U1V/7B0BIvVVPWzkhjBsU6a2XAZAAAAANhJxp0AAABQnkeyc2lOSvLG0hEsR1PVz4iBJ+vBsBMAAAAAdoNxJwAAAJR399IBDNpTmqq+sHQEyzMbeD6zdAfshqcadgIAAADA7jHuBAAAgILavrt6po9lh0vytqaqP1Q6guVrqrpN8tTSHbCTLkzymKaqX1Y6BAAAAABWnXEnAAAAlHXXJHuUjmCQzk7ytNIRlDMbyD06yQWlW+By+EGSw5qq/rvSIQAAAACwDow7AQAAoKx7lA5gsJ7eVPXXS0dQVlPVRyS5X5JzC6fApTkzyT2aqj6ydAgAAAAArAvjTgAAACjLuJNL8qEkrykdwTA0VX1Mkrsk+U7pFrgEpyT55aaqP1o6BAAAAADWiXEnAAAAFNL23Y2THFS6g8E5M8kjm6q+qHQIw9FU9aeS3C7J50u3wMV8Isntm6r29xIAAAAA5sy4EwAAAMpxaieX5PEex84laar65CR3SHJc6RZI8g9J7tpU9bdKhwAAAADAOjLuBAAAgHKMO/lpf9NU9dtLRzBcTVWfleReSV5euoWNdWGSP0ry8KaqzysdAwAAAADras/SAQAAALCJ2r7bI8ndSncwKJ9O8vulIxi+pqp/lOQpbd/9S5JXJNm7cBKbY3uSBzdV/cHSIQAAAACw7pzcCQAAAGXcJsl+pSMYjG8mObSp6h+WDmF1NFV9RJJfSXJK2RI2xAlJasNOAAAAAFgO404AAAAo456lAxiMc5Pcr6nqb5YOYfU0Vd1lOhY/qnQLa+1lSe7YVPVXSocAAAAAwKYw7gQAAIAy7lE6gEG4MMlDm6o+oXQIq6up6u1J7pvkaUnOL5zDejk9yX2bqn6qk4UBAAAAYLmMOwEAAGDJ2r67apI7lO5gEH67qer3lI5g9TVVfVFT1S9NcvskXyjdw1r4QJJbNVX93tIhAAAAALCJjDsBAABg+Q5JslfpCIp7elPVry4dwXqZPab91kleWbqFlXVukicnuVdT1d8sHQMAAAAAm2rP0gEAAACwgTySnaap6heVjmA9NVX9n0l+u+279yZ5TZLrFk5idXwsyWOaqv5i6RAAAAAA2HRO7gQAAIDlM+7cbE1T1S8oHcH6a6r6mCS3SPK60i0M3jlJfi/JnQ07AQAAAGAYnNwJAAAAS9T23Q2S3Lx0B0VcmOSJTVW/pnQIm6Op6rOSPLbtuzdn+qj2mxROYniOTvI7TVWfWjoEAAAAANjByZ0AAACwXHcvHUAR5yV5kGEnpTRVfVySg5O0Sc4vnMMwnJrkAU1V38ewEwAAAACGx7gTAAAAlssj2TfPt5Ic0lT1O0uHsNmaqj63qepnJrllkmNK91DMeUn+LMnNm6p+V+kYAAAAAOCSeSw7AAAALEnbd1eIceem+UymJ+M5FY/BaKr6C0nu3fbdryV5aZJfKJzEclyU5I1JntlU9ddKxwAAAAAAl87JnQAAALA8VZL9S0ewNK9LckfDToaqqer3Zfqo9qcnObtwDov1kSS3bar6kYadAAAAALAanNwJAAAAy3NWpic53qZ0CAt1TpLfbar6DaVD4LI0Vf3DJC9q++6IJH+c5IlJ9i4axTz9e6YndR5ZOgQAAAAA2DlO7gQAAIAlaar65CR3SPJ/klxQOIfFOCHJrQ07WTVNVZ/eVPXTkhyU5FVJzi+cxO759yS/keSWhp0AAAAAsJqMOwEAAGCJmqo+v6nq5ySZJPlU4Rzm54dJnpXkl5uq/lLpGNhVTVV/vanqJyb5xSRvSHJR4SR2zsVHnW9pqvrC0kEAAAAAwK4x7gQAAIACmqruk/xykickObNwDrvnY5me1vlnTVU7kZW10FT1l5qq/s0kt0jy+jjJc+i6GHUCAAAAwFrZs3QAAAAAbKrZ+ObVbd8dmeQ5SR6fZI+iUeyM7yT5oyRHNFXtdEPWUlPV/57kUW3f/UmSpyX5rSRXLVvFxbwvyV81Vf3B0iEAAAAAwHwZdwIAAEBhTVV/O8nvtH338iQvSnLvwklcuvOTvCzJ85uq/m7pGFiGpqpPTfK0tu/+NMljkjw5ybhs1cY6O8kRSf6mqeovFG4BAAAAABbEuBMAAAAGoqnqzye5T9t3h2R6kuediwbx0y5K8sYkf9pU9cmlY6CEpqrPTvLS2Rj97kmekOS+8XXGZfhkkr9N8pamqr9fOgYAAAAAWCxfdAUAAICBaar6+CSHzEaez05y16JBXJTkrUme21T150rHwBA0VX1hkg8k+UDbdwckeViSRyapioatn68l+Yckr/f5BwAAAAA2i3EnAAAADNRs5Hl823d1kv+d5CFJ9igatVnOzfSkzr9oqvpLpWNgqJqqPi3Ji5O8uO27W2b6uepBSW5aNGx1fTvJu5K8OclHZ0NaAAAAAGDDGHcCAADAwDVV3SU5vO27ZyR5fJLHJblO2aq1ti3Ja5K8pqnqM0rHwCppqvqkJCcleXbbdwcnOSzJ/0pSFw0bvi8lOTrJO5J83KATAAAAADDuBAAAgBXRVPVXMx1MPTfJfZP8VpJ7JrlC0bD18P0kRyZ5XZIPN1V9UeEeWHlNVX82yWeTPKftuwOT/HqSu8+u/Uu2DcD3kxyf5LgkRzdV/cWyOQAAAADA0Bh3AgAAwIppqvr8TE93e0fbd9dJ8tAkhye5bdGw1fP9JO9P8tYk72mq+tzCPbC2mqr+ZpLXJnlt23dbklRJ7pTkjkn+Z5IDCuYtw5lJPpHkY0k+kuRTTVVfUDYJAAAAABgy404AAABYYU1VfyvJy5K8rO27GyY5dHbdKckeJdsGalumg86jknyoqerzCvfAxpmdjHvi7Hp5ksw+f912dtVJbpXkOqUad9N3M300/WeSfHr24384ERgAAAAA2BnGnQAAALAmmqo+NdOh1MvbvtsvyV0yfWz7PZKMS7YVdHJ2nJT3waaqTy7cA1yC2eevUzM9lThJ0vbd/kkOTnKzJL+Q5KAkP5/khkmuXCDz4s7NdCx+8sV+/EKSk2a/F2AYXpHkiNIRc3R+6QAAAABgeYw7AQAAYA01VX1mknfOrh+fivcrmT4C+Q6Znoq3bid7npakz/SUvE8l2dpU9TfKJgG7qqnq05N8eHb9hLbvrpXpyPOAJNdNcq0k106y3+y6RpJ9Z798nyR7Zfq10KvOfm5LkouSXJDknNnPnTP7z+clOT3Jd2Y/njG7Ts/088zJTVWfNr/fKbAoTVX/IMkPSncAAAAA7ArjTgAAANgAFzsV781J0vbdlTI9Ee/WSaokt0hy0yQHlmq8nH6Q5GtJ/iPJlzI9Ke/fkny2qeozSoYBy9NU9XcyHV8CAAAAAKwl404AAADYQLOTrLbOrv/S9t2+mT72+MaZnop3g9l1YJJrJtl/9uM8fS/Jd5OcdbHr9ExHnF9P8tXZj1+fDboAAAAAAADWmnEnAAAA8F+aqj4708eaf+Zn/Zq27378aOOrZ/q4zmg8RwAAIABJREFU4x9fP3a1TB/5ftbFfu7HjztOpo88Pi/J2UnOaqr6wnn1AwAAAAAArAPjTgAAAGCnNFV9QXacsAkAAAAAAMCcXaF0AAAAAAAAAAAAAAA7GHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCAGHcCAAAAAAAAAAAADIhxJwAAAAAAAAAAAMCA7Fk6AChrNJ7cN8lzS3ewEj68fdvWp5WOAAAAAAAAAACAdWfcCYySVKUjWAmnlA4AAAAAAAAAAIBN4LHsAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAAAANi3AkAAAAAAAAAAAAwIMadAAAAAAAAAAAA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7tWZHRE71q83pX1QhRzmMPTdNzMb8Dx76lrWqyntLyW588iY44a++2GNehbF0HfnZ/xupLdqSnvrCuXAltHbAgAArA7DnQAAALAFmtKWJL88dR1z+E6Suw1995mpC9lsQ9+9LclNkxw9dS0jnZ7k9zMbAjx56mKmMPTd+UPfPTXJPbMaQw2nJTl46LvfHvrux1MXw8V6bJKfVMh5flPafSrkMIeh796b2RHty+LwChlHVchYREdl/O6Fdu9kKeltAQAAlp/hTgAAANgay3gk++eT/NrQdydNXchWGfru1KHvDk1yQJJl/LqPTXLjoe9eOPTdeVMXM7Wh796e5OZJjpy6lhFen+SmQ98dO3UhXLKh776Q5FkVoq6V5MkVcpjT0HcvSPKSqeu4JE1pd09y6MiYLyc5cXQxC2jou68kecfImIOb0u5Vox7YanpbAACA5Wa4EwAAALbGl5J8b+oiNuB1SW67Nqi07Qx9d2KSWyd5TJJvTFzOepyY5FeHvjt46LtTpi5mkQx9972h7w5LcpckH526ng34XJL7D333G57TpfOsJF+skPMnTWlvXCGH+f2PJB+fuohLcL8kVxmZcfTaEear6sUj1++X5KAahcBU9LYAAADLyXAnAAAAbIGh705IcuMkL526lktwepIjhr47cOi7U6cuZkpD350z9N2Lklw/yeOSfG3iknbm7UnuOvTdAUPfvX/qYhbZ0HfvTtImeVSSz05czsX5cmZHAN907fcGS2boux9ndnzsWHskeWGFHOY09N2ZSR6U5PtT13IxjqiQsexHNl+S1yY5bWSGo9lZenpbAACA5WO4EwAAALbI0HffGfrukCT7J3nr1PVcyLlJ/iXJLw19969TF7NIhr47c+i752d2I/yQJO+ZuKTTk/xrklsMfXfPoe/eNXE9S2Pou/OGvntJkpskeXCS/5i4pAs6MclvJrnB0HdHDn13ztQFMb+h796c5LgKUXdtSvvwCjnMaei7PskjkizcccBNaa+e5D4jY04c+u5LNepZVGsD1y8fGXPXprSlRj0wNb0tAADA8th96gIAAABguxn67iNJ7t2U9rZJ/iDJQzPboW0KZ2a2m+hztusR7Os19N1ZmX2vXtqU9kZJHpLZgODNt+DyZyZ5c5LXJHnN0HdnbME1V9bQd+clOT7J8WvDOg9PcmBmO3tulfOTdElel+TY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}



% Custom title page
\renewcommand{\@maketitle}{\bgroup\setlength{\parindent}{0pt}\begin{flushright}
{%
\vskip76pt%
{\raggedleft \titlefont \@title\par}%
\vskip11pt
{\raggedleft \@author\par}
\vskip51pt%
}%
\end{flushright}\egroup
{%
{\color{watermarkcolor}\rule{\linewidth}{0.5pt}}
\vskip12pt%
\abscontent
}%
\vskip25pt%
}%

% Other packages
\RequirePackage{enumitem} % For reducing bullet list item separation

\RequirePackage{tabularx}

\RequirePackage[flushmargin,ragged]{footmisc}

\newlength{\myFootnoteWidth}%
\newlength{\myFootnoteLabel}%
\setlength{\myFootnoteLabel}{0.5em}
\renewcommand{\@makefntext}[1]{%
  \setlength{\myFootnoteWidth}{\columnwidth}%
  \addtolength{\myFootnoteWidth}{-\myFootnoteLabel}%
  \noindent\makebox[\myFootnoteLabel][r]{\@makefnmark\ }%
  \parbox[t]{\myFootnoteWidth}{#1}
  }

% Commands to set the footnote for the front page.
\renewcommand{\footnoterule}{%
  \kern -3pt
  {\color{watermarkcolor} \hrule width \columnwidth height 0.5pt}
  \kern 2.5pt
}

\newcommand{\@authfootnote}[2]{%
  \begingroup
  \setlength{\myFootnoteLabel}{0em}
  \renewcommand\thefootnote{}\footnote{\footnotelayout\copyrightfont\textsuperscript{#1} #2}%
   \endgroup%
}

\newcommand\blfootnote[1]{%
  \@authfootnote{}{#1}%
%   \begingroup
%   \setlength{\myFootnoteLabel}{0em}
%   \renewcommand\thefootnote{}\footnote{#1}%
% NEW: uncommented so that footnotes start at 1 and not at 2.
   \addtocounter{footnote}{-1}%
%   \addtocounter{Hfootnote}{-1}%
%   \endgroup%
}

\newcommand\correspondingauthoraffiliation[2]{%
  \@authfootnote{#1}{#2}%
  \ifthenelse{\boolean{displaylineno}}{\par\linenumbers}{}
}


\newcommand\jot@copyright{%
\ifthenelse{\equal{\jot@license}{ccby}}{Licensed under Attribution 4.0 International (CC BY 4.0)}{}\ifthenelse{\equal{\jot@license}{ccbynd}}{Licensed under Attribution - No Derivatives 4.0 International (CC BY-ND 4.0)}{}\ifthenelse{\equal{\jot@license}{ccbyncnd}}{Li\-cen\-sed un\-der At\-tri\-bu\-tion - Non\-Com\-mer\-cial - No De\-ri\-va\-ti\-ves 4.0 In\-ter\-na\-tio\-nal (CC BY-NC-ND 4.0)}{}}
% choose from ccby, ccbynd, ccbyncnd

\RequirePackage{listofitems}
\newcommand\substr[3]{%
  \setsepchar{#2}%
  \readlist\parsedinput{#1}%
  \foreachitem\x\in\parsedinput{%
    \ifnum\xcnt=1\else#3\fi\x%
  }%
}


%%%%

\newcommand{\jot@cite}{\textbf{JOT reference format:\\ }\expandafter\let\csname textsuperscript \endcsname\@gobble
\let\Authfont\relax\AB@authlist. \textit{\substr{\thetitle}{\\}{:}}. {Journal of Object Technology}. Vol. \jot@volume, No. \jot@number, \jot@year. 
\jot@copyright\ \href{http://dx.doi.org/\jot@doijournalprefix/jot.\jot@year.\jot@volume.\jot@number.\jot@articleno}{http://dx.doi.org/\jot@doijournalprefix/jot.\jot@year.\jot@volume.\jot@number.\jot@articleno}}


\newcommand{\firstpagefootnote}{\blfootnote{\footnotesize%
\\[-3mm]{}%
\jot@cite}}

\newenvironment{tableminipage}[1]{\begin{minipage}{#1}\renewcommand\footnoterule{ \kern -1ex}%
\setlength{\myFootnoteLabel}{0.5em}%
}{\end{minipage}}

% Package to enable absolute positioning of figures
\RequirePackage[absolute,overlay]{textpos}
\setlength{\TPHorizModule}{1mm}
\setlength{\TPVertModule}{1mm}
\textblockorigin{0mm}{0mm} % start everything near the top-left corner

% List style redefinition

\renewcommand\labelitemi{\textendash}
\renewcommand\labelitemii{-}
\renewcommand\labelitemiii{\textperiodcentered}



% Acknowledgment
\newcommand{\jot@ack}{}
\newcommand{\acknowledgements}[1]{\renewcommand{\jot@ack}{\subsection*{Acknowledgments} #1}}
\newcommand{\acknowledgement}[1]{\renewcommand{\jot@ack}{\subsection*{Acknowledgments} #1}}
\newcommand{\acknowledgment}[1]{\renewcommand{\jot@ack}{\subsection*{Acknowledgments} #1}}
\newcommand{\acknowledgments}[1]{\renewcommand{\jot@ack}{\subsection*{Acknowledgments} #1}}

\let\jot@bib\bibliography
\let\bibliography\relax
\newcommand{\bibliography}[1]{\jot@ack\jot@bib{#1}}

% Short Bio command
\newcommand{\shortbio}[2]{\paragraph{#1}\hskip-8.5pt #2\smallskip}

% AUTHOR EMAIL + HOMEPAGE

\newcommand{\authorcontact}[2][]{You can contact the author at \href{mailto:#2?subject=Your paper "\@title"}{#2}\ifthenelse{\equal{#1}{}{}}{}{ or visit \url{#1}}.}

%\newcommand{\editorcontact}[2][]{You can contact them at \href{mailto:#2?subject=Your paper "\@title"}{#2}\ifthenelse{\equal{#1}{}{}}{}{ or visit \url{#1}}.}

\newcommand{\editorcontact}[2][]{You can contact the editor at \href{mailto:#2?subject=Your paper "\@title"}{#2}\ifthenelse{\equal{#1}{}{}}{}{ or visit \url{#1}}.}

\newcommand{\email}[1]{\href{mailto:#1}{#1}}

%\renewcommand{\url}[1]{\href{#1}{#1}}


% Listings

\RequirePackage{listings}

\definecolor{codegreen}{rgb}{0,0.6,0}
\definecolor{codegray}{rgb}{0.5,0.5,0.5}
\definecolor{codepurple}{rgb}{0.58,0,0.82}
\definecolor{backcolour}{rgb}{0.95,0.95,0.92}

%Code listing style named "mystyle"
\lstdefinestyle{jot}{
  backgroundcolor=\color{backcolour},   
  commentstyle=\color{codegreen},
  keywordstyle=\color{magenta},
  numberstyle=\tiny\color{codegray},
  stringstyle=\color{codepurple},
  basicstyle=\listing@font\footnotesize,
  breakatwhitespace=false,         
  breaklines=true,                 
  captionpos=b,                    
  keepspaces=true,                 
  numbers=left,                    
  numbersep=6pt,                  
  showspaces=false,                
  showstringspaces=false,
  showtabs=flase,                  
  tabsize=2
}

%"mystyle" code listing set
\lstset{style=jot}

\newcommand{\pdfinlimg}[5]{
\makebox[#1cm][l]{\immediate\pdfliteral{
  q
  #3 0 0 #4 0 0 cm
  #1 0 0 #2 0 0 cm
  0.885 0 0 0.885 0 0 cm 
  BI
  /W #3
  /H #4
  /CS /RGB
  /BPC 8
  /F [ /AHx /Fl ]
  ID
  #5>
  EI
  Q
}\vbox to #2cm{}}
}

