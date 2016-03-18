
url = 'http://bourse.lesechos.fr/telechargements/DownloadHisto-20091101-20091114-20091114_105520.txt'
page = urllib.urlopen(url)
texte = page.read()
