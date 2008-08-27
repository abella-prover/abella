
file = File.open(ARGV[0]).read
regex = /%.*?\n/
file.gsub!(regex) do |match|
  "<span class=\"comment\">#{match.chop}</span>\n"
end
print file

