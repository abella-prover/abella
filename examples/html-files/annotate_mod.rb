
file = File.open(ARGV[0]).read
regex = /%.*?\n/
file.gsub!(regex) do |match|
  "<span class=\"comment\">#{match}</span>"
end
print file

