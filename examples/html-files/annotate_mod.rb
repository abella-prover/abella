# This does not handle nesting of comments or interactions between
# different styles of comments.

file = File.open(ARGV[0]).read

file.gsub!(/\/\*.*?\*\//m) do |match|
  "<span class=\"comment\">#{match}</span>"
end

file.gsub!(/%.*?\n/) do |match|
  "<span class=\"comment\">#{match.chop}</span>\n"
end

print file

