# This does not handle nesting of comments or interactions between
# different styles of comments.

file = File.open(ARGV[0]).read

file.gsub!(/\/\*.*?\*\//m) do |match|
  "<span class=\"comment\">#{match}</span>"
end

file.gsub!(/%.*?\n/) do |match|
  "<span class=\"comment\">#{match.chop}</span>\n"
end

file.gsub!(/accum_sig ([^.]*)\./,
           'accum_sig \1. <a class="view" href="\1.sig">[View \1.sig]</a>')

file.gsub!(/accumulate ([^.]*)\./,
           'accumulate \1. <a class="view" href="\1.mod">[View \1.mod]</a>')

print file
