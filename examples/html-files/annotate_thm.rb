count = 0

details = ARGV[0].chomp(".thm")  + "-details.html"
file = File.open(ARGV[0]).read
regex = /%.*?\n|(Theorem|Axiom|Def|induction|apply|cut|inst|case|assert|exists|clear|search|split|split\*|unfold|intros|skip|abort|undo).*?\./m
file.gsub!(regex) do |match|
  if match =~ /^%/ then
    match
  else
    "<a href=\"#{details}##{count += 1}\">#{match}</a>"
  end
end
print file

