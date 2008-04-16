count = 0

details = ARGV[0].chomp(".thm")  + "-details.html"
file = File.open(ARGV[0]).read
regex = /%.*?\n|(Theorem|CoDefine|Define|coinduction|induction|apply|cut|inst|case|assert|exists|clear|search|split|split\*|unfold|intros|skip|abort|undo).*?\./m
file.gsub!(regex) do |match|
  if match =~ /^%/ then
    match
  else
    type = (match =~ /^(Theorem|CoDefine|Define)/) ? "command" : "tactic"
    "<a href=\"#{details}##{count += 1}\" class=\"#{type}\">#{match}</a>"
  end
end
print file

