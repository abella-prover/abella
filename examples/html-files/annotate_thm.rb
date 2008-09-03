$details = ARGV[0].chomp(".thm")  + "-details.html"

class Element
  attr_accessor :text, :ref, :tag
  @@count = 0

  def initialize(text, tag, counted)
    @text = text
    @tag = tag
    @ref = (@@count += 1) if counted
  end

  def to_s
    case @tag
    when :whitespace
      @text
    when :comment
      "<span class=\"comment\">#{@text}</span>"
    else
      type = (tag == :tactic ? "tactic" : "command")
      "<a href=\"#{$details}##{@ref}\" class=\"#{type}\">#{@text}</a>"
    end
  end
end

def convert(string)
  regex = /(%.*?\n|(?:Theorem|CoDefine|Define|coinduction|induction|apply|cut|inst|case|assert|exists|clear|search|split|split\*|unfold|intros|skip|abort|undo).*?\.)/m
  
  string.split(regex).map do |s|
    case s
    when /^\s*$/m
      Element.new(s, :whitespace, false)
    when /^%/
      Element.new(s, :comment, false)
    when /^Theorem/
      Element.new(s, :theorem, true)
    when /^(Define|CoDefine)/
      Element.new(s, :definition, true)
    else
      Element.new(s, :tactic, true)
    end
  end
end

file_contents = File.open(ARGV[0]).read
elements = convert(file_contents)
print elements.join('')
