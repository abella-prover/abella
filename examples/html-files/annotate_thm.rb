# This does not handle nesting of comments or interactions between
# different styles of comments.

$details = ARGV[0].chomp(".thm")  + "-details.html"

class Element
  attr_accessor :text, :ref, :tag
  @@input_count = 0
  @@proof_count = 0

  def initialize(text, tag)
    @text = text
    @tag = tag

    if tag == :tactic || tag == :theorem ||
       tag == :command || tag == :import then
      @ref = (@@input_count += 1)
    elsif tag == :proof_start
      @ref = (@@proof_count += 1)
    end
  end

  def to_s
    case @tag
    when :whitespace
      @text
    when :comment
      "<span class=\"comment\">#{@text}</span>"
    when :proof_start
      " " +
      "<a class=\"fold-link\" id=\"proof#{@ref}-show\"" +
      " href=\"javascript:toggle('proof#{@ref}', true);\">[Show Proof]</a>" +
      "<a class=\"folded\" id=\"proof#{@ref}-hide\"" +
      " href=\"javascript:toggle('proof#{@ref}', false);\">[Hide Proof]</a>" +
      "<span class=\"folded\" id=\"proof#{@ref}\">"
    when :proof_end
      "</span>"
    else
      type = (tag == :tactic ? "tactic" : "command")
      @text.gsub!(/(%.*)/, '<span class="comment">\1</span>')
      "<a href=\"#{$details}##{@ref}\" class=\"#{type}\">#{@text}</a>" +
      if tag == :import then
        @text =~ /\"(.*)\"/
        " <a class=\"import-link\" href=\"#{$1}.html\">[View #{$1}]</a>"
      else
        ""
      end
    end
  end
end

def convert(string)
  regex = /(\/\*.*?\*\/|%.*?\n|(?:Theorem|CoDefine|Define|Import|Specification|coinduction|induction|apply|cut|inst|monotone|case|assert|exists|clear|abbrev|unabbrev|search|split|split\*|unfold|intros|skip|abort|undo)(?:[^%]|%.*?\n)*?\.)/m

  string.split(regex).map do |s|
    case s
    when /\A\s*\Z/m
      # \A and \Z correspond to ^ and $ for multiline regex matching
      Element.new(s, :whitespace)
    when /^%/
      Element.new(s, :comment)
    when /^\/\*/
      Element.new(s, :comment)
    when /^Theorem/
      Element.new(s, :theorem)
    when /^(Define|CoDefine|Set|Specification)/
      Element.new(s, :command)
    when /^Import/
      Element.new(s, :import)
    else
      Element.new(s, :tactic)
    end
  end
end

def mark_proofs(array)
  result = []
  possible_end = nil

  array.each do |e|
    result << e

    if e.tag == :theorem then
      result << Element.new("", :proof_start)
      possible_end = nil
    elsif e.tag == :tactic then
      # The old possible end was not really the end of the proof
      possible_end.tag = :whitespace if possible_end

      # Maybe this is the end of the proof
      possible_end = Element.new("", :proof_end)
      result << possible_end
    end
  end

  result
end

file_contents = File.open(ARGV[0]).read
elements = convert(file_contents)
elements = mark_proofs(elements)
print elements.join('')
