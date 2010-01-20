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
  regex = /(\/\*.*?\*\/|%.*?\n|(?:Theorem|CoDefine|Define|Import|Specification|Type|Kind|Split|Query|Set|coinduction|induction|apply|backchain|cut|inst|monotone|permute|case|assert|exists|clear|abbrev|unabbrev|search|split|split\*|unfold|intros|skip|abort|undo)(?:[^%]|%.*?\n)*?\.)/m

  list = string.split(regex).map do |s|
    case s
    when /\A\s*\Z/m
      # \A and \Z correspond to ^ and $ for multiline regex matching
      [Element.new(s, :whitespace)]
    when /^%/
      [Element.new(s.chop, :comment), Element.new("\n", :whitespace)]
    when /^\/\*/
      [Element.new(s, :comment)]
    when /^Theorem/
      [Element.new(s, :theorem)]
    when /^(Define|CoDefine|Set|Query|Specification|Type|Kind|Split)/
      [Element.new(s, :command)]
    when /^Import/
      [Element.new(s, :import)]
    else
      [Element.new(s, :tactic)]
    end
  end

  list.flatten
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

# Slide the end of proofs over comments and non-newline whitespace
def slide_proof_ends(array)
  result = []
  sliding = nil

  array.each do |e|
    if sliding then
      if e.tag == :comment then
        result << e
      elsif e.tag == :whitespace && !(e.text.include? "\n") then
        result << e
      else
        result << sliding
        sliding = nil
        result << e
      end
    elsif
      if e.tag == :proof_end then
        sliding = e
      elsif
        result << e
      end
    end
  end

  result << sliding if sliding
  result
end

file_contents = File.open(ARGV[0]).read
elements = convert(file_contents)
elements = mark_proofs(elements)
elements = slide_proof_ends(elements)
print elements.join('')
