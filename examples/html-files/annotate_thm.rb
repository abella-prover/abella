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
    when :heading
      "</pre><h1>#{@text}</h1><pre>"
    when :proof_start
      "\n<div class=\"proof\">"
    when :proof_end
      "</div>"
    when :pre_start
      "<pre>"
    when :pre_end
      "</pre>"
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

class Heading < Element
  def initialize(text)
    text =~ /^%(=+) (.*) (=+) *$/
    @size = $1.length
    super($2, :heading)
  end

  def to_s
    "<h#{@size}>#{@text}</h#{@size}>"
  end
end

class HTMLComment < Element
  def initialize(text)
    text =~ /\/\*@(.*)\*\//m
    super($1, :html_comment)
  end

  def to_s
    coded = @text.gsub(/`([^`]*)`/, '<code>\1</code>')
    "<p class='body'>#{coded}</p>"
  end
end

def convert(string)
  regex = /(\/\*.*?\*\/|%.*?\n|(?:Theorem|CoDefine|Define|Import|Specification|Type|Kind|Close|Split|Query|Set|Show|coinduction|induction|apply|backchain|cut|inst|monotone|permute|case|assert|exists|clear|abbrev|unabbrev|search|split|split\*|unfold|intros|skip|abort|undo)(?:[^%]|%.*?\n)*?\.)/m

  list = string.split(regex).map do |s|
    case s
    when /\A\s*\Z/m
      # \A and \Z correspond to ^ and $ for multiline regex matching
      [Element.new(s, :whitespace)]
    when /^%=/
      [Element.new("", :pre_end),
       Heading.new(s),
       Element.new("", :pre_start)]
    when /^%/
      [Element.new(s.chop, :comment), Element.new("\n", :whitespace)]
    when /^\/\*@/
      [Element.new("", :pre_end),
       HTMLComment.new(s),
       Element.new("", :pre_start)]
    when /^\/\*/
      [Element.new(s, :comment)]
    when /^Theorem/
      [Element.new(s, :theorem)]
    when /^(Define|CoDefine|Set|Show|Query|Specification|Type|Kind|Split|Close)/
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

def remove_div_newlines(array)
  div = false
  array.each do |e|
    if e.tag == :proof_start || e.tag == :proof_end then
      div = true
    elsif div && e.tag == :whitespace then
      e.text.sub!(/^\n/,"")
      div = false
    end
  end
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

def remove_empty_pre(array)
  result = []
  maybe_empty_pre = []

  array.each do |e|
    if maybe_empty_pre.empty? then
      if e.tag == :pre_start then
        maybe_empty_pre = [e]
      else
        result << e
      end
    else
      if e.tag == :whitespace then
        maybe_empty_pre << e
      elsif e.tag == :pre_end then
        maybe_empty_pre = []
      else
        result += maybe_empty_pre
        result << e
        maybe_empty_pre = []
      end
    end
  end

  result
end

def remove_initial_pre_space(array)
  result = []
  initial = true

  array.each do |e|
    if initial then
      if e.tag != :whitespace then
        result << e
        initial = false
      end
    else
      if e.tag == :pre_start then
        initial = true
      end
      result << e
    end
  end

  result
end

def remove_final_pre_space(array)
  result = []
  maybe_final_space = []

  array.each do |e|
    if maybe_final_space.empty? then
      if e.tag == :whitespace then
        maybe_final_space << e
      else
        result << e
      end
    else
      if e.tag == :whitespace then
        maybe_final_space << e
      elsif e.tag == :pre_end then
        maybe_final_space = []
        result << e
      else
        result += maybe_final_space
        result << e
        maybe_final_space = []
      end
    end
  end

  result
end

file_contents = File.open(ARGV[0]).read
elements = convert(file_contents)
elements = mark_proofs(elements)
elements = slide_proof_ends(elements)
elements = remove_div_newlines(elements)
elements = remove_empty_pre(elements)
elements = remove_initial_pre_space(elements)
elements = remove_final_pre_space(elements)
print elements.join('')
