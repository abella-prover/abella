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
      "\n<div class=\"proof\">"
    when :proof_end
      "</div>"
    when :pre_start
      "\n<pre>"
    when :pre_end
      "</pre>\n"
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
    text =~ /^%=+ (.*?) *=*$/
    super($1, :heading)
  end

  def to_s
    "\n<h2>#{@text}</h2>\n"
  end
end

class HTMLComment < Element
  def initialize(text)
    text =~ /\/\*@(.*)\*\//m
    super($1, :html_comment)
  end

  def to_s
    coded = @text.gsub(/`([^`]*)`/, '<code>\1</code>')
    "<p class='body'>\n#{coded}\n</p>"
  end
end

def convert(string)
  regex = /(\/\*.*?\*\/|%.*?\n|(?:Theorem|CoDefine|Define|Import|Specification|Type|Kind|Close|Split|Query|Set|Show|(?:(?:[A-Za-z_][A-Za-z_0-9]* *: *)?(?:induction|coinduction|apply|cut|inst|case|assert))|backchain|monotone|permute|exists|witness|clear|abbrev|unabbrev|search|split|split\*|unfold|intros|rename|skip|abort|undo)(?:"[^"]*"|[^%]|%.*?\n)*?\.)/m

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

def read_lp(name)
  file = File.open(name).read

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

  return file
end


def contents(elements)
  title = ""
  if (elements[0].tag == :comment) then
    first, *elements = *elements
    title = first.text.gsub(/^%* */, "")
  end

  title_comment = ""
  if (elements[0].tag == :pre_end &&
      elements[1].tag == :html_comment &&
      elements[2].tag == :pre_start) then
    pre_end, title_comment, pre_start, *elements = *elements
  end

  while (elements[0].tag == :whitespace) do
    first, *elements = *elements
  end

  name = ARGV[0]

  specification_section = ""
  elements.each do |e|
    if e.text =~ /^Specification "(.*)"/ then
      specification_section = <<-eos
<div class="section" id="specification">
<h1>Executable Specification</h1>

<a class="view" href="#{$1}.sig">[View #{$1}.sig]</a>
<a class="view" href="#{$1}.mod">[View #{$1}.mod]</a>
<pre class="command">
#{read_lp($1 + ".sig")}
</pre>
<pre class="command">
#{read_lp($1 + ".mod")}
</pre>

</div>
        eos
      break
    end
  end

  <<-eos
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
        "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" lang="en" xml:lang="en">
<head>
<title>Abella: #{title}</title>
<link href="http://abella-prover.org/style.css" rel="stylesheet" type="text/css" />
<link rel="icon" href="http://abella-prover.org/images/favicon.ico" type="image/x-icon" />
<link rel="shortcut icon" href="http://abella-prover.org/images/favicon.ico"
        type="image/x-icon" />
<script src="http://abella-prover.org/jquery.js"></script>
<script type="text/javascript">
$(function() {
  $('.proof').hide();

  $('<span> </span><a class="fold-link" href="#">[Show Proof]</a>')
    .insertAfter($('.proof').prev())
    .toggle(function() {
      $(this).next().show('fast');
      $(this).text('[Hide Proof]');
    }, function() {
      $(this).next().hide('slow');
      $(this).text('[Show Proof]');
    });

  $('<span> </span><a class="fold-link" href="#">[Show All Proofs]</a>')
    .insertBefore($('#reasoning #menubar'))
    .click(function() {
      $('.proof:hidden').prev().click();
      return false;
  });

  $('<span> </span><a class="fold-link" href="#">[Hide All Proofs]</a>')
    .insertBefore($('#reasoning #menubar'))
    .click(function() {
      $('.proof:visible').prev().click();
      return false;
  });
});
</script>
</head>

<body>

<div id="logo-small">
<a href="http://abella-prover.org/index.html">
<img src="http://abella-prover.org/images/logo-small.png"/>
</a>
</div>

<div class="section">
<h1>#{title}</h1>
#{title_comment}
</div>

#{specification_section}

<div class="section" id="reasoning">
<h1>Reasoning</h1>
<a class="view" href="#{name}">[View #{name}]</a>
<span id="menubar" />
<p class="body">
Click on a command or tactic to see a detailed view of its use.
</p>
<pre>
#{elements.join('')}
</pre>
</div>

</body>
</html>
eos
end

file_contents = File.open(ARGV[0]).read
elements = convert(file_contents)
elements = mark_proofs(elements)
elements = slide_proof_ends(elements)
elements = remove_div_newlines(elements)
elements = remove_empty_pre(elements)
elements = remove_initial_pre_space(elements)
elements = remove_final_pre_space(elements)
print contents(elements)
