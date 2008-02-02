<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
        "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" lang="en" xml:lang="en">
<head>
<title>Abella: <? include 'title' ?></title>
<link href="../style.css" rel="stylesheet" type="text/css" />
<link rel="icon" href="../images/favicon.ico" type="image/x-icon">
<link rel="shortcut icon" href="../images/favicon.ico" type="image/x-icon">
</head>

<body>

<div id="logo-small"/>
<a href="../index.html">
<img src="../images/logo-small.png"/>
</a>
</div>

<div class="section" style="width: 80%">
<h1 class="title"><? include 'title' ?></h1>
</div>

<div class="section" style="width: 80%">
<h2 class="title">Specification (<? include 'name' ?>.mod)</h2>
<pre class="code">
<? include 'specification' ?>
</pre>
</div>

<div class="section" style="width: 80%">
<h2 class="title">Reasoning (<? include 'name' ?>.thm)</h2>
<p class="body">
Click on a command or tactic to see a detailed view of its use.
</p>
<pre class="code">
<? include 'reasoning' ?>
</pre>
</div>

</body>
</html>
