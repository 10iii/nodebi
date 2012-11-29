<?php
function microtime_float()
{
	list($usec, $sec) = explode(" ", microtime());
	return ((float)$usec + (float)$sec);
}
echo "\n";
echo $argv[1]."\n";
$start = microtime_float();
shell_exec($argv[1]);
echo "time cost:" . (microtime_float()-$start)."\n";
?>
