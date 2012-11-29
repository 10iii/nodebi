var bi = require('./bi.js');

function main(n) {
	var 
		i = 1,
		s = "",
		d,
		$neg10 = bi(-10),
		$three = bi(3),
		$ten = bi(10),
		g = 1,
		$g,
		$z0 = bi(1),
		$z1 = bi(0),
		$z2 = bi(1),
		$digits = Array(10),
		$negdigits = Array(10),
		k = 0,
		$k,
		l = 2,
		$l,
		a;

	for (var j = 0; j < 10; ++j) {
		$digits[j] = bi(j);
		$negdigits[j] = $digits[j].multiply($neg10);
	}

	do {
		while ($z0.compareTo($z2) > 0 || 
					((d = $z0.multiply($three).add($z1).divide($z2).bnIntValue()) !=
					$z0.bnShiftLeft(2).add($z1).divide($z2).bnIntValue())) {
			$z1 = $z1.multiply($g = bi(g += 2));
			$z2 = $z2.multiply($g);
			$z1 = $z1.add($z0.multiply($l = bi(l += 4)));
			$z0 = $z0.multiply($k = bi(++k));
		}
		$z0 = $z0.multiply($ten);
		$z1 = $z1.multiply($ten);
		$z1 = $z1.add($z2.multiply($negdigits[d]));
		s += d;

		if (i % 10 == 0) {
			console.log(s + "\t:" + i);
			s = ""
		}
	} while (++i <= n)

	if ((i = n % 10) != 0) {
		s += Array(11 - i).join(' ')
	}
	if (s.length > 0) {
		console.log(s + "\t:" + n)
	}
}

main.call(this, 1 * process.argv[2]);

