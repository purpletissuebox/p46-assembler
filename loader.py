import draftsman.blueprintable

data = [457179136, 0, 436207616, 457179136, 0, 356515840, 0, 454033408, 20971520, 268435456, 17825792, 570425344, 526385152, 0, 436207616, 0, 454033408, 454033408, 436207616, 454033408, 15728640, 335544320, 13631488, 436207616, 13631488, 268435456, 13631488, 570425344, 513802240, 0, 436207616, 0]

def get_good_signals(banned):
	banned_signals = draftsman.data.signals.pure_virtual + banned
	signal_list_p = draftsman.data.signals.item + draftsman.data.signals.fluid + draftsman.data.signals.virtual
	for vsig in banned_signals:
		signal_list_p.remove(vsig)
	return signal_list_p

def create_combinator(signal_lib, values, starting_sig, idx):
	comb = draftsman.entity.ConstantCombinator()
	n = len(values) - idx
	if n > 20:
		n = 20
	
	for i in range(n):
		comb.set_signal(i, signal_lib[starting_sig + i], values[idx + i])
	return comb

def create_bank(host_bp, signal_lib, values, idx, ypos):
	n = (len(values) - idx + 19)//20
	off = 0
	for i in range(n):
		cur_comb = create_combinator(signal_lib, values, off, idx + off)
		cur_comb.tile_position = [i, ypos]
		host_bp.entities.append(cur_comb)
		if i != 0:
			host_bp.add_circuit_connection("red", i-1, i)
		off += 20

def create_array(host_bp, signal_lib, values):
	i = 0
	y = 0
	while i < len(values):
		create_bank(host_bp, signal_lib, values, i, y)
		y += 1
		i += 256

def main():
	bp = draftsman.blueprintable.Blueprint()
	signal_list = get_good_signals([])
	create_array(bp, signal_list, data)
	print(bp.to_string())

main()