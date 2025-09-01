local bit32_band = bit32.band
	local bit32_bor = bit32.bor
	local bit32_bxor = bit32.bxor
	local bit32_lshift = bit32.lshift
	local bit32_rshift = bit32.rshift
	local bit32_lrotate = bit32.lrotate
	local bit32_rrotate = bit32.rrotate
	local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi, sha3_RC_lo, sha3_RC_hi = table.create(0), table.create(0), table.create(0), table.create(0), table.create(0), table.create(0)
	local sha2_H_ext256 = {
		[224] = table.create(0);
		[256] = sha2_H_hi;
	}

	local sha2_H_ext512_lo, sha2_H_ext512_hi = {
		[384] = table.create(0);
		[512] = sha2_H_lo;
	}, {
		[384] = table.create(0);
		[512] = sha2_H_hi;
	}

	local md5_K, md5_sha1_H = table.create(0), {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0}
	local md5_next_shift = {0, 0, 0, 0, 0, 0, 0, 0, 28, 25, 26, 27, 0, 0, 10, 9, 11, 12, 0, 15, 16, 17, 18, 0, 20, 22, 23, 21}
	local HEX64, XOR64A5, lanes_index_base
	local common_W = table.create(0)
	local K_lo_modulo, hi_factor, hi_factor_keccak = 4294967296, 0, 0
	local TWO_POW_NEG_56 = 2 ^ -56
	local TWO_POW_NEG_17 = 2 ^ -17
	local TWO_POW_2 = 2 ^ 2
	local TWO_POW_3 = 2 ^ 3
	local TWO_POW_4 = 2 ^ 4
	local TWO_POW_5 = 2 ^ 5
	local TWO_POW_6 = 2 ^ 6
	local TWO_POW_7 = 2 ^ 7
	local TWO_POW_8 = 2 ^ 8
	local TWO_POW_9 = 2 ^ 9
	local TWO_POW_10 = 2 ^ 10
	local TWO_POW_11 = 2 ^ 11
	local TWO_POW_12 = 2 ^ 12
	local TWO_POW_13 = 2 ^ 13
	local TWO_POW_14 = 2 ^ 14
	local TWO_POW_15 = 2 ^ 15
	local TWO_POW_16 = 2 ^ 16
	local TWO_POW_17 = 2 ^ 17
	local TWO_POW_18 = 2 ^ 18
	local TWO_POW_19 = 2 ^ 19
	local TWO_POW_20 = 2 ^ 20
	local TWO_POW_21 = 2 ^ 21
	local TWO_POW_22 = 2 ^ 22
	local TWO_POW_23 = 2 ^ 23
	local TWO_POW_24 = 2 ^ 24
	local TWO_POW_25 = 2 ^ 25
	local TWO_POW_26 = 2 ^ 26
	local TWO_POW_27 = 2 ^ 27
	local TWO_POW_28 = 2 ^ 28
	local TWO_POW_29 = 2 ^ 29
	local TWO_POW_30 = 2 ^ 30
	local TWO_POW_31 = 2 ^ 31
	local TWO_POW_32 = 2 ^ 32
	local TWO_POW_40 = 2 ^ 40
	local TWO56_POW_7 = 256 ^ 7
	local function sha256_feed_64(H, str, offs, size)
		local W, K = common_W, sha2_K_hi
		local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
		for pos = offs, offs + size - 1, 64 do
			for j = 1, 16 do
				pos = pos + 4
				local a, b, c, d = string.byte(str, pos - 3, pos)
				W[j] = ((a * 256 + b) * 256 + c) * 256 + d
			end

			for j = 17, 64 do
				local a, b = W[j - 15], W[j - 2]
				W[j] = bit32_bxor(bit32_rrotate(a, 7), bit32_lrotate(a, 14), bit32_rshift(a, 3)) + bit32_bxor(bit32_lrotate(b, 15), bit32_lrotate(b, 13), bit32_rshift(b, 10)) + W[j - 7] + W[j - 16]
			end

			local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
			for j = 1, 64 do
				local z = bit32_bxor(bit32_rrotate(e, 6), bit32_rrotate(e, 11), bit32_lrotate(e, 7)) + bit32_band(e, f) + bit32_band(-1 - e, g) + h + K[j] + W[j]
				h = g
				g = f
				f = e
				e = z + d
				d = c
				c = b
				b = a
				a = z + bit32_band(d, c) + bit32_band(a, bit32_bxor(d, c)) + bit32_bxor(bit32_rrotate(a, 2), bit32_rrotate(a, 13), bit32_lrotate(a, 10))
			end

			h1, h2, h3, h4 = (a + h1) % 4294967296, (b + h2) % 4294967296, (c + h3) % 4294967296, (d + h4) % 4294967296
			h5, h6, h7, h8 = (e + h5) % 4294967296, (f + h6) % 4294967296, (g + h7) % 4294967296, (h + h8) % 4294967296
		end

		H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
	end

	local function sha512_feed_128(H_lo, H_hi, str, offs, size)
		local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
		local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
		local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
		for pos = offs, offs + size - 1, 128 do
			for j = 1, 16 * 2 do
				pos = pos + 4
				local a, b, c, d = string.byte(str, pos - 3, pos)
				W[j] = ((a * 256 + b) * 256 + c) * 256 + d
			end

			for jj = 34, 160, 2 do
				local a_lo, a_hi, b_lo, b_hi = W[jj - 30], W[jj - 31], W[jj - 4], W[jj - 5]
				local tmp1 = bit32_bxor(bit32_rshift(a_lo, 1) + bit32_lshift(a_hi, 31), bit32_rshift(a_lo, 8) + bit32_lshift(a_hi, 24), bit32_rshift(a_lo, 7) + bit32_lshift(a_hi, 25)) % 4294967296 +
					bit32_bxor(bit32_rshift(b_lo, 19) + bit32_lshift(b_hi, 13), bit32_lshift(b_lo, 3) + bit32_rshift(b_hi, 29), bit32_rshift(b_lo, 6) + bit32_lshift(b_hi, 26)) % 4294967296 +
					W[jj - 14] + W[jj - 32]

				local tmp2 = tmp1 % 4294967296
				W[jj - 1] = bit32_bxor(bit32_rshift(a_hi, 1) + bit32_lshift(a_lo, 31), bit32_rshift(a_hi, 8) + bit32_lshift(a_lo, 24), bit32_rshift(a_hi, 7)) +
					bit32_bxor(bit32_rshift(b_hi, 19) + bit32_lshift(b_lo, 13), bit32_lshift(b_hi, 3) + bit32_rshift(b_lo, 29), bit32_rshift(b_hi, 6)) +
					W[jj - 15] + W[jj - 33] + (tmp1 - tmp2) / 4294967296

				W[jj] = tmp2
			end

			local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
			local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
			for j = 1, 80 do
				local jj = 2 * j
				local tmp1 = bit32_bxor(bit32_rshift(e_lo, 14) + bit32_lshift(e_hi, 18), bit32_rshift(e_lo, 18) + bit32_lshift(e_hi, 14), bit32_lshift(e_lo, 23) + bit32_rshift(e_hi, 9)) % 4294967296 +
					(bit32_band(e_lo, f_lo) + bit32_band(-1 - e_lo, g_lo)) % 4294967296 +
					h_lo + K_lo[j] + W[jj]

				local z_lo = tmp1 % 4294967296
				local z_hi = bit32_bxor(bit32_rshift(e_hi, 14) + bit32_lshift(e_lo, 18), bit32_rshift(e_hi, 18) + bit32_lshift(e_lo, 14), bit32_lshift(e_hi, 23) + bit32_rshift(e_lo, 9)) +
					bit32_band(e_hi, f_hi) + bit32_band(-1 - e_hi, g_hi) +
					h_hi + K_hi[j] + W[jj - 1] +
					(tmp1 - z_lo) / 4294967296

				h_lo = g_lo
				h_hi = g_hi
				g_lo = f_lo
				g_hi = f_hi
				f_lo = e_lo
				f_hi = e_hi
				tmp1 = z_lo + d_lo
				e_lo = tmp1 % 4294967296
				e_hi = z_hi + d_hi + (tmp1 - e_lo) / 4294967296
				d_lo = c_lo
				d_hi = c_hi
				c_lo = b_lo
				c_hi = b_hi
				b_lo = a_lo
				b_hi = a_hi
				tmp1 = z_lo + (bit32_band(d_lo, c_lo) + bit32_band(b_lo, bit32_bxor(d_lo, c_lo))) % 4294967296 + bit32_bxor(bit32_rshift(b_lo, 28) + bit32_lshift(b_hi, 4), bit32_lshift(b_lo, 30) + bit32_rshift(b_hi, 2), bit32_lshift(b_lo, 25) + bit32_rshift(b_hi, 7)) % 4294967296
				a_lo = tmp1 % 4294967296
				a_hi = z_hi + (bit32_band(d_hi, c_hi) + bit32_band(b_hi, bit32_bxor(d_hi, c_hi))) + bit32_bxor(bit32_rshift(b_hi, 28) + bit32_lshift(b_lo, 4), bit32_lshift(b_hi, 30) + bit32_rshift(b_lo, 2), bit32_lshift(b_hi, 25) + bit32_rshift(b_lo, 7)) + (tmp1 - a_lo) / 4294967296
			end

			a_lo = h1_lo + a_lo
			h1_lo = a_lo % 4294967296
			h1_hi = (h1_hi + a_hi + (a_lo - h1_lo) / 4294967296) % 4294967296
			a_lo = h2_lo + b_lo
			h2_lo = a_lo % 4294967296
			h2_hi = (h2_hi + b_hi + (a_lo - h2_lo) / 4294967296) % 4294967296
			a_lo = h3_lo + c_lo
			h3_lo = a_lo % 4294967296
			h3_hi = (h3_hi + c_hi + (a_lo - h3_lo) / 4294967296) % 4294967296
			a_lo = h4_lo + d_lo
			h4_lo = a_lo % 4294967296
			h4_hi = (h4_hi + d_hi + (a_lo - h4_lo) / 4294967296) % 4294967296
			a_lo = h5_lo + e_lo
			h5_lo = a_lo % 4294967296
			h5_hi = (h5_hi + e_hi + (a_lo - h5_lo) / 4294967296) % 4294967296
			a_lo = h6_lo + f_lo
			h6_lo = a_lo % 4294967296
			h6_hi = (h6_hi + f_hi + (a_lo - h6_lo) / 4294967296) % 4294967296
			a_lo = h7_lo + g_lo
			h7_lo = a_lo % 4294967296
			h7_hi = (h7_hi + g_hi + (a_lo - h7_lo) / 4294967296) % 4294967296
			a_lo = h8_lo + h_lo
			h8_lo = a_lo % 4294967296
			h8_hi = (h8_hi + h_hi + (a_lo - h8_lo) / 4294967296) % 4294967296
		end

		H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
		H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
	end

	local function md5_feed_64(H, str, offs, size)
		local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
		local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
		for pos = offs, offs + size - 1, 64 do
			for j = 1, 16 do
				pos = pos + 4
				local a, b, c, d = string.byte(str, pos - 3, pos)
				W[j] = ((d * 256 + c) * 256 + b) * 256 + a
			end

			local a, b, c, d = h1, h2, h3, h4
			local s = 25
			for j = 1, 16 do
				local F = bit32_rrotate(bit32_band(b, c) + bit32_band(-1 - b, d) + a + K[j] + W[j], s) + b
				s = md5_next_shift[s]
				a = d
				d = c
				c = b
				b = F
			end

			s = 27
			for j = 17, 32 do
				local F = bit32_rrotate(bit32_band(d, b) + bit32_band(-1 - d, c) + a + K[j] + W[(5 * j - 4) % 16 + 1], s) + b
				s = md5_next_shift[s]
				a = d
				d = c
				c = b
				b = F
			end

			s = 28
			for j = 33, 48 do
				local F = bit32_rrotate(bit32_bxor(bit32_bxor(b, c), d) + a + K[j] + W[(3 * j + 2) % 16 + 1], s) + b
				s = md5_next_shift[s]
				a = d
				d = c
				c = b
				b = F
			end

			s = 26
			for j = 49, 64 do
				local F = bit32_rrotate(bit32_bxor(c, bit32_bor(b, -1 - d)) + a + K[j] + W[(j * 7 - 7) % 16 + 1], s) + b
				s = md5_next_shift[s]
				a = d
				d = c
				c = b
				b = F
			end

			h1 = (a + h1) % 4294967296
			h2 = (b + h2) % 4294967296
			h3 = (c + h3) % 4294967296
			h4 = (d + h4) % 4294967296
		end

		H[1], H[2], H[3], H[4] = h1, h2, h3, h4
	end

	local function sha1_feed_64(H, str, offs, size)
		-- offs >= 0, size >= 0, size is multiple of 64
		local W = common_W
		local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
		for pos = offs, offs + size - 1, 64 do
			for j = 1, 16 do
				pos = pos + 4
				local a, b, c, d = string.byte(str, pos - 3, pos)
				W[j] = ((a * 256 + b) * 256 + c) * 256 + d
			end

			for j = 17, 80 do
				W[j] = bit32_lrotate(bit32_bxor(W[j - 3], W[j - 8], W[j - 14], W[j - 16]), 1)
			end

			local a, b, c, d, e = h1, h2, h3, h4, h5
			for j = 1, 20 do
				local z = bit32_lrotate(a, 5) + bit32_band(b, c) + bit32_band(-1 - b, d) + 0x5A827999 + W[j] + e -- constant = math.floor(TWO_POW_30 * sqrt(2))
				e = d
				d = c
				c = bit32_rrotate(b, 2)
				b = a
				a = z
			end

			for j = 21, 40 do
				local z = bit32_lrotate(a, 5) + bit32_bxor(b, c, d) + 0x6ED9EBA1 + W[j] + e -- TWO_POW_30 * sqrt(3)
				e = d
				d = c
				c = bit32_rrotate(b, 2)
				b = a
				a = z
			end

			for j = 41, 60 do
				local z = bit32_lrotate(a, 5) + bit32_band(d, c) + bit32_band(b, bit32_bxor(d, c)) + 0x8F1BBCDC + W[j] + e -- TWO_POW_30 * sqrt(5)
				e = d
				d = c
				c = bit32_rrotate(b, 2)
				b = a
				a = z
			end

			for j = 61, 80 do
				local z = bit32_lrotate(a, 5) + bit32_bxor(b, c, d) + 0xCA62C1D6 + W[j] + e -- TWO_POW_30 * sqrt(10)
				e = d
				d = c
				c = bit32_rrotate(b, 2)
				b = a
				a = z
			end

			h1 = (a + h1) % 4294967296
			h2 = (b + h2) % 4294967296
			h3 = (c + h3) % 4294967296
			h4 = (d + h4) % 4294967296
			h5 = (e + h5) % 4294967296
		end

		H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
	end

	local function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
		-- This is an example of a Lua function having 79 local variables :-)
		-- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
		local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
		local qwords_qty = block_size_in_bytes / 8
		for pos = offs, offs + size - 1, block_size_in_bytes do
			for j = 1, qwords_qty do
				local a, b, c, d = string.byte(str, pos + 1, pos + 4)
				lanes_lo[j] = bit32_bxor(lanes_lo[j], ((d * 256 + c) * 256 + b) * 256 + a)
				pos = pos + 8
				a, b, c, d = string.byte(str, pos - 3, pos)
				lanes_hi[j] = bit32_bxor(lanes_hi[j], ((d * 256 + c) * 256 + b) * 256 + a)
			end

			local L01_lo, L01_hi, L02_lo, L02_hi, L03_lo, L03_hi, L04_lo, L04_hi, L05_lo, L05_hi, L06_lo, L06_hi, L07_lo, L07_hi, L08_lo, L08_hi, L09_lo, L09_hi, L10_lo, L10_hi, L11_lo, L11_hi, L12_lo, L12_hi, L13_lo, L13_hi, L14_lo, L14_hi, L15_lo, L15_hi, L16_lo, L16_hi, L17_lo, L17_hi, L18_lo, L18_hi, L19_lo, L19_hi, L20_lo, L20_hi, L21_lo, L21_hi, L22_lo, L22_hi, L23_lo, L23_hi, L24_lo, L24_hi, L25_lo, L25_hi = lanes_lo[1], lanes_hi[1], lanes_lo[2], lanes_hi[2], lanes_lo[3], lanes_hi[3], lanes_lo[4], lanes_hi[4], lanes_lo[5], lanes_hi[5], lanes_lo[6], lanes_hi[6], lanes_lo[7], lanes_hi[7], lanes_lo[8], lanes_hi[8], lanes_lo[9], lanes_hi[9], lanes_lo[10], lanes_hi[10], lanes_lo[11], lanes_hi[11], lanes_lo[12], lanes_hi[12], lanes_lo[13], lanes_hi[13], lanes_lo[14], lanes_hi[14], lanes_lo[15], lanes_hi[15], lanes_lo[16], lanes_hi[16], lanes_lo[17], lanes_hi[17], lanes_lo[18], lanes_hi[18], lanes_lo[19], lanes_hi[19], lanes_lo[20], lanes_hi[20], lanes_lo[21], lanes_hi[21], lanes_lo[22], lanes_hi[22], lanes_lo[23], lanes_hi[23], lanes_lo[24], lanes_hi[24], lanes_lo[25], lanes_hi[25]

			for round_idx = 1, 24 do
				local C1_lo = bit32_bxor(L01_lo, L06_lo, L11_lo, L16_lo, L21_lo)
				local C1_hi = bit32_bxor(L01_hi, L06_hi, L11_hi, L16_hi, L21_hi)
				local C2_lo = bit32_bxor(L02_lo, L07_lo, L12_lo, L17_lo, L22_lo)
				local C2_hi = bit32_bxor(L02_hi, L07_hi, L12_hi, L17_hi, L22_hi)
				local C3_lo = bit32_bxor(L03_lo, L08_lo, L13_lo, L18_lo, L23_lo)
				local C3_hi = bit32_bxor(L03_hi, L08_hi, L13_hi, L18_hi, L23_hi)
				local C4_lo = bit32_bxor(L04_lo, L09_lo, L14_lo, L19_lo, L24_lo)
				local C4_hi = bit32_bxor(L04_hi, L09_hi, L14_hi, L19_hi, L24_hi)
				local C5_lo = bit32_bxor(L05_lo, L10_lo, L15_lo, L20_lo, L25_lo)
				local C5_hi = bit32_bxor(L05_hi, L10_hi, L15_hi, L20_hi, L25_hi)

				local D_lo = bit32_bxor(C1_lo, C3_lo * 2 + (C3_hi % TWO_POW_32 - C3_hi % TWO_POW_31) / TWO_POW_31)
				local D_hi = bit32_bxor(C1_hi, C3_hi * 2 + (C3_lo % TWO_POW_32 - C3_lo % TWO_POW_31) / TWO_POW_31)

				local T0_lo = bit32_bxor(D_lo, L02_lo)
				local T0_hi = bit32_bxor(D_hi, L02_hi)
				local T1_lo = bit32_bxor(D_lo, L07_lo)
				local T1_hi = bit32_bxor(D_hi, L07_hi)
				local T2_lo = bit32_bxor(D_lo, L12_lo)
				local T2_hi = bit32_bxor(D_hi, L12_hi)
				local T3_lo = bit32_bxor(D_lo, L17_lo)
				local T3_hi = bit32_bxor(D_hi, L17_hi)
				local T4_lo = bit32_bxor(D_lo, L22_lo)
				local T4_hi = bit32_bxor(D_hi, L22_hi)

				L02_lo = (T1_lo % TWO_POW_32 - T1_lo % TWO_POW_20) / TWO_POW_20 + T1_hi * TWO_POW_12
				L02_hi = (T1_hi % TWO_POW_32 - T1_hi % TWO_POW_20) / TWO_POW_20 + T1_lo * TWO_POW_12
				L07_lo = (T3_lo % TWO_POW_32 - T3_lo % TWO_POW_19) / TWO_POW_19 + T3_hi * TWO_POW_13
				L07_hi = (T3_hi % TWO_POW_32 - T3_hi % TWO_POW_19) / TWO_POW_19 + T3_lo * TWO_POW_13
				L12_lo = T0_lo * 2 + (T0_hi % TWO_POW_32 - T0_hi % TWO_POW_31) / TWO_POW_31
				L12_hi = T0_hi * 2 + (T0_lo % TWO_POW_32 - T0_lo % TWO_POW_31) / TWO_POW_31
				L17_lo = T2_lo * TWO_POW_10 + (T2_hi % TWO_POW_32 - T2_hi % TWO_POW_22) / TWO_POW_22
				L17_hi = T2_hi * TWO_POW_10 + (T2_lo % TWO_POW_32 - T2_lo % TWO_POW_22) / TWO_POW_22
				L22_lo = T4_lo * TWO_POW_2 + (T4_hi % TWO_POW_32 - T4_hi % TWO_POW_30) / TWO_POW_30
				L22_hi = T4_hi * TWO_POW_2 + (T4_lo % TWO_POW_32 - T4_lo % TWO_POW_30) / TWO_POW_30

				D_lo = bit32_bxor(C2_lo, C4_lo * 2 + (C4_hi % TWO_POW_32 - C4_hi % TWO_POW_31) / TWO_POW_31)
				D_hi = bit32_bxor(C2_hi, C4_hi * 2 + (C4_lo % TWO_POW_32 - C4_lo % TWO_POW_31) / TWO_POW_31)

				T0_lo = bit32_bxor(D_lo, L03_lo)
				T0_hi = bit32_bxor(D_hi, L03_hi)
				T1_lo = bit32_bxor(D_lo, L08_lo)
				T1_hi = bit32_bxor(D_hi, L08_hi)
				T2_lo = bit32_bxor(D_lo, L13_lo)
				T2_hi = bit32_bxor(D_hi, L13_hi)
				T3_lo = bit32_bxor(D_lo, L18_lo)
				T3_hi = bit32_bxor(D_hi, L18_hi)
				T4_lo = bit32_bxor(D_lo, L23_lo)
				T4_hi = bit32_bxor(D_hi, L23_hi)

				L03_lo = (T2_lo % TWO_POW_32 - T2_lo % TWO_POW_21) / TWO_POW_21 + T2_hi * TWO_POW_11
				L03_hi = (T2_hi % TWO_POW_32 - T2_hi % TWO_POW_21) / TWO_POW_21 + T2_lo * TWO_POW_11
				L08_lo = (T4_lo % TWO_POW_32 - T4_lo % TWO_POW_3) / TWO_POW_3 + T4_hi * TWO_POW_29 % TWO_POW_32
				L08_hi = (T4_hi % TWO_POW_32 - T4_hi % TWO_POW_3) / TWO_POW_3 + T4_lo * TWO_POW_29 % TWO_POW_32
				L13_lo = T1_lo * TWO_POW_6 + (T1_hi % TWO_POW_32 - T1_hi % TWO_POW_26) / TWO_POW_26
				L13_hi = T1_hi * TWO_POW_6 + (T1_lo % TWO_POW_32 - T1_lo % TWO_POW_26) / TWO_POW_26
				L18_lo = T3_lo * TWO_POW_15 + (T3_hi % TWO_POW_32 - T3_hi % TWO_POW_17) / TWO_POW_17
				L18_hi = T3_hi * TWO_POW_15 + (T3_lo % TWO_POW_32 - T3_lo % TWO_POW_17) / TWO_POW_17
				L23_lo = (T0_lo % TWO_POW_32 - T0_lo % TWO_POW_2) / TWO_POW_2 + T0_hi * TWO_POW_30 % TWO_POW_32
				L23_hi = (T0_hi % TWO_POW_32 - T0_hi % TWO_POW_2) / TWO_POW_2 + T0_lo * TWO_POW_30 % TWO_POW_32

				D_lo = bit32_bxor(C3_lo, C5_lo * 2 + (C5_hi % TWO_POW_32 - C5_hi % TWO_POW_31) / TWO_POW_31)
				D_hi = bit32_bxor(C3_hi, C5_hi * 2 + (C5_lo % TWO_POW_32 - C5_lo % TWO_POW_31) / TWO_POW_31)

				T0_lo = bit32_bxor(D_lo, L04_lo)
				T0_hi = bit32_bxor(D_hi, L04_hi)
				T1_lo = bit32_bxor(D_lo, L09_lo)
				T1_hi = bit32_bxor(D_hi, L09_hi)
				T2_lo = bit32_bxor(D_lo, L14_lo)
				T2_hi = bit32_bxor(D_hi, L14_hi)
				T3_lo = bit32_bxor(D_lo, L19_lo)
				T3_hi = bit32_bxor(D_hi, L19_hi)
				T4_lo = bit32_bxor(D_lo, L24_lo)
				T4_hi = bit32_bxor(D_hi, L24_hi)

				L04_lo = T3_lo * TWO_POW_21 % TWO_POW_32 + (T3_hi % TWO_POW_32 - T3_hi % TWO_POW_11) / TWO_POW_11
				L04_hi = T3_hi * TWO_POW_21 % TWO_POW_32 + (T3_lo % TWO_POW_32 - T3_lo % TWO_POW_11) / TWO_POW_11
				L09_lo = T0_lo * TWO_POW_28 % TWO_POW_32 + (T0_hi % TWO_POW_32 - T0_hi % TWO_POW_4) / TWO_POW_4
				L09_hi = T0_hi * TWO_POW_28 % TWO_POW_32 + (T0_lo % TWO_POW_32 - T0_lo % TWO_POW_4) / TWO_POW_4
				L14_lo = T2_lo * TWO_POW_25 % TWO_POW_32 + (T2_hi % TWO_POW_32 - T2_hi % TWO_POW_7) / TWO_POW_7
				L14_hi = T2_hi * TWO_POW_25 % TWO_POW_32 + (T2_lo % TWO_POW_32 - T2_lo % TWO_POW_7) / TWO_POW_7
				L19_lo = (T4_lo % TWO_POW_32 - T4_lo % TWO_POW_8) / TWO_POW_8 + T4_hi * TWO_POW_24 % TWO_POW_32
				L19_hi = (T4_hi % TWO_POW_32 - T4_hi % TWO_POW_8) / TWO_POW_8 + T4_lo * TWO_POW_24 % TWO_POW_32
				L24_lo = (T1_lo % TWO_POW_32 - T1_lo % TWO_POW_9) / TWO_POW_9 + T1_hi * TWO_POW_23 % TWO_POW_32
				L24_hi = (T1_hi % TWO_POW_32 - T1_hi % TWO_POW_9) / TWO_POW_9 + T1_lo * TWO_POW_23 % TWO_POW_32

				D_lo = bit32_bxor(C4_lo, C1_lo * 2 + (C1_hi % TWO_POW_32 - C1_hi % TWO_POW_31) / TWO_POW_31)
				D_hi = bit32_bxor(C4_hi, C1_hi * 2 + (C1_lo % TWO_POW_32 - C1_lo % TWO_POW_31) / TWO_POW_31)

				T0_lo = bit32_bxor(D_lo, L05_lo)
				T0_hi = bit32_bxor(D_hi, L05_hi)
				T1_lo = bit32_bxor(D_lo, L10_lo)
				T1_hi = bit32_bxor(D_hi, L10_hi)
				T2_lo = bit32_bxor(D_lo, L15_lo)
				T2_hi = bit32_bxor(D_hi, L15_hi)
				T3_lo = bit32_bxor(D_lo, L20_lo)
				T3_hi = bit32_bxor(D_hi, L20_hi)
				T4_lo = bit32_bxor(D_lo, L25_lo)
				T4_hi = bit32_bxor(D_hi, L25_hi)

				L05_lo = T4_lo * TWO_POW_14 + (T4_hi % TWO_POW_32 - T4_hi % TWO_POW_18) / TWO_POW_18
				L05_hi = T4_hi * TWO_POW_14 + (T4_lo % TWO_POW_32 - T4_lo % TWO_POW_18) / TWO_POW_18
				L10_lo = T1_lo * TWO_POW_20 % TWO_POW_32 + (T1_hi % TWO_POW_32 - T1_hi % TWO_POW_12) / TWO_POW_12
				L10_hi = T1_hi * TWO_POW_20 % TWO_POW_32 + (T1_lo % TWO_POW_32 - T1_lo % TWO_POW_12) / TWO_POW_12
				L15_lo = T3_lo * TWO_POW_8 + (T3_hi % TWO_POW_32 - T3_hi % TWO_POW_24) / TWO_POW_24
				L15_hi = T3_hi * TWO_POW_8 + (T3_lo % TWO_POW_32 - T3_lo % TWO_POW_24) / TWO_POW_24
				L20_lo = T0_lo * TWO_POW_27 % TWO_POW_32 + (T0_hi % TWO_POW_32 - T0_hi % TWO_POW_5) / TWO_POW_5
				L20_hi = T0_hi * TWO_POW_27 % TWO_POW_32 + (T0_lo % TWO_POW_32 - T0_lo % TWO_POW_5) / TWO_POW_5
				L25_lo = (T2_lo % TWO_POW_32 - T2_lo % TWO_POW_25) / TWO_POW_25 + T2_hi * TWO_POW_7
				L25_hi = (T2_hi % TWO_POW_32 - T2_hi % TWO_POW_25) / TWO_POW_25 + T2_lo * TWO_POW_7

				D_lo = bit32_bxor(C5_lo, C2_lo * 2 + (C2_hi % TWO_POW_32 - C2_hi % TWO_POW_31) / TWO_POW_31)
				D_hi = bit32_bxor(C5_hi, C2_hi * 2 + (C2_lo % TWO_POW_32 - C2_lo % TWO_POW_31) / TWO_POW_31)

				T1_lo = bit32_bxor(D_lo, L06_lo)
				T1_hi = bit32_bxor(D_hi, L06_hi)
				T2_lo = bit32_bxor(D_lo, L11_lo)
				T2_hi = bit32_bxor(D_hi, L11_hi)
				T3_lo = bit32_bxor(D_lo, L16_lo)
				T3_hi = bit32_bxor(D_hi, L16_hi)
				T4_lo = bit32_bxor(D_lo, L21_lo)
				T4_hi = bit32_bxor(D_hi, L21_hi)

				L06_lo = T2_lo * TWO_POW_3 + (T2_hi % TWO_POW_32 - T2_hi % TWO_POW_29) / TWO_POW_29
				L06_hi = T2_hi * TWO_POW_3 + (T2_lo % TWO_POW_32 - T2_lo % TWO_POW_29) / TWO_POW_29
				L11_lo = T4_lo * TWO_POW_18 + (T4_hi % TWO_POW_32 - T4_hi % TWO_POW_14) / TWO_POW_14
				L11_hi = T4_hi * TWO_POW_18 + (T4_lo % TWO_POW_32 - T4_lo % TWO_POW_14) / TWO_POW_14
				L16_lo = (T1_lo % TWO_POW_32 - T1_lo % TWO_POW_28) / TWO_POW_28 + T1_hi * TWO_POW_4
				L16_hi = (T1_hi % TWO_POW_32 - T1_hi % TWO_POW_28) / TWO_POW_28 + T1_lo * TWO_POW_4
				L21_lo = (T3_lo % TWO_POW_32 - T3_lo % TWO_POW_23) / TWO_POW_23 + T3_hi * TWO_POW_9
				L21_hi = (T3_hi % TWO_POW_32 - T3_hi % TWO_POW_23) / TWO_POW_23 + T3_lo * TWO_POW_9

				L01_lo = bit32_bxor(D_lo, L01_lo)
				L01_hi = bit32_bxor(D_hi, L01_hi)
				L01_lo, L02_lo, L03_lo, L04_lo, L05_lo = bit32_bxor(L01_lo, bit32_band(-1 - L02_lo, L03_lo)), bit32_bxor(L02_lo, bit32_band(-1 - L03_lo, L04_lo)), bit32_bxor(L03_lo, bit32_band(-1 - L04_lo, L05_lo)), bit32_bxor(L04_lo, bit32_band(-1 - L05_lo, L01_lo)), bit32_bxor(L05_lo, bit32_band(-1 - L01_lo, L02_lo))
				L01_hi, L02_hi, L03_hi, L04_hi, L05_hi = bit32_bxor(L01_hi, bit32_band(-1 - L02_hi, L03_hi)), bit32_bxor(L02_hi, bit32_band(-1 - L03_hi, L04_hi)), bit32_bxor(L03_hi, bit32_band(-1 - L04_hi, L05_hi)), bit32_bxor(L04_hi, bit32_band(-1 - L05_hi, L01_hi)), bit32_bxor(L05_hi, bit32_band(-1 - L01_hi, L02_hi))
				L06_lo, L07_lo, L08_lo, L09_lo, L10_lo = bit32_bxor(L09_lo, bit32_band(-1 - L10_lo, L06_lo)), bit32_bxor(L10_lo, bit32_band(-1 - L06_lo, L07_lo)), bit32_bxor(L06_lo, bit32_band(-1 - L07_lo, L08_lo)), bit32_bxor(L07_lo, bit32_band(-1 - L08_lo, L09_lo)), bit32_bxor(L08_lo, bit32_band(-1 - L09_lo, L10_lo))
				L06_hi, L07_hi, L08_hi, L09_hi, L10_hi = bit32_bxor(L09_hi, bit32_band(-1 - L10_hi, L06_hi)), bit32_bxor(L10_hi, bit32_band(-1 - L06_hi, L07_hi)), bit32_bxor(L06_hi, bit32_band(-1 - L07_hi, L08_hi)), bit32_bxor(L07_hi, bit32_band(-1 - L08_hi, L09_hi)), bit32_bxor(L08_hi, bit32_band(-1 - L09_hi, L10_hi))
				L11_lo, L12_lo, L13_lo, L14_lo, L15_lo = bit32_bxor(L12_lo, bit32_band(-1 - L13_lo, L14_lo)), bit32_bxor(L13_lo, bit32_band(-1 - L14_lo, L15_lo)), bit32_bxor(L14_lo, bit32_band(-1 - L15_lo, L11_lo)), bit32_bxor(L15_lo, bit32_band(-1 - L11_lo, L12_lo)), bit32_bxor(L11_lo, bit32_band(-1 - L12_lo, L13_lo))
				L11_hi, L12_hi, L13_hi, L14_hi, L15_hi = bit32_bxor(L12_hi, bit32_band(-1 - L13_hi, L14_hi)), bit32_bxor(L13_hi, bit32_band(-1 - L14_hi, L15_hi)), bit32_bxor(L14_hi, bit32_band(-1 - L15_hi, L11_hi)), bit32_bxor(L15_hi, bit32_band(-1 - L11_hi, L12_hi)), bit32_bxor(L11_hi, bit32_band(-1 - L12_hi, L13_hi))
				L16_lo, L17_lo, L18_lo, L19_lo, L20_lo = bit32_bxor(L20_lo, bit32_band(-1 - L16_lo, L17_lo)), bit32_bxor(L16_lo, bit32_band(-1 - L17_lo, L18_lo)), bit32_bxor(L17_lo, bit32_band(-1 - L18_lo, L19_lo)), bit32_bxor(L18_lo, bit32_band(-1 - L19_lo, L20_lo)), bit32_bxor(L19_lo, bit32_band(-1 - L20_lo, L16_lo))
				L16_hi, L17_hi, L18_hi, L19_hi, L20_hi = bit32_bxor(L20_hi, bit32_band(-1 - L16_hi, L17_hi)), bit32_bxor(L16_hi, bit32_band(-1 - L17_hi, L18_hi)), bit32_bxor(L17_hi, bit32_band(-1 - L18_hi, L19_hi)), bit32_bxor(L18_hi, bit32_band(-1 - L19_hi, L20_hi)), bit32_bxor(L19_hi, bit32_band(-1 - L20_hi, L16_hi))
				L21_lo, L22_lo, L23_lo, L24_lo, L25_lo = bit32_bxor(L23_lo, bit32_band(-1 - L24_lo, L25_lo)), bit32_bxor(L24_lo, bit32_band(-1 - L25_lo, L21_lo)), bit32_bxor(L25_lo, bit32_band(-1 - L21_lo, L22_lo)), bit32_bxor(L21_lo, bit32_band(-1 - L22_lo, L23_lo)), bit32_bxor(L22_lo, bit32_band(-1 - L23_lo, L24_lo))
				L21_hi, L22_hi, L23_hi, L24_hi, L25_hi = bit32_bxor(L23_hi, bit32_band(-1 - L24_hi, L25_hi)), bit32_bxor(L24_hi, bit32_band(-1 - L25_hi, L21_hi)), bit32_bxor(L25_hi, bit32_band(-1 - L21_hi, L22_hi)), bit32_bxor(L21_hi, bit32_band(-1 - L22_hi, L23_hi)), bit32_bxor(L22_hi, bit32_band(-1 - L23_hi, L24_hi))
				L01_lo = bit32_bxor(L01_lo, RC_lo[round_idx])
				L01_hi = L01_hi + RC_hi[round_idx] -- RC_hi[] is either 0 or 0x80000000, so we could use fast addition instead of slow XOR
			end

			lanes_lo[1] = L01_lo
			lanes_hi[1] = L01_hi
			lanes_lo[2] = L02_lo
			lanes_hi[2] = L02_hi
			lanes_lo[3] = L03_lo
			lanes_hi[3] = L03_hi
			lanes_lo[4] = L04_lo
			lanes_hi[4] = L04_hi
			lanes_lo[5] = L05_lo
			lanes_hi[5] = L05_hi
			lanes_lo[6] = L06_lo
			lanes_hi[6] = L06_hi
			lanes_lo[7] = L07_lo
			lanes_hi[7] = L07_hi
			lanes_lo[8] = L08_lo
			lanes_hi[8] = L08_hi
			lanes_lo[9] = L09_lo
			lanes_hi[9] = L09_hi
			lanes_lo[10] = L10_lo
			lanes_hi[10] = L10_hi
			lanes_lo[11] = L11_lo
			lanes_hi[11] = L11_hi
			lanes_lo[12] = L12_lo
			lanes_hi[12] = L12_hi
			lanes_lo[13] = L13_lo
			lanes_hi[13] = L13_hi
			lanes_lo[14] = L14_lo
			lanes_hi[14] = L14_hi
			lanes_lo[15] = L15_lo
			lanes_hi[15] = L15_hi
			lanes_lo[16] = L16_lo
			lanes_hi[16] = L16_hi
			lanes_lo[17] = L17_lo
			lanes_hi[17] = L17_hi
			lanes_lo[18] = L18_lo
			lanes_hi[18] = L18_hi
			lanes_lo[19] = L19_lo
			lanes_hi[19] = L19_hi
			lanes_lo[20] = L20_lo
			lanes_hi[20] = L20_hi
			lanes_lo[21] = L21_lo
			lanes_hi[21] = L21_hi
			lanes_lo[22] = L22_lo
			lanes_hi[22] = L22_hi
			lanes_lo[23] = L23_lo
			lanes_hi[23] = L23_hi
			lanes_lo[24] = L24_lo
			lanes_hi[24] = L24_hi
			lanes_lo[25] = L25_lo
			lanes_hi[25] = L25_hi
		end
	end
	do
		local function mul(src1, src2, factor, result_length)
			local result, carry, value, weight = table.create(result_length), 0, 0, 1
			for j = 1, result_length do
				for k = math.max(1, j + 1 - #src2), math.min(j, #src1) do
					carry = carry + factor * src1[k] * src2[j + 1 - k]
				end

				local digit = carry % TWO_POW_24
				result[j] = math.floor(digit)
				carry = (carry - digit) / TWO_POW_24
				value = value + digit * weight
				weight = weight * TWO_POW_24
			end

			return result, value
		end

		local idx, step, p, one, sqrt_hi, sqrt_lo = 0, {4, 1, 2, -2, 2}, 4, {1}, sha2_H_hi, sha2_H_lo
		repeat
			p = p + step[p % 6]
			local d = 1
			repeat
				d = d + step[d % 6]
				if d * d > p then
					local root = p ^ (1 / 3)
					local R = root * TWO_POW_40
					R = mul(table.create(1, math.floor(R)), one, 1, 2)
					local _, delta = mul(R, mul(R, R, 1, 4), -1, 4)
					local hi = R[2] % 65536 * 65536 + math.floor(R[1] / 256)
					local lo = R[1] % 256 * 16777216 + math.floor(delta * (TWO_POW_NEG_56 / 3) * root / p)

					if idx < 16 then
						root = math.sqrt(p)
						R = root * TWO_POW_40
						R = mul(table.create(1, math.floor(R)), one, 1, 2)
						_, delta = mul(R, R, -1, 2)
						local hi = R[2] % 65536 * 65536 + math.floor(R[1] / 256)
						local lo = R[1] % 256 * 16777216 + math.floor(delta * TWO_POW_NEG_17 / root)
						local idx = idx % 8 + 1
						sha2_H_ext256[224][idx] = lo
						sqrt_hi[idx], sqrt_lo[idx] = hi, lo + hi * hi_factor
						if idx > 7 then
							sqrt_hi, sqrt_lo = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384]
						end
					end

					idx = idx + 1
					sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo % K_lo_modulo + hi * hi_factor
					break
				end
			until p % d == 0
		until idx > 79
	end
	for width = 224, 256, 32 do
		local H_lo, H_hi = table.create(0), nil
		if XOR64A5 then
			for j = 1, 8 do
				H_lo[j] = XOR64A5(sha2_H_lo[j])
			end
		else
			H_hi = table.create(0)
			for j = 1, 8 do
				H_lo[j] = bit32_bxor(sha2_H_lo[j], 0xA5A5A5A5) % 4294967296
				H_hi[j] = bit32_bxor(sha2_H_hi[j], 0xA5A5A5A5) % 4294967296
			end
		end

		sha512_feed_128(H_lo, H_hi, "SHA-512/" .. tostring(width) .. "\128" .. string.rep("\0", 115) .. "\88", 0, 128)
		sha2_H_ext512_lo[width] = H_lo
		sha2_H_ext512_hi[width] = H_hi
	end
	do
		for idx = 1, 64 do
			local hi, lo = math.modf(math.abs(math.sin(idx)) * TWO_POW_16)
			md5_K[idx] = hi * 65536 + math.floor(lo * TWO_POW_16)
		end
	end
	do
		local sh_reg = 29
		local function next_bit()
			local r = sh_reg % 2
			sh_reg = bit32_bxor((sh_reg - r) / 2, 142 * r)
			return r
		end

		for idx = 1, 24 do
			local lo, m = 0, nil
			for _ = 1, 6 do
				m = m and m * m * 2 or 1
				lo = lo + next_bit() * m
			end

			local hi = next_bit() * m
			sha3_RC_hi[idx], sha3_RC_lo[idx] = hi, lo + hi * hi_factor_keccak
		end
	end
	local function sha256ext(width, message)
		local Array256 = sha2_H_ext256[width] -- # == 8
		local length, tail = 0, ""
		local H = table.create(8)
		H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = Array256[1], Array256[2], Array256[3], Array256[4], Array256[5], Array256[6], Array256[7], Array256[8]

		local function partial(message_part)
			if message_part then
				local partLength = #message_part
				if tail then
					length = length + partLength
					local offs = 0
					local tailLength = #tail
					if tail ~= "" and tailLength + partLength >= 64 then
						offs = 64 - tailLength
						sha256_feed_64(H, tail .. string.sub(message_part, 1, offs), 0, 64)
						tail = ""
					end

					local size = partLength - offs
					local size_tail = size % 64
					sha256_feed_64(H, message_part, offs, size - size_tail)
					tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
					return partial
				else
					error("Adding more chunks is not allowed after receiving the result", 2)
				end
			else
				if tail then
					local final_blocks = table.create(10) --{tail, "\128", string.rep("\0", (-9 - length) % 64 + 1)}
					final_blocks[1] = tail
					final_blocks[2] = "\128"
					final_blocks[3] = string.rep("\0", (-9 - length) % 64 + 1)

					tail = nil
					length = length * (8 / TWO56_POW_7)
					for j = 4, 10 do
						length = length % 1 * 256
						final_blocks[j] = string.char(math.floor(length))
					end

					final_blocks = table.concat(final_blocks)
					sha256_feed_64(H, final_blocks, 0, #final_blocks)
					local max_reg = width / 32
					for j = 1, max_reg do
						H[j] = string.format("%08x", H[j] % 4294967296)
					end

					H = table.concat(H, "", 1, max_reg)
				end

				return H
			end
		end

		if message then
			return partial(message)()
		else
			return partial
		end
	end

	local function sha512ext(width, message)
		local length, tail, H_lo, H_hi = 0, "", table.pack(table.unpack(sha2_H_ext512_lo[width])), not HEX64 and table.pack(table.unpack(sha2_H_ext512_hi[width]))

		local function partial(message_part)
			if message_part then
				local partLength = #message_part
				if tail then
					length = length + partLength
					local offs = 0
					if tail ~= "" and #tail + partLength >= 128 then
						offs = 128 - #tail
						sha512_feed_128(H_lo, H_hi, tail .. string.sub(message_part, 1, offs), 0, 128)
						tail = ""
					end

					local size = partLength - offs
					local size_tail = size % 128
					sha512_feed_128(H_lo, H_hi, message_part, offs, size - size_tail)
					tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
					return partial
				else
					error("Adding more chunks is not allowed after receiving the result", 2)
				end
			else
				if tail then
					local final_blocks = table.create(3)
					final_blocks[1] = tail
					final_blocks[2] = "\128"
					final_blocks[3] = string.rep("\0", (-17 - length) % 128 + 9)

					tail = nil
					length = length * (8 / TWO56_POW_7)
					for j = 4, 10 do
						length = length % 1 * 256
						final_blocks[j] = string.char(math.floor(length))
					end

					final_blocks = table.concat(final_blocks)
					sha512_feed_128(H_lo, H_hi, final_blocks, 0, #final_blocks)
					local max_reg = math.ceil(width / 64)

					if HEX64 then
						for j = 1, max_reg do
							H_lo[j] = HEX64(H_lo[j])
						end
					else
						for j = 1, max_reg do
							H_lo[j] = string.format("%08x", H_hi[j] % 4294967296) .. string.format("%08x", H_lo[j] % 4294967296)
						end

						H_hi = nil
					end

					H_lo = string.sub(table.concat(H_lo, "", 1, max_reg), 1, width / 4)
				end

				return H_lo
			end
		end

		if message then
			return partial(message)()
		else
			return partial
		end
	end

	local function md5(message)
		local H, length, tail = table.create(4), 0, ""
		H[1], H[2], H[3], H[4] = md5_sha1_H[1], md5_sha1_H[2], md5_sha1_H[3], md5_sha1_H[4]

		local function partial(message_part)
			if message_part then
				local partLength = #message_part
				if tail then
					length = length + partLength
					local offs = 0
					if tail ~= "" and #tail + partLength >= 64 then
						offs = 64 - #tail
						md5_feed_64(H, tail .. string.sub(message_part, 1, offs), 0, 64)
						tail = ""
					end

					local size = partLength - offs
					local size_tail = size % 64
					md5_feed_64(H, message_part, offs, size - size_tail)
					tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
					return partial
				else
					error("Adding more chunks is not allowed after receiving the result", 2)
				end
			else
				if tail then
					local final_blocks = table.create(3) 
					final_blocks[1] = tail
					final_blocks[2] = "\128"
					final_blocks[3] = string.rep("\0", (-9 - length) % 64)
					tail = nil
					length = length * 8
					for j = 4, 11 do
						local low_byte = length % 256
						final_blocks[j] = string.char(low_byte)
						length = (length - low_byte) / 256
					end

					final_blocks = table.concat(final_blocks)
					md5_feed_64(H, final_blocks, 0, #final_blocks)
					for j = 1, 4 do
						H[j] = string.format("%08x", H[j] % 4294967296)
					end

					H = string.gsub(table.concat(H), "(..)(..)(..)(..)", "%4%3%2%1")
				end

				return H
			end
		end

		if message then
			return partial(message)()
		else
			return partial
		end
	end

	local function sha1(message)
		local H, length, tail = table.pack(table.unpack(md5_sha1_H)), 0, ""

		local function partial(message_part)
			if message_part then
				local partLength = #message_part
				if tail then
					length = length + partLength
					local offs = 0
					if tail ~= "" and #tail + partLength >= 64 then
						offs = 64 - #tail
						sha1_feed_64(H, tail .. string.sub(message_part, 1, offs), 0, 64)
						tail = ""
					end

					local size = partLength - offs
					local size_tail = size % 64
					sha1_feed_64(H, message_part, offs, size - size_tail)
					tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
					return partial
				else
					error("Adding more chunks is not allowed after receiving the result", 2)
				end
			else
				if tail then
					local final_blocks = table.create(10)
					final_blocks[1] = tail
					final_blocks[2] = "\128"
					final_blocks[3] = string.rep("\0", (-9 - length) % 64 + 1)
					tail = nil
					length = length * (8 / TWO56_POW_7)
					for j = 4, 10 do
						length = length % 1 * 256
						final_blocks[j] = string.char(math.floor(length))
					end

					final_blocks = table.concat(final_blocks)
					sha1_feed_64(H, final_blocks, 0, #final_blocks)
					for j = 1, 5 do
						H[j] = string.format("%08x", H[j] % 4294967296)
					end

					H = table.concat(H)
				end

				return H
			end
		end

		if message then
			return partial(message)()
		else
			return partial
		end
	end

	local function keccak(block_size_in_bytes, digest_size_in_bytes, is_SHAKE, message)
		if type(digest_size_in_bytes) ~= "number" then
			error("Argument 'digest_size_in_bytes' must be a number", 2)
		end
		local tail, lanes_lo, lanes_hi = "", table.create(25, 0), hi_factor_keccak == 0 and table.create(25, 0)
		local result
		local function partial(message_part)
			if message_part then
				local partLength = #message_part
				if tail then
					local offs = 0
					if tail ~= "" and #tail + partLength >= block_size_in_bytes then
						offs = block_size_in_bytes - #tail
						keccak_feed(lanes_lo, lanes_hi, tail .. string.sub(message_part, 1, offs), 0, block_size_in_bytes, block_size_in_bytes)
						tail = ""
					end

					local size = partLength - offs
					local size_tail = size % block_size_in_bytes
					keccak_feed(lanes_lo, lanes_hi, message_part, offs, size - size_tail, block_size_in_bytes)
					tail = tail .. string.sub(message_part, partLength + 1 - size_tail)
					return partial
				else
					error("Adding more chunks is not allowed after receiving the result", 2)
				end
			else
				if tail then
					local gap_start = is_SHAKE and 31 or 6
					tail = tail .. (#tail + 1 == block_size_in_bytes and string.char(gap_start + 128) or string.char(gap_start) .. string.rep("\0", (-2 - #tail) % block_size_in_bytes) .. "\128")
					keccak_feed(lanes_lo, lanes_hi, tail, 0, #tail, block_size_in_bytes)
					tail = nil

					local lanes_used = 0
					local total_lanes = math.floor(block_size_in_bytes / 8)
					local qwords = table.create(0)

					local function get_next_qwords_of_digest(qwords_qty)
						if lanes_used >= total_lanes then
							keccak_feed(lanes_lo, lanes_hi, "\0\0\0\0\0\0\0\0", 0, 8, 8)
							lanes_used = 0
						end

						qwords_qty = math.floor(math.min(qwords_qty, total_lanes - lanes_used))
						if hi_factor_keccak ~= 0 then
							for j = 1, qwords_qty do
								qwords[j] = HEX64(lanes_lo[lanes_used + j - 1 + lanes_index_base])
							end
						else
							for j = 1, qwords_qty do
								qwords[j] = string.format("%08x", lanes_hi[lanes_used + j] % 4294967296) .. string.format("%08x", lanes_lo[lanes_used + j] % 4294967296)
							end
						end

						lanes_used = lanes_used + qwords_qty
						return string.gsub(table.concat(qwords, "", 1, qwords_qty), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"), qwords_qty * 8
					end

					local parts = table.create(0) -- digest parts
					local last_part, last_part_size = "", 0

					local function get_next_part_of_digest(bytes_needed)
						bytes_needed = bytes_needed or 1
						if bytes_needed <= last_part_size then
							last_part_size = last_part_size - bytes_needed
							local part_size_in_nibbles = bytes_needed * 2
							local result = string.sub(last_part, 1, part_size_in_nibbles)
							last_part = string.sub(last_part, part_size_in_nibbles + 1)
							return result
						end

						local parts_qty = 0
						if last_part_size > 0 then
							parts_qty = 1
							parts[parts_qty] = last_part
							bytes_needed = bytes_needed - last_part_size
						end
						while bytes_needed >= 8 do
							local next_part, next_part_size = get_next_qwords_of_digest(bytes_needed / 8)
							parts_qty = parts_qty + 1
							parts[parts_qty] = next_part
							bytes_needed = bytes_needed - next_part_size
						end

						if bytes_needed > 0 then
							last_part, last_part_size = get_next_qwords_of_digest(1)
							parts_qty = parts_qty + 1
							parts[parts_qty] = get_next_part_of_digest(bytes_needed)
						else
							last_part, last_part_size = "", 0
						end

						return table.concat(parts, "", 1, parts_qty)
					end

					if digest_size_in_bytes < 0 then
						result = get_next_part_of_digest
					else
						result = get_next_part_of_digest(digest_size_in_bytes)
					end

				end

				return result
			end
		end

		if message then
			return partial(message)()
		else
			return partial
		end
	end

	local function HexToBinFunction(hh)
		return string.char(tonumber(hh, 16))
	end

	local function hex2bin(hex_string)
		return (string.gsub(hex_string, "%x%x", HexToBinFunction))
	end

	local base64_symbols = {
		["+"] = 62, ["-"] = 62, [62] = "+";
		["/"] = 63, ["_"] = 63, [63] = "/";
		["="] = -1, ["."] = -1, [-1] = "=";
	}

	local symbol_index = 0
	for j, pair in {"AZ", "az", "09"} do
		for ascii = string.byte(pair), string.byte(pair, 2) do
			local ch = string.char(ascii)
			base64_symbols[ch] = symbol_index
			base64_symbols[symbol_index] = ch
			symbol_index = symbol_index + 1
		end
	end

	local function bin2base64(binary_string)
		local stringLength = #binary_string
		local result = table.create(math.ceil(stringLength / 3))
		local length = 0

		for pos = 1, #binary_string, 3 do
			local c1, c2, c3, c4 = string.byte(string.sub(binary_string, pos, pos + 2) .. '\0', 1, -1)
			length = length + 1
			result[length] =
				base64_symbols[math.floor(c1 / 4)] ..
				base64_symbols[c1 % 4 * 16 + math.floor(c2 / 16)] ..
				base64_symbols[c3 and c2 % 16 * 4 + math.floor(c3 / 64) or -1] ..
				base64_symbols[c4 and c3 % 64 or -1]
		end

		return table.concat(result)
	end

	local function base642bin(base64_string)
		local result, chars_qty = table.create(0), 3
		for pos, ch in string.gmatch(string.gsub(base64_string, "%s+", ""), "()(.)") do
			local code = base64_symbols[ch]
			if code < 0 then
				chars_qty = chars_qty - 1
				code = 0
			end

			local idx = pos % 4
			if idx > 0 then
				result[-idx] = code
			else
				local c1 = result[-1] * 4 + math.floor(result[-2] / 16)
				local c2 = (result[-2] % 16) * 16 + math.floor(result[-3] / 4)
				local c3 = (result[-3] % 4) * 64 + code
				result[#result + 1] = string.sub(string.char(c1, c2, c3), 1, chars_qty)
			end
		end

		return table.concat(result)
	end

	local block_size_for_HMAC
	local BinaryStringMap = table.create(0)
	for Index = 0, 255 do
		BinaryStringMap[string.format("%02x", Index)] = string.char(Index)
	end
	local function hmac(hash_func, key, message, AsBinary)
		local block_size = block_size_for_HMAC[hash_func]
		if not block_size then
			error("Unknown hash function", 2)
		end

		local KeyLength = #key
		if KeyLength > block_size then
			key = string.gsub(hash_func(key), "%x%x", HexToBinFunction)
			KeyLength = #key
		end

		local append = hash_func()(string.gsub(key, ".", function(c)
			return string.char(bit32_bxor(string.byte(c), 0x36))
		end) .. string.rep("6", block_size - KeyLength))

		local result

		local function partial(message_part)
			if not message_part then
				result = result or hash_func(
					string.gsub(key, ".", function(c)
						return string.char(bit32_bxor(string.byte(c), 0x5c))
					end) .. string.rep("\\", block_size - KeyLength)
						.. (string.gsub(append(), "%x%x", HexToBinFunction))
				)

				return result
			elseif result then
				error("Adding more chunks is not allowed after receiving the result", 2)
			else
				append(message_part)
				return partial
			end
		end
		if message then local FinalMessage = partial(message)()return AsBinary and (string.gsub(FinalMessage, "%x%x", BinaryStringMap)) or FinalMessage else return partial end end

	local sha = {md5 = md5,sha1 = sha1,sha224 = function(message)return sha256ext(224, message)end;sha256 = function(message)return sha256ext(256, message)end;sha512_224 = function(message)return sha512ext(224, message)end;sha512_256 = function(message)return sha512ext(256, message)end;sha384 = function(message)return sha512ext(384, message)end;sha512 = function(message)return sha512ext(512, message)end;sha3_224 = function(message)return keccak((1600 - 2 * 224) / 8, 224 / 8, false, message)end;sha3_256 = function(message)return keccak((1600 - 2 * 256) / 8, 256 / 8, false, message)end;sha3_384 = function(message)return keccak((1600 - 2 * 384) / 8, 384 / 8, false, message)end;sha3_512 = function(message)return keccak((1600 - 2 * 512) / 8, 512 / 8, false, message)end;shake128 = function(message, digest_size_in_bytes)return keccak((1600 - 2 * 128) / 8, digest_size_in_bytes, true, message)end;shake256 = function(message, digest_size_in_bytes)return keccak((1600 - 2 * 256) / 8, digest_size_in_bytes, true, message)end;hmac = hmac;hex_to_bin = hex2bin;base64_to_bin = base642bin;bin_to_base64 = bin2base64;}

	block_size_for_HMAC = {
		[sha.md5] = 64;
		[sha.sha1] = 64;
		[sha.sha224] = 64;
		[sha.sha256] = 64;
		[sha.sha512_224] = 128;
		[sha.sha512_256] = 128;
		[sha.sha384] = 128;
		[sha.sha512] = 128;
		[sha.sha3_224] = (1600 - 2 * 224) / 8;
		[sha.sha3_256] = (1600 - 2 * 256) / 8;
		[sha.sha3_384] = (1600 - 2 * 384) / 8;
		[sha.sha3_512] = (1600 - 2 * 512) / 8;
	}
	local hashlib = sha
	crypt.hash = function(data, algorithm)
		return hashlib[string.gsub(algorithm, "-", "_")](data)
	end
	crypt.hmac = function(data, key, asBinary)
		return hashlib.hmac(hashlib.sha512_256, data, key, asBinary)
	end
	crypt.generatebytes = function(size)
		local bytes = table.create(size)
		for i = 1, size do
			bytes[i] = string.char(math.random(0, 255))
		end

		return crypt.base64encode(table.concat(bytes))
	end
	crypt.generatekey = function()
		return crypt.generatebytes(32)
	end
	local s_box 	= { 99, 124, 119, 123, 242, 107, 111, 197,  48,   1, 103,  43, 254, 215, 171, 118, 202,130, 201, 125, 250,  89,  71, 240, 173, 212, 162, 175, 156, 164, 114, 192, 183, 253, 147,  38,  54,63, 247, 204,  52, 165, 229, 241, 113, 216,  49,  21,   4, 199,  35, 195,  24, 150,   5, 154,   7,18, 128, 226, 235,  39, 178, 117,   9, 131,  44,  26,  27, 110,  90, 160,  82,  59, 214, 179,  41,227,  47, 132,  83, 209,   0, 237,  32, 252, 177,  91, 106, 203, 190,  57,  74,  76,  88, 207, 208,239, 170, 251,  67,  77,  51, 133,  69, 249,   2, 127,  80,  60, 159, 168,  81, 163,  64, 143, 146,157,  56, 245, 188, 182, 218,  33,  16, 255, 243, 210, 205,  12,  19, 236,  95, 151,  68,  23, 196,167, 126,  61, 100,  93,  25, 115,  96, 129,  79, 220,  34,  42, 144, 136,  70, 238, 184,  20, 222,94,  11, 219, 224,  50,  58,  10,  73,   6,  36,  92, 194, 211, 172,  98, 145, 149, 228, 121, 231,200,  55, 109, 141, 213,  78, 169, 108,  86, 244, 234, 101, 122, 174,   8, 186, 120,  37,  46,  28,166, 180, 198, 232, 221, 116,  31,  75, 189, 139, 138, 112,  62, 181, 102,  72,   3, 246,  14,  97,53,  87, 185, 134, 193,  29, 158, 225, 248, 152,  17, 105, 217, 142, 148, 155,  30, 135, 233, 206,85,  40, 223, 140, 161, 137,  13, 191, 230,  66, 104,  65, 153,  45,  15, 176,  84, 187,  22}
	local inv_s_box = {82,9,106,213,48,54,165,56,191,64,163,158,129,243,215,251,124,227,57,130,155,47,255,135,52,142,67,68,196,222,233,203,84,123,148,50,166,194,35,61,238,76,149,11,66,250,195,78,8,46,161,102,40,217,36,178,118,91,162,73,109,139,209,37,114,248,246,100,134,104,152,22,212,164,92,204,93,101,182,146,108,112,72,80,253,237,185,218,94,21,70,87,167,141,157,132,144,216,171,0,140,188,211,10,247,228,88,5,184,179,69,6,208,44,30,143,202,63,15,2,193,175,189,3,1,19,138,107,58,145,17,65,79,103,220,234,151,242,207,206,240,180,230,115,150,172,116,34,231,173,53,133,226,249,55,232,28,117,223,110,71,241,26,113,29,41,197,137,111,183,98,14,170,24,190,27,252,86,62,75,198,210,121,32,154,219,192,254,120,205,90,244,31,221,168,51,136,7,199,49,177,18,16,89,39,128,236,95,96,81,127,169,25,181,74,13,45,229,122,159,147,201,156,239,160,224,59,77,174,42,245,176,200,235,187,60,131,83,153,97,23,43,4,126,186,119,214,38,225,105,20,99,85,33,12,125}
	local rcon = {  0,   1,   2,   4,   8,  16,  32,  64, 128,  27,  54, 108, 216, 171,  77, 154,  47,  94,188,  99, 198, 151,  53, 106, 212, 179, 125, 250, 239, 197, 145,  57}
	local function xtime(x)
		local i = bit32.lshift(x, 1)
		return if bit32.band(x, 128) == 0 then i else bit32.bxor(i, 27) % 256
	end

	local function subBytes		(s, inv)
		inv = if inv then inv_s_box else s_box
		for i = 1, 4 do
			for j = 1, 4 do
				s[i][j] = inv[s[i][j] + 1]
			end
		end
	end
	local function shiftRows		(s, inv) 	-- Processes State by circularly shifting rows
		s[1][3], s[2][3], s[3][3], s[4][3] = s[3][3], s[4][3], s[1][3], s[2][3]
		if inv then
			s[1][2], s[2][2], s[3][2], s[4][2] = s[4][2], s[1][2], s[2][2], s[3][2]
			s[1][4], s[2][4], s[3][4], s[4][4] = s[2][4], s[3][4], s[4][4], s[1][4]
		else
			s[1][2], s[2][2], s[3][2], s[4][2] = s[2][2], s[3][2], s[4][2], s[1][2]
			s[1][4], s[2][4], s[3][4], s[4][4] = s[4][4], s[1][4], s[2][4], s[3][4]
		end
	end
	local function addRoundKey	(s, k) 			-- Processes Cipher by adding a round key to the State
		for i = 1, 4 do
			for j = 1, 4 do
				s[i][j] = bit32.bxor(s[i][j], k[i][j])
			end
		end
	end
	local function mixColumns	(s, inv) 		-- Processes Cipher by taking and mixing State columns
		local t, u
		if inv then
			for i = 1, 4 do
				t = xtime(xtime(bit32.bxor(s[i][1], s[i][3])))
				u = xtime(xtime(bit32.bxor(s[i][2], s[i][4])))
				s[i][1], s[i][2] = bit32.bxor(s[i][1], t), bit32.bxor(s[i][2], u)
				s[i][3], s[i][4] = bit32.bxor(s[i][3], t), bit32.bxor(s[i][4], u)
			end
		end

		local i
		for j = 1, 4 do
			i = s[j]
			t, u = bit32.bxor		(i[1], i[2], i[3], i[4]), i[1]
			for k = 1, 4 do
				i[k] = bit32.bxor	(i[k], t, xtime(bit32.bxor(i[k], i[k + 1] or u)))
			end
		end
	end

	-- BYTE ARRAY UTILITIES
	local function bytesToMatrix	(t, c, inv) -- Converts a byte array to a 4x4 matrix
		if inv then
			table.move		(c[1], 1, 4, 1, t)
			table.move		(c[2], 1, 4, 5, t)
			table.move		(c[3], 1, 4, 9, t)
			table.move		(c[4], 1, 4, 13, t)
		else
			for i = 1, #c / 4 do
				table.clear	(t[i])
				table.move	(c, i * 4 - 3, i * 4, 1, t[i])
			end
		end

		return t
	end
	local function xorBytes		(t, a, b) 		-- Returns bitwise XOR of all their bytes
		table.clear		(t)

		for i = 1, math.min(#a, #b) do
			table.insert(t, bit32.bxor(a[i], b[i]))
		end
		return t
	end
	local function incBytes		(a, inv)		-- Increment byte array by one
		local o = true
		for i = if inv then 1 else #a, if inv then #a else 1, if inv then 1 else - 1 do
			if a[i] == 255 then
				a[i] = 0
			else
				a[i] += 1
				o = false
				break
			end
		end

		return o, a
	end

	-- MAIN ALGORITHM
	local function expandKey	(key) 				-- Key expansion
		local kc = bytesToMatrix(if #key == 16 then {table.create(0), table.create(0), table.create(0), table.create(0)} elseif #key == 24 then {table.create(0), table.create(0), table.create(0), table.create(0)
			, table.create(0), table.create(0)} else {table.create(0), table.create(0), table.create(0), table.create(0), table.create(0), table.create(0), table.create(0), table.create(0)}, key)
		local is = #key / 4
		local i, t, w = 2, table.create(0), nil

		while #kc < (#key / 4 + 7) * 4 do
			w = table.clone	(kc[#kc])
			if #kc % is == 0 then
				table.insert(w, table.remove(w, 1))
				for j = 1, 4 do
					w[j] = s_box[w[j] + 1]
				end
				w[1]	 = bit32.bxor(w[1], rcon[i])
				i 	+= 1
			elseif #key == 32 and #kc % is == 4 then
				for j = 1, 4 do
					w[j] = s_box[w[j] + 1]
				end
			end

			table.clear	(t)
			xorBytes	(w, table.move(w, 1, 4, 1, t), kc[#kc - is + 1])
			table.insert(kc, w)
		end

		table.clear		(t)
		for i = 1, #kc / 4 do
			table.insert(t, table.create(0))
			table.move	(kc, i * 4 - 3, i * 4, 1, t[#t])
		end
		return t
	end
	local function encrypt	(key, km, pt, ps, r)
		bytesToMatrix	(ps, pt)
		addRoundKey		(ps, km[1])

		for i = 2, #key / 4 + 6 do
			subBytes	(ps)
			shiftRows	(ps)
			mixColumns	(ps)
			addRoundKey	(ps, km[i])
		end
		subBytes		(ps)
		shiftRows		(ps)
		addRoundKey		(ps, km[#km])

		return bytesToMatrix(r, ps, true)
	end
	local function decrypt	(key, km, ct, cs, r)
		bytesToMatrix	(cs, ct)

		addRoundKey		(cs, km[#km])
		shiftRows		(cs, true)
		subBytes		(cs, true)
		for i = #key / 4 + 6, 2, - 1 do
			addRoundKey	(cs, km[i])
			mixColumns	(cs, true)
			shiftRows	(cs, true)
			subBytes	(cs, true)
		end

		addRoundKey		(cs, km[1])
		return bytesToMatrix(r, cs, true)
	end
	local function convertType	(a)
		if type(a) == "string" then
			local r = table.create(0)

			for i = 1, string.len(a), 7997 do
				table.move({string.byte(a, i, i + 7996)}, 1, 7997, i, r)
			end
			return r
		elseif type(a) == "table" then
			for _, i in a do
				assert(type(i) == "number" and math.floor(i) == i and 0 <= i and i < 256,
					"Unable to cast value to bytes")
			end
			return a
		else
			error("Unable to cast value to bytes")
		end
	end
	local function deepCopy(Original)
		local copy = table.create(0)
		for key, val in Original do
			local Type = typeof(val)
			if Type == "table" then
				val = deepCopy(val)
			end
			copy[key] = val
		end
		return copy
	end
	local function init			(key, txt, m, iv, s) 	-- Initializes functions if possible
		key = convertType(key)
		assert(#key == 16 or #key == 24 or #key == 32, "Key must be either 16, 24 or 32 bytes long")
		txt = convertType(txt)
		assert(#txt % (s or 16) == 0, "Input must be a multiple of " .. (if s then "segment size " .. s
			else "16") .. " bytes in length")
		if m then
			if type(iv) == "table" then
				iv = table.clone(iv)
				local l, e 		= iv.Length, iv.LittleEndian
				assert(type(l) == "number" and 0 < l and l <= 16,
					"Counter value length must be between 1 and 16 bytes")
				iv.Prefix 		= convertType(iv.Prefix or table.create(0))
				iv.Suffix 		= convertType(iv.Suffix or table.create(0))
				assert(#iv.Prefix + #iv.Suffix + l == 16, "Counter must be 16 bytes long")
				iv.InitValue 	= if iv.InitValue == nil then {1} else table.clone(convertType(iv.InitValue
				))
				assert(#iv.InitValue <= l, "Initial value length must be of the counter value")
				iv.InitOverflow = if iv.InitOverflow == nil then table.create(l, 0) else table.clone(
				convertType(iv.InitOverflow))
				assert(#iv.InitOverflow <= l,
					"Initial overflow value length must be of the counter value")
				for _ = 1, l - #iv.InitValue do
					table.insert(iv.InitValue, 1 + if e then #iv.InitValue else 0, 0)
				end
				for _ = 1, l - #iv.InitOverflow do
					table.insert(iv.InitOverflow, 1 + if e then #iv.InitOverflow else 0, 0)
				end
			elseif type(iv) ~= "function" then
				local i, t = if iv then convertType(iv) else table.create(16, 0), table.create(0)
				assert(#i == 16, "Counter must be 16 bytes long")
				iv = {Length = 16, Prefix = t, Suffix = t, InitValue = i,
					InitOverflow = table.create(16, 0)}
			end
		elseif m == false then
			iv 	= if iv == nil then  table.create(16, 0) else convertType(iv)
			assert(#iv == 16, "Initialization vector must be 16 bytes long")
		end
		if s then
			s = math.floor(tonumber(s) or 1)
			assert(type(s) == "number" and 0 < s and s <= 16, "Segment size must be between 1 and 16 bytes"
			)
		end

		return key, txt, expandKey(key), iv, s
	end
	type bytes = {number} -- Type instance of a valid bytes object

	-- CIPHER MODES OF OPERATION
	local aes = {
		-- Electronic codebook (ECB)
		encrypt_ECB = function(key : bytes, plainText : bytes, initVector : bytes?) 									: bytes
			local km
			key, plainText, km, initVector = init(key, plainText, false, initVector)

			local iv = deepCopy(initVector)
			local b, k, s, t = table.create(0), table.create(0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #plainText, 16 do
				table.move(plainText, i, i + 15, 1, k)
				table.move(encrypt(key, km, k, s, t), 1, 16, i, b)
			end

			return b, iv
		end,
		decrypt_ECB = function(key : bytes, cipherText : bytes, initVector : bytes?) 								: bytes
			local km
			key, cipherText, km = init(key, cipherText, false, initVector)

			local b, k, s, t = table.create(0), table.create(0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #cipherText, 16 do
				table.move(cipherText, i, i + 15, 1, k)
				table.move(decrypt(key, km, k, s, t), 1, 16, i, b)
			end

			return b
		end,
		-- Cipher block chaining (CBC)
		encrypt_CBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
			local km
			key, plainText, km, initVector = init(key, plainText, false, initVector)
			local iv = deepCopy(initVector)
			local b, k, p, s, t = table.create(0), table.create(0), initVector, {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #plainText, 16 do
				table.move(plainText, i, i + 15, 1, k)
				table.move(encrypt(key, km, xorBytes(t, k, p), s, p), 1, 16, i, b)
			end

			return b, iv
		end,
		decrypt_CBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
			local km
			key, cipherText, km, initVector = init(key, cipherText, false, initVector)

			local b, k, p, s, t = table.create(0), table.create(0), initVector, {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #cipherText, 16 do
				table.move(cipherText, i, i + 15, 1, k)
				table.move(xorBytes(k, decrypt(key, km, k, s, t), p), 1, 16, i, b)
				table.move(cipherText, i, i + 15, 1, p)
			end

			return b
		end,
		-- Propagating cipher block chaining (PCBC)
		encrypt_PCBC = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
			local km
			key, plainText, km, initVector = init(key, plainText, false, initVector)
			local iv = deepCopy(initVector)
			local b, k, c, p, s, t = table.create(0), table.create(0), initVector, table.create(16, 0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #plainText, 16 do
				table.move(plainText, i, i + 15, 1, k)
				table.move(encrypt(key, km, xorBytes(k, xorBytes(t, c, k), p), s, c), 1, 16, i, b)
				table.move(plainText, i, i + 15, 1, p)
			end

			return b, iv
		end,
		decrypt_PCBC = function(key : bytes, cipherText : bytes, initVector : bytes?) 			: bytes
			local km
			key, cipherText, km, initVector = init(key, cipherText, false, initVector)

			local b, k, c, p, s, t = table.create(0), table.create(0), initVector, table.create(16, 0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #cipherText, 16 do
				table.move(cipherText, i, i + 15, 1, k)
				table.move(xorBytes(p, decrypt(key, km, k, s, t), xorBytes(k, c, p)), 1, 16, i, b)
				table.move(cipherText, i, i + 15, 1, c)
			end

			return b
		end,
		-- Cipher feedback (CFB)
		encrypt_CFB = function(key : bytes, plainText : bytes, initVector : bytes?, segmentSize : number?)
			: bytes
			local km
			key, plainText, km, initVector, segmentSize = init(key, plainText, false, initVector,
				if segmentSize == nil then 1 else segmentSize)
			local iv = deepCopy(initVector)
			local b, k, p, q, s, t = table.create(0), table.create(0), initVector, table.create(0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #plainText, segmentSize do
				table.move(plainText, i, i + segmentSize - 1, 1, k)
				table.move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
				for j = 16, segmentSize + 1, - 1 do
					table.insert(q, 1, p[j])
				end
				table.move(q, 1, 16, 1, p)
			end

			return b, iv
		end,
		decrypt_CFB = function(key : bytes, cipherText : bytes, initVector : bytes, segmentSize : number?)
			: bytes
			local km
			key, cipherText, km, initVector, segmentSize = init(key, cipherText, false, initVector,
				if segmentSize == nil then 1 else segmentSize)

			local b, k, p, q, s, t = table.create(0), table.create(0), initVector, table.create(0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #cipherText, segmentSize do
				table.move(cipherText, i, i + segmentSize - 1, 1, k)
				table.move(xorBytes(q, encrypt(key, km, p, s, t), k), 1, segmentSize, i, b)
				for j = 16, segmentSize + 1, - 1 do
					table.insert(k, 1, p[j])
				end
				table.move(k, 1, 16, 1, p)
			end

			return b
		end,
		-- Output feedback (OFB)
		encrypt_OFB = function(key : bytes, plainText : bytes, initVector : bytes?) 			: bytes
			local km
			key, plainText, km, initVector = init(key, plainText, false, initVector)
			local iv = deepCopy(initVector)
			local b, k, p, s, t = table.create(0), table.create(0), initVector, {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0)
			for i = 1, #plainText, 16 do
				table.move(plainText, i, i + 15, 1, k)
				table.move(encrypt(key, km, p, s, t), 1, 16, 1, p)
				table.move(xorBytes(t, k, p), 1, 16, i, b)
			end

			return b, iv
		end,
		-- Counter (CTR)
		encrypt_CTR = function(key : bytes, plainText : bytes, counter : ((bytes) -> bytes) | bytes | { [
			string]: any }?) : bytes
			local km
			key, plainText, km, counter = init(key, plainText, true, counter)
			local iv = deepCopy(counter)
			local b, k, c, s, t, r, n = table.create(0), table.create(0), table.create(0), {table.create(0), table.create(0), table.create(0), table.create(0)}, table.create(0), type(counter) == "table", nil
			for i = 1, #plainText, 16 do
				if r then
					if i > 1 and incBytes(counter.InitValue, counter.LittleEndian) then
						table.move(counter.InitOverflow, 1, 16, 1, counter.InitValue)
					end
					table.clear	(c)
					table.move	(counter.Prefix, 1, #counter.Prefix, 1, c)
					table.move	(counter.InitValue, 1, counter.Length, #c + 1, c)
					table.move	(counter.Suffix, 1, #counter.Suffix, #c + 1, c)
				else
					n = convertType(counter(c, (i + 15) / 16))
					assert		(#n == 16, "Counter must be 16 bytes long")
					table.move	(n, 1, 16, 1, c)
				end
				table.move(plainText, i, i + 15, 1, k)
				table.move(xorBytes(c, encrypt(key, km, c, s, t), k), 1, 16, i, b)
			end

			return b, iv
		end
	} -- Returns the library
	local modes = table.create(0)

	for _, ciphermode in { "ECB", "CBC", "PCBC", "CFB", "OFB", "CTR" } do -- Missing: GCM (important)
		local encrypt = aes["encrypt_" .. ciphermode]
		local decrypt = aes["decrypt_" .. ciphermode]

		modes[string.lower(ciphermode)] = { encrypt = encrypt, decrypt = decrypt or encrypt }
	end

	-- Function to add PKCS#7 padding to a string
	local function PKCS7_unpad(inputString)
		local blockSize = 16
		local length = (#inputString % blockSize)

		-- Only add padding if needed
		if 0 == length then
			return inputString
		end

		local paddingSize = blockSize - length

		local padding = string.rep(string.char(paddingSize), paddingSize)
		return inputString .. padding
	end

	-- Function to remove PKCS#7 padding from a padded string
	local function PKCS7_pad(paddedString)
		local lastByte = string.byte(paddedString, -1)

		-- Check if padding is present
		if lastByte <= 16 and 0 < lastByte then
			return string.sub(paddedString, 1, -lastByte - 1)
		else
			return paddedString
		end
	end

	local function table_type(t)
		local ct = 1
		for i in t do
			if i ~= ct then
				return "dictionary"
			end
			ct += 1
		end
		return "array"
	end

	local function bytes_to_char(t)
		return string.char(unpack(t))
	end

	local function crypt_generalized(action: string?)
		return function(data: string, key: string, iv: string?, mode: string?): (string, string)
			if mode and type(mode) == "string" then
				mode = string.lower(mode)
				mode = modes[mode]
			else
				mode = modes.cbc -- Default
			end

			if iv then
				iv = crypt.base64decode(iv)
				pcall(function()
					iv = game:GetService("HttpService"):JSONDecode(iv)
				end)
				if 16 < #iv then
					iv = string.sub(iv, 1, 16)
				elseif #iv < 16 then
					iv = PKCS7_unpad(iv)
				end
			end

			pcall(function()
				key = crypt.base64decode(key)
			end)

			-- TODO This code below is even worse
			local crypt_f = mode[action]
			data, iv = crypt_f(key, if action == "encrypt" then PKCS7_unpad(data) else crypt.base64decode(data), iv)

			data = bytes_to_char(data)

			if action == "decrypt" then
				data = PKCS7_pad(data)
			else
				if table_type(iv) == "array" then
					iv = bytes_to_char(iv)
				else
					iv = game:GetService("HttpService"):JSONEncode(iv)
				end
				iv = crypt.base64encode(iv)
				data = crypt.base64encode(data)
			end
			return data, iv
		end
	end
