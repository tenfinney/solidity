/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Translates Yul code from EVM dialect to eWasm dialect.
 */

#include <libyul/backends/wasm/EVMToEWasmTranslator.h>

#include <libyul/backends/wasm/WordSizeTransform.h>
#include <libyul/backends/wasm/WasmDialect.h>
#include <libyul/optimiser/ExpressionSplitter.h>

#include <libyul/AsmParser.h>

#include <liblangutil/ErrorReporter.h>
#include <liblangutil/Scanner.h>

using namespace std;
using namespace dev;
using namespace yul;
using namespace langutil;

namespace
{
static string const polyfill{R"({
function or_bool(a, b, c, d) -> r {
	r := i64.ne(0, i64.or(i64.or(a, b), i64.or(c, d)))
}
function add_carry(x, y, c) -> r, r_c {
	let t := i64.add(x, y)
	r := i64.add(t, c)
	r_c := i64.or(
		i64.lt_u(t, x),
		i64.lt_u(r, t)
	)
}
function add(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	let carry
	r4, carry := add_carry(x4, y4, 0)
	r3, carry := add_carry(x3, y3, carry)
	r2, carry := add_carry(x2, y2, carry)
	r1, carry := add_carry(x1, y1, carry)
}
function bit_negate(x) -> y {
	y := i64.xor(x, 0xffffffffffffffff)
}
function sub(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	// x - y = x + (~y + 1)
	let carry
	r4, carry := add_carry(x4, bit_negate(y4), 1)
	// TODO check that add_carry also works correctly
	// with carry = 2
	r3, carry := add_carry(x3, bit_negate(y3), i64.add(carry, 1))
	r2, carry := add_carry(x2, bit_negate(y2), i64.add(carry, 1))
	r1, carry := add_carry(x1, bit_negate(y1), i64.add(carry, 1))
}
function byte(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	if i64.eqz(i64.or(i64.or(x1, x2), x3), 0) {
		let component
		switch i64.div_u(x4, 8)
		case 0 { component := y1 }
		case 1 { component := y2 }
		case 2 { component := y3 }
		case 3 { component := y4 }
		x4 := i64.mul(i64.rem_u(x4, 8), 8)
		r4 := shr_u(component, i64.sub(56, x4))
		r4 := i64.and(0xff, r4)
	}
}
function xor(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	r1 := i64.xor(x1, y1)
	r2 := i64.xor(x2, y2)
	r3 := i64.xor(x3, y3)
	r4 := i64.xor(x4, y4)
}
function or(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	r1 := i64.or(x1, y1)
	r2 := i64.or(x2, y2)
	r3 := i64.or(x3, y3)
	r4 := i64.or(x4, y4)
}
function and(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	r1 := i64.and(x1, y1)
	r2 := i64.and(x2, y2)
	r3 := i64.and(x3, y3)
	r4 := i64.and(x4, y4)
}
function not(x1, x2, x3, x4) -> r1, r2, r3, r4 {
	let mask := 0xffffffffffffffff
	r1, r2, r3, r4 := xor(x1, x2, x3, x4, mask, mask, mask, mask)
}
function iszero(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	r4 := i64.eqz(i64.or(i64.or(x1, x2), i64.or(x3, x4)))
}
function eq(x1, x2, x3, x4, y1, y2, y3, y4) -> r1, r2, r3, r4 {
	if i64.eq(x1, y1) {
		if i64.eq(x2, y2) {
			if i64.eq(x3, y3) {
				if i64.eq(x4, y4) {
					r4 := 1
				}
			}
		}
	}
}
function pop(x1, x2, x3, x4) {}
})"};

/*
 * To implement:
 * mul
 * div
 * sdiv
 * mod
 * smod
 * exp
 * lt
 * gt
 * slt
 * sgt
 * shl
 * shr
 * sar
 * addmod
 * mulmod
 * signextend
 * keccak256
 * address
 * balance
 * origin
 * caller
 * callvalue
 * calldataload
 * calldatasize
 * calldatacopy
 * codesize
 * codecopy
 * gasprice
 * extcodesize
 * extcodecopy
 * returndatasize
 * returndatacopy
 * extcodehash
 * blockhash
 * coinbase
 * timestamp
 * number
 * difficulty
 * gaslimit
 * mload
 * mstore
 * mstore8
 * sload
 * sstore
 * pc
 * msize
 * gas
 * log0
 * log1
 * log2
 * log3
 * log4
 * create
 * call
 * callcode
 * return
 * delegatecall
 * staticcall
 * create2
 * revert
 * invalid
 * selfdestruct
 *
 */

Block parsePolyfill()
{
	ErrorList errors;
	ErrorReporter errorReporter(errors);
	shared_ptr<WasmDialect> wasmDialect{make_shared<WasmDialect>()};
	shared_ptr<Scanner> scanner{make_shared<Scanner>(CharStream(polyfill, ""))};
	shared_ptr<Block> block = Parser(errorReporter, wasmDialect).parse(scanner, false);
	yulAssert(errors.empty(), "");
	return move(*block);
}
}
void EVMToEWasmTranslator::run(Dialect const& _evmDialect, Block& _ast)
{
	// TODO first parse the polyfill and then rename all functions
	// that clash with those in the polyfill.

	// TODO probably good to also run the function grouper
	// so that we can use arbitrary variables for function parameters.
	NameDispenser nameDispenser{_evmDialect, _ast};
	ExpressionSplitter{_evmDialect, nameDispenser}(_ast);
	WordSizeTransform::run(_ast, nameDispenser);
	_ast.statements += std::move(parsePolyfill().statements);
	// TODO re-parse?
}

