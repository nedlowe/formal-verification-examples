// Calling the proven allocator from Node or TypeScript.
//
//   bend main.bend -o build/allocate.mjs
//   node node/example.mjs
//
// The proofs are about main.bend, so this is the same code the laws cover,
// compiled to JavaScript: amounts are plain numbers of minor units (cents),
// lists are Bend's cons cells, and a value past 2^48 - 1 throws rather than
// being rounded.

import Alloc from '../build/allocate.mjs'

const toList = (xs) => xs.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const toArray = (list) => {
  const out = []
  for (let l = list; l.$ === 'Con'; l = l.tail) out.push(l.head)
  return out
}

export const allocate = (totalMinorUnits, weights) =>
  toArray(Alloc.allocate(totalMinorUnits, toList(weights)))

console.log(allocate(10_000, [1, 1, 1])) // $100.00 three ways
console.log(allocate(123_456_789, [5_000, 12_500, 82_500])) // a dividend
console.log(allocate(500, [0, 1, 2])) // a zero-weight account

try {
  allocate(1_000_000_000_000, [1_000, 1_000]) // $10bn in cents x 1,000: past 2^48
} catch (error) {
  console.log('refused:', String(error))
}
