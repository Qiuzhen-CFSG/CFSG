module

public import Theory.SpecificGroups.Lyons.GebhardtPresentation
public import Mathlib.Tactic.Group

/-!
# Signed strings for the literal relators

These short strings are the freely reduced 25 literal source relators.
The list equality below proves their agreement in the free group;
the expression parser used to generate them is not trusted.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333-338,
Section 3B; original ATLAS matrices in `Atlas111Source/`. Generated
by `GebhardtMatrixSource/GenerateCertificateInputs.py`.
-/

namespace Lyons.Gebhardt.MatrixRealization.CertificateInputs

-- Each generated relation uses the same finite normalization rules.
set_option linter.unusedSimpArgs false

/-- Signed strings in source order: nine parabolic, seven local, nine outer. -/
@[expose] public def relatorStrings : List String := [
  "aaaaaaaa",
  "bbbbb",
  "abababab",
  "AABaab",
  "ABabABabABab",
  "ccccc",
  "AAcaaCCC",
  "ABcbabCBCBAACaab",
  "BBcbccbbCBCC",
  "DaBadAAAAAbA",
  "DbbAdaBBaa",
  "DCDbaCbaBBadcdcABCbCAbbAbaBa",
  "DCDaaCbaCbABdcdBBCbCbabaa",
  "DCBaCDbbacbadcAbcdABcbaCbbabaBa",
  "DCBaCDaCCbdcAbcdbACbAbcBBaaaa",
  "cACaCAcaDCACacAcdcaCACacd",
  "Zazaaa",
  "ZDZazdzAAA",
  "ZDZCDcbabbcbcbCdzdzBaBCdcdADCBBCdCaCbbcBcACdBcACCBc",
  "ZDCdCbAbcDcdCdbABcdzDCbaBDcDCdCBaBcDcdcbCB",
  "ZbDZazdBzabDcaCbCBBaCbAccBcda",
  "ZbDZCADCbaBaCbcaCDcdacBabaczdBzaCDBABcdcbDcaCbCBBcAcDcbbcaaaCa",
  "ZDCDZAbdcABabACBcazdcdzbaBcdCabcBAAAc",
  "ZDCDZDcbABzdcdzAcbcACdBAbabcACBcABaCA",
  "aDCbAADCBBCdCaCaCbAccBcDcacBaDZbzBz"]

set_option maxRecDepth 10000 in
private theorem string00_eq : word "aaaaaaaa" = word "a" ^ 8 := by
  change (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = ((FreeGroup.of (0 : Alphabet))) ^ 8
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string01_eq : word "bbbbb" = word "b" ^ 5 := by
  change (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) = ((FreeGroup.of (1 : Alphabet))) ^ 5
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string02_eq : word "abababab" = word "ab" ^ 4 := by
  change (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) = ((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))) ^ 4
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string03_eq : word "AABaab" = commutatorWord (word "aa") (word "b") := by
  change (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) = commutatorWord (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (1 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string04_eq : word "ABabABabABab" = commutatorWord (word "a") (word "b") ^ 3 := by
  change (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) = commutatorWord (((FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (1 : Alphabet)))) ^ 3
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string05_eq : word "ccccc" = word "c" ^ 5 := by
  change (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) = ((FreeGroup.of (2 : Alphabet))) ^ 5
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string06_eq : word "AAcaaCCC" = equationRelator (conjugate (word "c") (word "aa")) (word "ccc") := by
  change (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ = equationRelator (conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet))))) (((FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string07_eq : word "ABcbabCBCBAACaab" = equationRelator (conjugate (word "c") (word "ba")) (conjugate (word "c") (word "aab") * word "cb cB") := by
  change (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))))) (conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)))) * ((FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string08_eq : word "BBcbccbbCBCC" = equationRelator (conjugate (word "c") (word "bb")) (word "cc" * conjugate (word "c") (word "B") *
    (conjugate (word "c") (word "b"))⁻¹ ^ 2) := by
  change (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ = equationRelator (conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet))))) (((FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet))) * conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (1 : Alphabet))⁻¹)) *
    (conjugate (((FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (1 : Alphabet)))))⁻¹ ^ 2)
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string09_eq : word "DaBadAAAAAbA" = equationRelator (conjugate (word "aBa") (word "d")) (word "aBaaaaa") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string10_eq : word "DbbAdaBBaa" = equationRelator (conjugate (word "bbA") (word "d")) (word "AAbbA") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹)) (((FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string11_eq : word "DCDbaCbaBBadcdcABCbCAbbAbaBa" = equationRelator (conjugate (word "baCbaBBa") (word "dcd")) (word "AbABaBBa cBcbaC") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string12_eq : word "DCDaaCbaCbABdcdBBCbCbabaa" = equationRelator (conjugate (word "aaCbaCbAB") (word "dcd")) (word "AABA BcBcbb") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹)) (((FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string13_eq : word "DCBaCDbbacbadcAbcdABcbaCbbabaBa" = equationRelator (conjugate (word "bbacba") (word "dcAbcd")) (word "AbABA BBcABCba") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string14_eq : word "DCBaCDaCCbdcAbcdbACbAbcBBaaaa" = equationRelator (conjugate (word "aCCb") (word "dcAbcd")) (word "AAAAbb CBaBcaB") := by
  change (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)))) (((FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string15_eq : word "cACaCAcaDCACacAcdcaCACacd" = word "cACaCAcaDCACacAcdcaCACacd" := by
  change (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) = ((FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string16_eq : word "Zazaaa" = equationRelator (conjugate (word "a") (word "z")) (word "AAA") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (4 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string17_eq : word "ZDZazdzAAA" = equationRelator (conjugate (word "a") (word "zdz")) (word "aaa") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet))))) (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string18_eq : word "ZDZCDcbabbcbcbCdzdzBaBCdcdADCBBCdCaCbbcBcACdBcACCBc" = equationRelator (conjugate (word "CDcbabb cbcbCd") (word "zdz"))
    (word "Cbcc aCbDca CbCBB cA cDcbb cdaDCDcbAb") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)))) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)))))
    (((FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string19_eq : word "ZDCdCbAbcDcdCdbABcdzDCbaBDcDCdCBaBcDcdcbCB" = equationRelator (commutatorWord (word "z") (word "DCbaBDcDCdCBaB cDcd")) (word "bcBC") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ = equationRelator (commutatorWord (((FreeGroup.of (4 : Alphabet)))) (((FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))))) (((FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string20_eq : word "ZbDZazdBzabDcaCbCBBaCbAccBcda" = equationRelator (conjugate (word "a") (word "zdBz")) (word "ADC bCC aB cAbb cB cACdBA") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))))) (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string21_eq : word "ZbDZCADCbaBaCbcaCDcdacBabaczdBzaCDBABcdcbDcaCbCBBcAcDcbbcaaaCa" = equationRelator (conjugate (word "CADCbaBaC bcaCDcdacBabac") (word "zdBz"))
    (word "AcAAA CBBCdCa Cbb cBcACdBCDCbabdcA") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)))) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)))))
    (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string22_eq : word "ZDCDZAbdcABabACBcazdcdzbaBcdCabcBAAAc" = equationRelator (conjugate (word "AbdcABabACBca") (word "zdcdz")) (word "CaaabCB A cDCbAB") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) = equationRelator (conjugate (((FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)))) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet))))) (((FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string23_eq : word "ZDCDZDcbABzdcdzAcbcACdBAbabcACBcABaCA" = equationRelator (conjugate (word "DcbAB") (word "zdcdz")) (word "acAbaCbcaCBABabDcaCBCa") := by
  change (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ = equationRelator (conjugate (((FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹)) (((FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (4 : Alphabet))))) (((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
private theorem string24_eq : word "aDCbAADCBBCdCaCaCbAccBcDcacBaDZbzBz" = word "aDCbAA DCBB CdC aCaC bAccB cDca cBaD ZbzBz" := by
  change (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)) = ((FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (3 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (0 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (2 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (0 : Alphabet)) * (FreeGroup.of (3 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet))⁻¹ * (FreeGroup.of (1 : Alphabet)) * (FreeGroup.of (4 : Alphabet)) * (FreeGroup.of (1 : Alphabet))⁻¹ * (FreeGroup.of (4 : Alphabet)))
  simp only [conjugate, commutatorWord, equationRelator, pow_succ, pow_zero,
    mul_one, one_mul, mul_inv_rev, inv_inv]
  try group

set_option maxRecDepth 10000 in
/-- Exact agreement with the authoritative free-group expressions. -/
public theorem relatorStrings_eq :
    relatorStrings.map word = parabolicRelators ++ localRelators ++ outerRelators := by
  simp only [relatorStrings, parabolicRelators, localRelators, outerRelators,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    string00_eq, string01_eq, string02_eq, string03_eq, string04_eq, string05_eq, string06_eq, string07_eq, string08_eq, string09_eq, string10_eq, string11_eq, string12_eq, string13_eq, string14_eq, string16_eq, string17_eq, string18_eq, string19_eq, string20_eq, string21_eq, string22_eq, string23_eq, string24_eq]

end Lyons.Gebhardt.MatrixRealization.CertificateInputs
