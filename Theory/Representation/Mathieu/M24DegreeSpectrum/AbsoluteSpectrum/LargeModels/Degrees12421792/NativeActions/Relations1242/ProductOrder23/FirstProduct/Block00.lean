module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.SecondWide

/-!
# Rows 0–53 of the literal product A B

Kernel-checked base-2048 expansions and multiplication rows. Each checked
one-coordinate hint is part of the certificate, not an assumption.
The block is assembled in `ProductOrder23.FirstProduct`.
Source: ATLAS M24G1-f2r1242B0.m1/.m2; see ../source/README.md.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block00
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.Tables
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

def hints : List (Option Nat) := [some 1,some 0,some 4,some 5,some 2,some 3,some 8,some 9,some 6,some 7,some 13,some 14,some 16,some 10,some 11,some 20,some 12,some 22,some 23,some 25,some 15,some 28,some 17,some 18,some 32,some 19,some 34,some 35,some 21,some 38,some 39,some 41,some 24,some 44,some 26,some 27,some 48,some 49,some 29,some 30,some 53,some 31,some 55,some 56,some 33,some 59,some 60,some 62,some 36,some 37,some 66,some 67,some 69,some 40]

set_option maxRecDepth 8192 in
private theorem expand00 : expandBlocks 18 69 (nat_lit 0x4) = nat_lit 0x400000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand01 : expandBlocks 18 69 (nat_lit 0x8) = nat_lit 0x200000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand02 : expandBlocks 18 69 (nat_lit 0xe) = nat_lit 0x200400800 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand03 : expandBlocks 18 69 (nat_lit 0x7) = nat_lit 0x400801 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand04 : expandBlocks 18 69 (nat_lit 0x40) = nat_lit 0x40000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand05 : expandBlocks 18 69 (nat_lit 0x80) = nat_lit 0x20000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand06 : expandBlocks 18 69 (nat_lit 0x50) = nat_lit 0x40000100000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand07 : expandBlocks 18 69 (nat_lit 0x400) = nat_lit 0x4000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand08 : expandBlocks 18 69 (nat_lit 0x800) = nat_lit 0x2000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand09 : expandBlocks 18 69 (nat_lit 0x1000) = nat_lit 0x1000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand10 : expandBlocks 18 69 (nat_lit 0x20) = nat_lit 0x80000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand11 : expandBlocks 18 69 (nat_lit 0x8000) = nat_lit 0x200000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand12 : expandBlocks 18 69 (nat_lit 0x20000) = nat_lit 0x80000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand13 : expandBlocks 18 69 (nat_lit 0x40000) = nat_lit 0x40000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand14 : expandBlocks 18 69 (nat_lit 0x80000) = nat_lit 0x20000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand15 : expandBlocks 18 69 (nat_lit 0x100) = nat_lit 0x10000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand16 : expandBlocks 18 69 (nat_lit 0x200000) = nat_lit 0x8000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand17 : expandBlocks 18 69 (nat_lit 0x200) = nat_lit 0x8000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand18 : expandBlocks 18 69 (nat_lit 0x1000000) = nat_lit 0x1000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand19 : expandBlocks 18 69 (nat_lit 0x4000000) = nat_lit 0x400000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand20 : expandBlocks 18 69 (nat_lit 0x8000000) = nat_lit 0x200000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand21 : expandBlocks 18 69 (nat_lit 0x20000000) = nat_lit 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand22 : expandBlocks 18 69 (nat_lit 0x40000000) = nat_lit 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand23 : expandBlocks 18 69 (nat_lit 0x80000000) = nat_lit 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand24 : expandBlocks 18 69 (nat_lit 0x2000) = nat_lit 0x800000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand25 : expandBlocks 18 69 (nat_lit 0x200000000) = nat_lit 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand26 : expandBlocks 18 69 (nat_lit 0x4000) = nat_lit 0x400000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand27 : expandBlocks 18 69 (nat_lit 0x1000000000) = nat_lit 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand28 : expandBlocks 18 69 (nat_lit 0x2000000000) = nat_lit 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand29 : expandBlocks 18 69 (nat_lit 0x10000) = nat_lit 0x100000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand30 : expandBlocks 18 69 (nat_lit 0x10000000000) = nat_lit 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand31 : expandBlocks 18 69 (nat_lit 0x40000000000) = nat_lit 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand32 : expandBlocks 18 69 (nat_lit 0x80000000000) = nat_lit 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand33 : expandBlocks 18 69 (nat_lit 0x200000000000) = nat_lit 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand34 : expandBlocks 18 69 (nat_lit 0x400000000000) = nat_lit 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand35 : expandBlocks 18 69 (nat_lit 0x800000000000) = nat_lit 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand36 : expandBlocks 18 69 (nat_lit 0x100000) = nat_lit 0x10000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand37 : expandBlocks 18 69 (nat_lit 0x4000000000000) = nat_lit 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand38 : expandBlocks 18 69 (nat_lit 0x8000000000000) = nat_lit 0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand39 : expandBlocks 18 69 (nat_lit 0x10000000000000) = nat_lit 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand40 : expandBlocks 18 69 (nat_lit 0x400000) = nat_lit 0x4000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand41 : expandBlocks 18 69 (nat_lit 0x40000000000000) = nat_lit 0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand42 : expandBlocks 18 69 (nat_lit 0x800000) = nat_lit 0x2000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand43 : expandBlocks 18 69 (nat_lit 0x200000000000000) = nat_lit 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand44 : expandBlocks 18 69 (nat_lit 0x400000000000000) = nat_lit 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand45 : expandBlocks 18 69 (nat_lit 0x2000000) = nat_lit 0x800000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand46 : expandBlocks 18 69 (nat_lit 0x2000000000000000) = nat_lit 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand47 : expandBlocks 18 69 (nat_lit 0x8000000000000000) = nat_lit 0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand48 : expandBlocks 18 69 (nat_lit 0x10000000000000000) = nat_lit 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand49 : expandBlocks 18 69 (nat_lit 0x20000000000000000) = nat_lit 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand50 : expandBlocks 18 69 (nat_lit 0x10000000) = nat_lit 0x100000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand51 : expandBlocks 18 69 (nat_lit 0x100000000000000000) = nat_lit 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand52 : expandBlocks 18 69 (nat_lit 0x400000000000000000) = nat_lit 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem expand53 : expandBlocks 18 69 (nat_lit 0x800000000000000000) = nat_lit 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem wide_correct : bWideBlock00 = bBlock00.map (expandBlocks 18 69) := by
  simp only [bWideBlock00, bBlock00, List.map_cons, List.map_nil, expand00, expand01, expand02, expand03, expand04, expand05, expand06, expand07, expand08, expand09, expand10, expand11, expand12, expand13, expand14, expand15, expand16, expand17, expand18, expand19, expand20, expand21, expand22, expand23, expand24, expand25, expand26, expand27, expand28, expand29, expand30, expand31, expand32, expand33, expand34, expand35, expand36, expand37, expand38, expand39, expand40, expand41, expand42, expand43, expand44, expand45, expand46, expand47, expand48, expand49, expand50, expand51, expand52, expand53]

set_option maxRecDepth 8192 in
theorem checked : CF.check aBlock00 bRows bWideChunks c1Block00 hints = true := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct.Block00
