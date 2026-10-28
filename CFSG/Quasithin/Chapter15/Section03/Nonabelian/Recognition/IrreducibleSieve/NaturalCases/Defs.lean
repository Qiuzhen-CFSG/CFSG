module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Component
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Models

/-!
# The four natural-module alternatives in G.9.3

These alternatives identify the action of the component join `K`, while `H`
is the full extending actor. Every identification includes a group isomorphism
and an intertwining binary linear equivalence. The rank parameter is the
original actor rank. No local Chapter 15 hypotheses enter this definition.

SL₂ is the genuine even-characteristic natural model of L₂. SL₃ is retained
without taking its central quotient. Sp₄ and G₂ use their actual commutator
subgroups, including over the field of two elements.

Source: Aschbacher--Smith, G.9.3(6),(8),(9),(10), printed pp.353--357.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases

open Representation
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic

attribute [local instance] ZMod.algebra

universe u v f
variable {H : Type u} {W : Type v} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- Exactly the natural field-module branches, with valid field parameters,
the original rank bounds, and actual group-and-module identifications. -/
inductive Alternative (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop
  | rankOne {F : Type f} [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (parameter : 2 ≤ n) (field_card : Nat.card F = 2 ^ n)
      (dimension : Module.finrank (ZMod 2) W = 2 * n) (rank_bound : n - 1 ≤ m)
      (natural : Quasiequivalent (ρ.comp K.subtype) (SL2.BinarySmall.natural (K := F))) :
      Alternative ρ K m
  | linearThree {F : Type f} [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (parameter : 0 < n) (field_card : Nat.card F = 2 ^ n)
      (dimension : Module.finrank (ZMod 2) W = 3 * n) (rank_bound : 3 * n - 2 ≤ 2 * m)
      (natural : Quasiequivalent (ρ.comp K.subtype) (LinearThreeRecognition.naturalBinary F)) :
      Alternative ρ K m
  | symplecticFour {F : Type f} [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (parameter : 0 < n) (field_card : Nat.card F = 2 ^ n)
      (dimension : Module.finrank (ZMod 2) W = 4 * n) (rank_bound : 2 * n - 1 ≤ m)
      (natural : Quasiequivalent (ρ.comp K.subtype) (SymplecticFourRecognition.binaryNatural F)) :
      Alternative ρ K m
  | g2 {F : Type f} [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (parameter : 0 < n) (field_card : Nat.card F = 2 ^ n)
      (dimension : Module.finrank (ZMod 2) W = 6 * n) (rank_bound : 3 * n - 1 ≤ m)
      (natural : Quasiequivalent (ρ.comp K.subtype) (G2Recognition.derivedNaturalBinary F)) :
      Alternative ρ K m

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases
