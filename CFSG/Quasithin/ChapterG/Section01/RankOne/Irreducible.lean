module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import Theory.Representation.SL2.SylowFixedDimension
public import Theory.Representation.BinaryOffender.Defs

/-!
# Irreducible rank-one recognition from Sylow fixed spaces

The dimension fixed by a Sylow two-subgroup equals the actual Schur-field
degree. In the proved small-degree classifier, that excludes the Hermitian
and triple-tensor alternatives when the fixed dimension reaches the field
degree. Complementary Sylow fixed spaces give the same conclusion without
any dimension assumption: the whole dimension is twice the Schur degree,
and that degree divides the defining field degree.

This proves the irreducible slice of Aschbacher–Smith G.1.7 needed by the
equality case in E.2.15. It uses the independently proved highest-weight
recognition in G.9 and makes no direct-sum or extension-splitting assertion.
Source: printed pp.228 and 329–330.
-/

public section
open scoped MatrixGroups MonoidAlgebra
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section01.RankOne
variable {F U : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(2,F) U) [ρ.IsIrreducible]

theorem natural_of_minimal_degree_and_sylow_fixed
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (hn : ∃ g, ρ g ≠ 1) (R : Sylow 2 SL(2,F))
    (hd : Module.finrank (ZMod 2) U ≤ 2*m)
    (hfix : m ≤ Module.finrank (ZMod 2) (fixedSpace ρ (R : Subgroup _))) :
    Representation.SL2.BinarySmall.IsNatural ρ := by
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)
  have hs : m ≤ s := hfix.trans_eq
    (Representation.SL2.finrank_sylow_invariants_eq_endField 2 ρ R)
  rcases Section09.DefiningCharacteristic.binary_small_module_alternatives
    ρ hn m hm hcard (by omega) with h | h | h
  · exact h.2.2
  · change 2*s = m ∧ _ at h
    omega
  · change s = 1 ∧ _ at h
    omega

theorem natural_of_complementary_sylow_fixed
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (hn : ∃ g, ρ g ≠ 1) (R S : Sylow 2 SL(2,F))
    (hRS : IsCompl (fixedSpace ρ (R : Subgroup _)) (fixedSpace ρ (S : Subgroup _))) :
    Representation.SL2.BinarySmall.IsNatural ρ := by
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)
  have hR : Module.finrank (ZMod 2) (fixedSpace ρ (R : Subgroup _)) = s :=
    Representation.SL2.finrank_sylow_invariants_eq_endField 2 ρ R
  have hS : Module.finrank (ZMod 2) (fixedSpace ρ (S : Subgroup _)) = s :=
    Representation.SL2.finrank_sylow_invariants_eq_endField 2 ρ S
  have hd := Submodule.finrank_add_eq_of_isCompl hRS
  rw [hR,hS] at hd
  obtain ⟨_,w,_,hsdiv,_,_,_⟩ :=
    Section09.DefiningCharacteristic.exists_binary_highestWeight_parameters ρ hn m hcard
  have hsle : s ≤ m := Nat.le_of_dvd (by omega) hsdiv
  have hsmall : Module.finrank (ZMod 2) U ≤ 2*(m+1) := by omega
  rcases Section09.DefiningCharacteristic.binary_small_module_alternatives
    ρ hn m hm hcard hsmall with h | h | h
  · exact h.2.2
  · change 2*s = m ∧ _ at h
    omega
  · change s = 1 ∧ _ at h
    omega
end CFSG.Quasithin.ChapterG.Section01.RankOne
