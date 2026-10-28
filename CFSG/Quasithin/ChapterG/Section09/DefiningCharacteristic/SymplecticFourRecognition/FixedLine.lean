module
public import Theory.Representation.SymplecticFixedLine
public import Theory.Representation.Quotient
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds

/-!
# Excluding a natural symplectic component with a binary fixed line

At the sharp G.9 degree, natural-module recognition forces Sp₄(4) and a
maximum-rank elementary actor. Thompson's inner-action theorem makes this
actor linear over the same coefficient field. Its nonzero fixed line would
then be a vector space over that field, contradicting its binary dimension.
All comparisons use the actual normal component and faithful quotient action.

Source: Aschbacher–Smith G.9.3 and G.11.8, printed pp.354–357,368–369.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.FixedLine
variable {D V K : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field K] [Finite K] [CharP K 2]

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open CFSG.Quasithin.ChapterG.Section09 Representation.SymplecticFixedLine

/-- The sharp G.9 degree and an actual binary fixed line exclude nonbinary
symplectic components, using the same natural coordinates and actor. -/
theorem not_natural_sharp_fixed_line
    {C : GroupClass} {ρ : Representation (ZMod 2) D V} {H A : Subgroup D} {m : ℕ}
    (h : ComponentHypothesis C ρ A H H m)
    (hd : Module.finrank (ZMod 2) V = m + 2)
    (e : H ≃* commutator (Matrix.symplecticGroup (Fin 2) K))
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (v : V) (hv : v ≠ 0)
    (hfix : BinaryOffender.fixedSpace ρ A = Submodule.span (ZMod 2) {v}) : False := by
  let : H.Normal := h.normal_H
  let : IsElementaryAbelian 2 A := h.elementary
  let : IsIrreducible (ρ.comp H.subtype) := h.irreducible
  let := ZMod.algebra K 2
  have hwindow := component_degree_window_of_automorphism_rank h e
    (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hK hn)
  let τ := (ρ.comp H.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hτ : Function.Injective τ :=
    (h.faithful.comp H.subtype_injective).comp e.symm.injective
  have hnatural := quasiequivalent_of_comp_equiv e
    (Nonbinary.small_quasiequivalent hn hK hτ hwindow.2)
  have hdim := finrank_of_quasiequivalent hK hnatural
  have hn2 : n = 2 := by omega
  have hm : m = 3*n := by omega
  obtain ⟨e',c,hc⟩ := hnatural
  let : Module K V := coordinateModule c
  have hsmul (a : K) (w : V) : c (a • w) = a • c w := c.apply_symm_apply _
  let : SMulCommClass K (ZMod 2) V := ⟨fun a b w => by
    apply c.injective
    simp only [hsmul,c.map_smul,smul_comm a b]⟩
  have hH : ∀ (x : H) (a : K) (w : V), ρ x (a • w) = a • ρ x w := by
    intro x a w
    apply c.injective
    change c (((ρ.comp H.subtype) x) (a • w)) = c (a • ((ρ.comp H.subtype) x) w)
    rw [hc,hsmul,hsmul,hc]
    exact (symplecticDerivedNatural 2 (e' x)).map_smul a (c w)
  let ef := e'.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hK hn)
  have hi := maximal_actor_inner ρ H A h.faithful ef hn hK (hm ▸ h.card_actor)
  have hlin := coefficient_linear_of_inner ρ H A ef hH hi
  have hb := card_le_two_of_fixed_line ρ A hlin v hv hfix
  rw [hK,hn2] at hb
  norm_num at hb

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.FixedLine
