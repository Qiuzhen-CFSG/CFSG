module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.CentralCover
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure

/-!
# Rigidity under every nine-group of root automorphisms

The diagonal E₉ is Sylow in the full automorphism group of UT₃(F₄).
Sylow conjugacy therefore transports its invariant-subgroup rigidity to
any subgroup of order nine, retaining its actual action on the root carrier.
No alignment of the original source actor with a chosen diagonal is assumed.

Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section

open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Four.RootNormalizerModel
open AutomizerConjugacy

theorem nine_invariant_eq_top (B : Subgroup (MulAut Root)) (hB : Nat.card B = 9)
    (A : Subgroup Root)
    (hinv : ∀ b ∈ B, ∀ q ∈ A, b q ∈ A)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨T, hT⟩ := torus_sylow
  obtain ⟨S, hBS⟩ := (IsPGroup.of_card (p := 3) (n := 2) hB).exists_le_sylow
  have hS : Nat.card (S : Subgroup (MulAut Root)) = 9 := by
    calc _ = Nat.card (T : Subgroup (MulAut Root)) := Nat.card_congr (S.equiv T).toEquiv
         _ = 9 := by rw [hT, torus_card]
  have hBE : B = S := eq_of_le_of_card_ge hBS (by rw [hB, hS])
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (MulAut Root) S T
  have htorus : B.map (MulAut.conj a).toMonoidHom = diagonalHom.range := by
    rw [hBE]
    change (↑(a • S) : Subgroup (MulAut Root)) = diagonalHom.range
    rw [ha, hT]
  have hi : ∀ d : Fˣ × Fˣ, ∀ q ∈ A.map a.toMonoidHom,
      diagonal d q ∈ A.map a.toMonoidHom := by
    intro d q hq
    obtain ⟨q, hq, rfl⟩ := hq
    have hm : diagonal d ∈ B.map (MulAut.conj a).toMonoidHom :=
      htorus ▸ (show diagonal d ∈ diagonalHom.range from ⟨d, rfl⟩)
    obtain ⟨b, hb, he⟩ := hm
    refine ⟨b q, hinv b hb q hq, ?_⟩
    have ht := congrArg (fun t : MulAut Root => t (a q)) he
    change a (b (a.symm (a q))) = diagonal d (a q) at ht
    rw [a.symm_apply_apply] at ht
    exact ht
  have hne' : ¬ IsElementaryAbelian 2 (A.map a.toMonoidHom) := by
    intro he
    let := he
    exact hne (IsElementaryAbelian.of_injective
      (A.equivMapOfInjective a.toMonoidHom a.injective).toMonoidHom
      (A.equivMapOfInjective a.toMonoidHom a.injective).injective)
  have he := diagonal_invariant_eq_top (A.map a.toMonoidHom) hi hne'
  have hh := congrArg (Subgroup.comap a.toMonoidHom) he
  simpa only [comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective, comap_top] using hh

/-- The same arbitrary-nine action result lifts through the genuine central
derived kernel whenever elementary subgroup preimages are elementary. -/
theorem nine_invariant_cover_eq_top {P : Type*} [Group P]
    (f : P →* Root) (hc : f.ker ≤ center P)
    (hd : f.ker ≤ _root_.commutator P)
    (hlift : ∀ W : Subgroup Root, IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap f))
    (B : Subgroup (MulAut Root)) (hB : Nat.card B = 9) (A : Subgroup P)
    (hinv : ∀ b ∈ B, ∀ q ∈ A.map f, b q ∈ A.map f)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  have hneImage : ¬ IsElementaryAbelian 2 (A.map f) := by
    intro he
    let := hlift (A.map f) he
    exact hne (IsElementaryAbelian.of_injective
      (Subgroup.inclusion (le_comap_map f A)) (Subgroup.inclusion_injective _))
  exact eq_top_of_map_eq_top_of_central_derived_kernel f hc hd A
    (nine_invariant_eq_top B hB (A.map f) hinv hneImage)
end Matrix.PSL3Four.RootNormalizerModel
