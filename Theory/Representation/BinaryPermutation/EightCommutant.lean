module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# Rigidity of the binary natural A₈ action

An invertible linear map commuting with A₈ fixes a weight-two vector:
three explicit three-cycles have precisely its line as their common fixed
space. The natural A₈ action is irreducible, so the kernel of the difference
from the identity is the whole module. Thus the linear centralizer is trivial.

This lets a chosen component intertwiner extend to the full S₈ action without
changing its coordinates or assuming equivariance for the outside coset.
Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the paragraph following 13.6.23, printed p.933/PDF p.950; natural-module
irreducibility is B.3.1, printed p.83.
-/

@[expose] public section
open Representation BinaryPermutation Equiv
namespace BinaryPermutation.EightCommutant
private abbrev Ω := Fin 8
private def a : Perm Ω := swap 2 3 * swap 3 4
private def b : Perm Ω := swap 4 5 * swap 5 6
private def c : Perm Ω := swap 5 6 * swap 6 7
private def pair : core Ω := ⟨![1,1,0,0,0,0,0,0], by rw [mem_core]; decide⟩
private def p : natural Ω := coreToNatural Ω pair

private theorem pair_ne : p ≠ 0 := by
  intro h
  have hc : pair.val ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := (mem_constants_iff _).mp hc
  have h0 := ht 0
  have h2 := ht 2
  change (1 : ZMod 2) = t at h0
  change (0 : ZMod 2) = t at h2
  exact one_ne_zero (h0.trans h2.symm)

private theorem even : a ∈ alternatingGroup Ω ∧ b ∈ alternatingGroup Ω ∧
    c ∈ alternatingGroup Ω := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

private theorem fix : naturalRepresentation Ω a p = p ∧
    naturalRepresentation Ω b p = p ∧ naturalRepresentation Ω c p = p := by
  have ha : coreRepresentation Ω a pair = pair := by apply Subtype.ext; decide
  have hb : coreRepresentation Ω b pair = pair := by apply Subtype.ext; decide
  have hc : coreRepresentation Ω c pair = pair := by apply Subtype.ext; decide
  exact ⟨(coreToNatural_equivariant a pair).symm.trans (congrArg (coreToNatural Ω) ha),
    (coreToNatural_equivariant b pair).symm.trans (congrArg (coreToNatural Ω) hb),
    (coreToNatural_equivariant c pair).symm.trans (congrArg (coreToNatural Ω) hc)⟩

private theorem fixed_pair (x : natural Ω)
    (ha : naturalRepresentation Ω a x = x)
    (hb : naturalRepresentation Ω b x = x)
    (hc : naturalRepresentation Ω c x = x) : x = 0 ∨ x = p := by
  obtain ⟨w, rfl⟩ := coreToNatural_surjective x
  have lift (g : Perm Ω) (hg : g 0 = 0)
      (he : naturalRepresentation Ω g (coreToNatural Ω w) = coreToNatural Ω w) :
      representation Ω g w.val = w.val :=
    (deleted_fixed_iff_of_fixed_point g w.val 0 hg).mp (congrArg Subtype.val he)
  have ha' := lift a (by decide) ha
  have hb' := lift b (by decide) hb
  have hc' := lift c (by decide) hc
  have h23 := congrFun ha' 3
  have h34 := congrFun ha' 4
  have h45 := congrFun hb' 5
  have h56 := congrFun hb' 6
  have h67 := congrFun hc' 7
  change w.val 2 = w.val 3 at h23
  change w.val 3 = w.val 4 at h34
  change w.val 4 = w.val 5 at h45
  change w.val 5 = w.val 6 at h56
  change w.val 6 = w.val 7 at h67
  have hsum := w.property
  change ∑ i : Fin 8, w.val i = 0 at hsum
  have h01 : w.val 0 = w.val 1 := by
    simp only [Fin.sum_univ_succ] at hsum
    change w.val 0 + (w.val 1 + (w.val 2 + (w.val 3 + (w.val 4 +
      (w.val 5 + (w.val 6 + (w.val 7 + 0))))))) = 0 at hsum
    simp only [show w.val 3 = w.val 2 from h23.symm,
      show w.val 4 = w.val 2 from (h23.trans h34).symm,
      show w.val 5 = w.val 2 from (h23.trans (h34.trans h45)).symm,
      show w.val 6 = w.val 2 from (h23.trans (h34.trans (h45.trans h56))).symm,
      show w.val 7 = w.val 2 from (h23.trans (h34.trans (h45.trans (h56.trans h67)))).symm] at hsum
    have hbinary : ∀ x y t : ZMod 2,
        x + (y + (t + (t + (t + (t + (t + (t + 0))))))) = 0 → x = y := by decide
    exact hbinary _ _ _ hsum
  have hconst (t : Full Ω) (ht : ∀ i, t i = w.val 2) : t ∈ constants Ω :=
    (mem_constants_iff t).mpr ⟨w.val 2, ht⟩
  by_cases he : w.val 0 = w.val 2
  · left
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply hconst
    intro i
    fin_cases i <;> simp_all
  · right
    apply Subtype.ext
    apply (Submodule.Quotient.eq _).mpr
    apply hconst
    have hdiff : w.val 0 - 1 = w.val 2 := by
      have hh : ∀ u v : ZMod 2, u ≠ v → u - 1 = v := by decide
      exact hh _ _ he
    intro i
    fin_cases i <;> simp_all [pair]

/-- The full linear centralizer of the natural A₈ action is trivial. -/
theorem commuting_eq_refl (f : natural (Fin 8) ≃ₗ[ZMod 2] natural (Fin 8))
    (hf : ∀ g : alternatingGroup (Fin 8), ∀ x,
      f (naturalRepresentation (Fin 8) g.val x) =
        naturalRepresentation (Fin 8) g.val (f x)) : f = LinearEquiv.refl _ _ := by
  have hp : f p = p := by
    have ha := (hf ⟨a, even.1⟩ p).symm
    have hb := (hf ⟨b, even.2.1⟩ p).symm
    have hc := (hf ⟨c, even.2.2⟩ p).symm
    rw [fix.1] at ha
    rw [fix.2.1] at hb
    rw [fix.2.2] at hc
    exact (fixed_pair (f p) ha hb hc).resolve_left (by
      intro h
      exact pair_ne (f.injective (h.trans f.map_zero.symm)))
  let P : Subrepresentation (alternatingNaturalRepresentation (Ω := Fin 8)) :=
    { toSubmodule := LinearMap.ker (f.toLinearMap - LinearMap.id)
      apply_mem_toSubmodule := by
        intro g x hx
        change f x - x = 0 at hx
        change f (naturalRepresentation (Fin 8) g.val x) -
          naturalRepresentation (Fin 8) g.val x = 0
        rw [hf, sub_eq_zero.mp hx, sub_self] }
  let := alternatingNatural_isIrreducible (Ω := Fin 8) (by simp)
  have ht : P = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top P).resolve_left (by
    intro h
    have hm : p ∈ P.toSubmodule := sub_eq_zero.mpr hp
    rw [h] at hm
    exact pair_ne hm)
  apply LinearEquiv.ext
  intro x
  have hx : x ∈ P.toSubmodule := by rw [ht]; exact Submodule.mem_top
  exact sub_eq_zero.mp hx
end BinaryPermutation.EightCommutant
