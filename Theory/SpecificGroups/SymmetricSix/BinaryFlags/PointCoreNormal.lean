module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
public import Mathlib.GroupTheory.Perm.Cycle.Type


/-!
# Normal two-subgroups of the natural point stabilizer

In the canonical point core C₂ × E₄, a normal subgroup containing the
point transposition is either that C₂ or the entire core: the source A₄
cycles the three nonidentity elements of E₄. The eight-element core is
checked in its actual disjoint-block coordinates. Conjugating natural
lines transports the result to the literal natural action on every line.

Source: Aschbacher–Smith, 13.7.9(1), using 13.7.3(4),(6), pp.936,940–941.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal
private abbrev a : S := swap01 * swap23
private abbrev b : S := Equiv.swap 0 2 * Equiv.swap 1 3
private theorem words_cert : ∀ x : DuadProduct,
    x ∈ DuadCalculation.productCore →
    (MulAut.conj flagRelabel) (duadProductHom x) ∈
      ([1,a,b,a*b,swap45,swap45*a,swap45*b,swap45*(a*b)] : List S) := by
  simp only [DuadCalculation.productCore, mem_prod, mem_top, true_and, DuadCalculation.core_mem_iff]
  decide +kernel

private theorem words {x : S} (hx : x ∈ pointCore) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a*b ∨ x = swap45 ∨
      x = swap45*a ∨ x = swap45*b ∨ x = swap45*(a*b) := by
  obtain ⟨y,hy,rfl⟩ := hx
  simpa only [List.mem_cons,List.not_mem_nil,or_false, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using words_cert y hy

theorem eq_core (N : Subgroup S) (hle : N ≤ pointCore)
    (hn : K ≤ normalizer (N : Set S)) (hs : swap45 ∈ N)
    (hne : ¬ N ≤ zpowers swap45) : N = pointCore := by
  have hrot (x : S) (hx : x ∈ N) : cycle012 * x * cycle012⁻¹ ∈ N :=
    le_normalizer_iff.mp hn cycle012 (by decide) x hx
  have ha_of_b (hb : b ∈ N) : a ∈ N := by
    have he : cycle012 * b * cycle012⁻¹ = a := by decide
    exact he ▸ hrot b hb
  have hb_of_a (ha : a ∈ N) : b ∈ N := by
    have he : cycle012 * a * cycle012⁻¹ = a*b := by decide
    have hh := mul_mem ha (he ▸ hrot a ha)
    have he' : a * (a*b) = b := by decide
    exact he' ▸ hh
  have ha_of_ab (hab : a*b ∈ N) : a ∈ N := by
    have he : cycle012 * (a*b) * cycle012⁻¹ = b := by decide
    exact ha_of_b (he ▸ hrot (a*b) hab)
  obtain ⟨x,hx,hxnot⟩ := SetLike.not_le_iff_exists.mp hne
  have ha : a ∈ N := by
    rcases words (hle hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hxnot (one_mem _))
    · exact hx
    · exact ha_of_b hx
    · exact ha_of_ab hx
    · exact False.elim (hxnot (mem_zpowers _))
    · have he : swap45*(swap45*a)=a := by decide
      exact he ▸ mul_mem hs hx
    · have he : swap45*(swap45*b)=b := by decide
      exact ha_of_b (he ▸ mul_mem hs hx)
    · have he : swap45*(swap45*(a*b))=a*b := by decide
      exact ha_of_ab (he ▸ mul_mem hs hx)
  apply le_antisymm hle
  rw [pointCore_eq_closure, closure_le, Set.insert_subset_iff,
    Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hs,ha,hb_of_a ha⟩

private theorem swap_in_core {t : S} (ht : t.IsSwap) (hm : t ∈ pointCore) : t = swap45 := by
  rcases words hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (exfalso; have he := Equiv.Perm.isSwap_iff_cycleType.mp ht; revert he; decide)

open NaturalGeometry NaturalPairing BinaryPermutation Representation.BinaryOffender
private theorem line_image (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    ∃ g : S, canonicalLine.map (naturalRepresentation Ω g) = P := by
  have hP0 : P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    contradiction
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff P).mp hP0
  obtain ⟨g,hg⟩ := NaturalTransport.exists_even_image v hv0
  refine ⟨g.val, ?_⟩
  rw [canonicalLine, Submodule.map_span, Set.image_singleton, hg]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0).symm

private theorem conjugate_stabilizes (P : Submodule (ZMod 2) V) (g h : S)
    (hh : h ∈ subspaceStabilizer (naturalRepresentation Ω) P) :
    g * h * g⁻¹ ∈ subspaceStabilizer (naturalRepresentation Ω)
      (P.map (naturalRepresentation Ω g)) := by
  apply (mem_stabilizer_iff_map _ _).mpr
  have hh' := (mem_stabilizer_iff_map _ _).mp hh
  simp only [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  rw [← Submodule.map_comp (naturalRepresentation Ω g) (naturalRepresentation Ω g⁻¹),
    ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_eq_id, Submodule.map_id, hh']

/-- A normal two-subgroup of a natural point stabilizer that contains a
transposition and is larger than that transposition subgroup is the full core. -/
theorem eq_point_core (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (N : Subgroup S)
    (hp : IsPGroup 2 N)
    (hle : N ≤ subspaceStabilizer (naturalRepresentation Ω) P)
    (hn : subspaceStabilizer (naturalRepresentation Ω) P ≤ normalizer (N : Set S))
    (t : S) (ht : t.IsSwap) (hm : t ∈ N) (hne : ¬ N ≤ zpowers t) :
    N = (subspaceStabilizer (naturalRepresentation Ω) P).pCoreIn 2 := by
  obtain ⟨g,rfl⟩ := line_image P hP
  let C := subspaceStabilizer (naturalRepresentation Ω)
    (canonicalLine.map (naturalRepresentation Ω g))
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hback : (canonicalLine.map (naturalRepresentation Ω g)).map
      (naturalRepresentation Ω g⁻¹) = canonicalLine := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
  have he : C.map c = H1 := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hs := conjugate_stabilizes _ g⁻¹ x hx
      rw [hback] at hs
      exact (canonicalLine_stabilizer _).mp ((mem_stabilizer_iff_map _ _).mp hs)
    · intro x hx
      refine ⟨g*x*g⁻¹, ?_, ?_⟩
      · exact conjugate_stabilizes _ g x
          ((mem_stabilizer_iff_map _ _).mpr (canonicalLine_map_of_mem hx))
      · change g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹=x
        simp [mul_assoc]
  have hNc : N.map c ≤ H1 := (map_mono hle).trans_eq he
  have hnC : H1 ≤ normalizer (N.map c : Set S) := by
    rw [← he]
    exact (map_mono hn).trans (le_normalizer_map c)
  have hNC : N.map c ≤ pointCore := by
    rw [← H1_core_eq_pointCore]
    exact le_pCoreIn_of_normalizes (hp.map c) hNc hnC
  have ht' : (c t).IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ht
    change (g⁻¹ * Equiv.swap i j * (g⁻¹)⁻¹).IsSwap
    rw [← Equiv.swap_apply_apply]
    exact ⟨_,_,g.symm.injective.ne hij,rfl⟩
  have hswap := swap_in_core ht' (hNC (mem_map_of_mem c hm))
  have hne' : ¬ N.map c ≤ zpowers swap45 := by
    intro hh
    apply hne
    rw [← hswap, ← MonoidHom.map_zpowers] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hfull := eq_core (N.map c) hNC (K_le_H1.trans hnC)
    (hswap ▸ mem_map_of_mem c hm) hne'
  have hecore : (C.pCoreIn 2).map c = pointCore := by
    rw [map_pCoreIn_of_injective 2 C c (MulAut.conj g⁻¹).injective, he,
      H1_core_eq_pointCore]
  exact (map_injective (MulAut.conj g⁻¹).injective) (hfull.trans hecore.symm)
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal

