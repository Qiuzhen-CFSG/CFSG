module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.CoreOrbits
public import Mathlib.Logic.Equiv.Basic

/-!
# From local conjugacy-class incidence to nine ambient fused involutions

Equal M-class fibers give a class-preserving bijection between the
involutions of A and Q outside E. Any ambient conjugacy class selects
equally many elements on both sides. The exact endpoint fusion union
in Q has thirteen elements, seven in E, hence six outside E. Adding the
three nonidentity elements of A ∩ E gives nine in A.

The proof keeps the local matching explicit: its construction in the split
endpoint normalizer remains an independent prerequisite. In particular,
merely fusing each H-involution into Q does not supply this matching.
Source: Aschbacher, “A 2-local characterization of M12”, Lemma 2.6(3)
and the last paragraph of the proof of Lemma 3.1, printed pp.35–37.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
variable {G : Type*} [Group G] [Finite G] {z g y : G}

/-- Equal class fibers preserve the size selected by any conjugacy-invariant predicate. -/
private theorem filtered_card_eq_of_class_fibers {L : Type*} [Group L] [Finite L]
    (S T : Set L)
    (hc : ∀ c : ConjClasses L,
      Nat.card {x : S // ConjClasses.mk (x : L) = c} =
      Nat.card {x : T // ConjClasses.mk (x : L) = c})
    (P : L → Prop) (hp : ∀ a b, IsConj a b → (P a ↔ P b)) :
    Nat.card {x : L // x ∈ S ∧ P x} = Nat.card {x : L // x ∈ T ∧ P x} := by
  classical
  let e' (c : ConjClasses L) : {x : S // ConjClasses.mk (x : L) = c} ≃
      {x : T // ConjClasses.mk (x : L) = c} :=
    (Finite.equivFin _).trans ((finCongr (hc c)).trans (Finite.equivFin _).symm)
  let e : S ≃ T := Equiv.ofFiberEquiv e'
  have he (a : S) : IsConj (a : L) (e a : L) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (Equiv.ofFiberEquiv_map e' a).symm
  let f : {x : L // x ∈ S ∧ P x} ≃ {x : L // x ∈ T ∧ P x} := {
    toFun a := ⟨e ⟨a, a.property.1⟩, (e ⟨a, a.property.1⟩).property,
      (hp _ _ (he ⟨a, a.property.1⟩)).mp a.property.2⟩
    invFun b := ⟨e.symm ⟨b, b.property.1⟩, (e.symm ⟨b, b.property.1⟩).property, by
      have hr := he (e.symm ⟨b, b.property.1⟩)
      rw [e.apply_symm_apply] at hr
      exact (hp _ _ hr).mpr b.property.2⟩
    left_inv a := by
      apply Subtype.ext
      change ((e.symm (e ⟨a, a.property.1⟩) : S) : L) = a
      exact congrArg (fun x : S => (x : L)) (e.symm_apply_apply _)
    right_inv b := by
      apply Subtype.ext
      change ((e (e.symm ⟨b, b.property.1⟩) : T) : L) = b
      exact congrArg (fun x : T => (x : L)) (e.apply_symm_apply _) }
  exact Nat.card_congr f



abbrev outsideFusion (z g : G) (B : Subgroup G) : Set G :=
  {x | x ∈ B ∧ x ∉ coreIntersection z g ∧ IsConj z x}

omit [Finite G] in
private theorem fused_order (hz : orderOf z = 2) {x : G} (hx : IsConj z x) :
    orderOf x = 2 := by
  obtain ⟨r, rfl⟩ := isConj_iff.mp hx
  change orderOf (MulAut.conj r z) = 2
  rw [(MulAut.conj r).orderOf_eq, hz]

omit [Finite G] in
private theorem fused_ne_one (hz : orderOf z = 2) {x : G} (hx : IsConj z x) : x ≠ 1 := by
  intro he
  have ho := fused_order hz hx
  simp [he] at ho

private def outsideFusionEquiv (hz : orderOf z = 2) (B : Subgroup G)
    (hB : B ≤ endpointNormalizer z g) :
    {x : endpointNormalizer z g //
      x ∈ normalizerInvolutionsOutside z g B ∧ IsConj z (x : G)} ≃ outsideFusion z g B where
  toFun x := ⟨x.val, x.property.1.1, x.property.1.2.1, x.property.2⟩
  invFun x := ⟨⟨x, hB x.property.1⟩,
    ⟨x.property.1, x.property.2.1, fused_order hz x.property.2.2⟩, x.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem outsideFusion_card_eq (h : Hypotheses z) (d : IntersectionData z g)
    (m : MiddleLocalData z) (matching : MiddleClassMatching z g m.A) :
    (outsideFusion z g m.A).ncard = (outsideFusion z g (coreInG z)).ncard := by
  have hM := intersection_centralizer_le_normalizer d
  have he := filtered_card_eq_of_class_fibers
    (normalizerInvolutionsOutside z g m.A)
    (normalizerInvolutionsOutside z g (coreInG z)) matching.class_fibers
    (fun x : endpointNormalizer z g => IsConj z (x : G)) (by
      intro a b hab
      have hab' : IsConj (a : G) (b : G) := (endpointNormalizer z g).subtype.map_isConj hab
      exact ⟨fun ha => ha.trans hab', fun hb => hb.trans hab'.symm⟩)
  exact (Nat.card_congr (outsideFusionEquiv h.involution m.A
    (m.A_le_centralizer.trans hM))).symm.trans
    (he.trans (Nat.card_congr (outsideFusionEquiv h.involution (coreInG z)
      ((coreInG_le z).trans hM))))

/-- Partition ambient fusion into its part in E and its part outside E. -/
theorem fusion_card_partition (h : Hypotheses z) (d : IntersectionData z g)
    (B : Subgroup G) :
    Nat.card (MiddleFusion z B) + 1 =
      (outsideFusion z g B).ncard + Nat.card (B ⊓ coreIntersection z g : Subgroup G) := by
  let S : Set G := {x | x ∈ B ∧ IsConj z x}
  let E := coreIntersection z g
  have hi : S ∩ (E : Set G) = ((B ⊓ E : Subgroup G) : Set G) \ {1} := by
    ext x
    constructor
    · rintro ⟨⟨hxB, hxz⟩, hxE⟩
      exact ⟨⟨hxB, hxE⟩, fused_ne_one h.involution hxz⟩
    · rintro ⟨⟨hxB, hxE⟩, hx1⟩
      exact ⟨⟨hxB, intersection_sharp_fused h d hxE hx1⟩, hxE⟩
  have ho : S \ (E : Set G) = outsideFusion z g B := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2, hx.1.2⟩,
      fun hx => ⟨⟨hx.1, hx.2.2⟩, hx.2.1⟩⟩
  have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard S (E : Set G)
  rw [hi, ho] at hc
  have hs := Set.ncard_sdiff_singleton_add_one (B ⊓ E).one_mem
  change _ + 1 = Nat.card (B ⊓ E : Subgroup G) at hs
  change _ + _ = Nat.card (MiddleFusion z B) at hc
  change _ + 1 = Nat.card (B ⊓ coreIntersection z g : Subgroup G) at hs
  omega

/-- The class matching in M gives nine from the source fusion union in Q. -/
theorem middleFusion_card_of_matching (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (m : MiddleLocalData z) (matching : MiddleClassMatching z g m.A)
    (fusion_union : ∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
      (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1) :
    Nat.card (MiddleFusion z m.A) = 9 := by
  have hcore : Nat.card (MiddleFusion z (coreInG z)) = 13 := by
    have he : {x : G | x ∈ coreInG z ∧ IsConj z x} = endpointSharp z g y :=
      Set.ext fusion_union
    exact (Nat.card_congr (Equiv.setCongr he)).trans (endpointSharp_card h d dy hinter)
  have hc := fusion_card_partition h d (coreInG z)
  rw [hcore, inf_eq_right.mpr (coreIntersection_le z g), d.card] at hc
  have ha := fusion_card_partition h d m.A
  rw [outsideFusion_card_eq h d m matching, matching.plane_card] at ha
  omega


end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
end
