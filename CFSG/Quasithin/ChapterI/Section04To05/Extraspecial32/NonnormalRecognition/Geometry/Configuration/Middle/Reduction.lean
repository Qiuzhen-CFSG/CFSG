module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Control

/-!
# Reduction of the middle fusion union to a missing involution

The two endpoints generate Q and their normalizers intersect in H, already
before the middle subgroup is constructed. If an involution in the third
H-orbit of Q is fused to z, all core involutions are fused. The proved local
involution-fusion theorem then fuses every nonidentity element of A to z.
Consequently one missing involution of A excludes that third orbit and proves
the exact union E# ∪ F# = z^G ∩ Q.

The orbit description and the missing involution remain explicit inputs;
no existence assertion of source Lemma 3.1 is claimed here.
Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.3, 2.6 and 3.1, printed pp.33–37.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z g y : G}

/-- The two actual eights generate Q from their exact involution-line overlap. -/
theorem endpoint_pair_generate (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z) :
    coreIntersection z g ⊔ coreIntersection z y = coreInG z := by
  have hn : coreIntersection z y ≤ normalizer (coreIntersection z g : Set G) :=
    ((coreIntersection_le z y).trans (coreInG_le z)).trans
      (intersection_centralizer_le_normalizer d)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (coreIntersection z g) (coreIntersection z y) hn
  rw [d.card, dy.card, hinter, Nat.card_zpowers, h.involution] at hc
  apply eq_of_le_of_card_ge (sup_le (coreIntersection_le z g) (coreIntersection_le z y))
  rw [h.coreInG_card]
  omega

/-- The two endpoint normalizers meet in the full centralizer H. -/
theorem endpoint_pair_normalizers (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z) :
    normalizer (coreIntersection z g : Set G) ⊓
      normalizer (coreIntersection z y : Set G) = Centralizer z := by
  apply le_antisymm
  · have hn := normalizer_inf_normalizer_le_normalizer_sup
      (coreIntersection z g) (coreIntersection z y)
    rwa [endpoint_pair_generate h d dy hinter, h.normalizer_core] at hn
  · exact le_inf (intersection_centralizer_le_normalizer d)
      (intersection_centralizer_le_normalizer dy)

omit [Finite G] in
/-- Full fusion of the core involutions forces full fusion of A#. -/
theorem MiddleLocalData.full_fusion_of_core (m : MiddleLocalData z)
    (d : IntersectionData z g)
    (hQ : ∀ t ∈ coreInG z, orderOf t = 2 → IsConj z t) :
    ∀ a ∈ m.A, a ≠ 1 → IsConj z a := by
  intro a ha ha1
  let : IsElementaryAbelian 2 m.A := m.elementary
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  obtain ⟨n, hn⟩ := d.involution_fusion a (m.A_le_centralizer ha) ha2
  have hc : IsConj a ((n : G) * a * (n : G)⁻¹) := isConj_iff.mpr ⟨n, rfl⟩
  have ht2 : orderOf ((n : G) * a * (n : G)⁻¹) = 2 := by
    change orderOf (MulAut.conj (n : G) a) = 2
    rw [(MulAut.conj (n : G)).orderOf_eq, ha2]
  exact (hQ _ hn ht2).trans hc.symm

/-- A missing involution in A excludes fusion of the third core orbit. -/
theorem fusion_union_of_third_orbit (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (m : MiddleLocalData z) (horbits : ThirdCoreOrbit z g y)
    (hmissing : ∃ a ∈ m.A, a ≠ 1 ∧ ¬ IsConj z a) :
    ∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
      (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1 := by
  intro x
  constructor
  · rintro ⟨hx, hzx⟩
    have hx2 : orderOf x = 2 := by
      obtain ⟨r, rfl⟩ := isConj_iff.mp hzx
      change orderOf (MulAut.conj r z) = 2
      rw [(MulAut.conj r).orderOf_eq, h.involution]
    have hx1 : x ≠ 1 := by
      intro he
      simp [he] at hx2
    refine ⟨?_, hx1⟩
    by_contra! hout
    have hQ : ∀ t ∈ coreInG z, orderOf t = 2 → IsConj z t := by
      intro t ht ht2
      have ht1 : t ≠ 1 := by
        intro he
        simp [he] at ht2
      rcases horbits x hx hx2 hout.1 hout.2 t ht ht2 with htE | htF | ⟨c, hc⟩
      · exact intersection_sharp_fused h d htE ht1
      · exact intersection_sharp_fused h dy htF ht1
      · exact hzx.trans (isConj_iff.mpr ⟨c, hc⟩)
    obtain ⟨a, ha, ha1, hna⟩ := hmissing
    exact hna (m.full_fusion_of_core d hQ a ha ha1)
  · rintro ⟨hx | hx, hx1⟩
    · exact ⟨coreIntersection_le z g hx, intersection_sharp_fused h d hx hx1⟩
    · exact ⟨coreIntersection_le z y hx, intersection_sharp_fused h dy hx hx1⟩

omit [Finite G] in
/-- Assemble the published record after the two ambient assertions are proved. -/
theorem middle_of_fusion_and_quotient (m : MiddleLocalData z)
    (hfusion : ∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
      (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1)
    (hquot : Nonempty
      ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (MiddleData z g y) :=
  ⟨{
    fusion_union := hfusion
    A := m.A
    elementary := m.elementary
    card := m.card
    self_centralizing := m.self_centralizing
    normalizer_quotient := hquot
    S := m.S
    A_le_sylow := m.A_le_sylow
    normalizer_intersection := m.normalizer_intersection }⟩


end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
