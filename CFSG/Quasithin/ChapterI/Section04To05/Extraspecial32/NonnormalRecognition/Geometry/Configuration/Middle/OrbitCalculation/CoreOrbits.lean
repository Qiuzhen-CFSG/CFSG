module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.CoreCount

/-!
# The third core orbit from fixed-point congruences

Every noncentral H-orbit in Q is fixed-point-free for both the core Q
and the chosen Sylow three-subgroup X. The p-group fixed-point congruence
therefore makes its positive size divisible by six. The two H-normal
endpoint eights, meeting in ⟨z⟩, account for thirteen of the nineteen
involutions. The six remaining involutions consequently form one H-orbit.

This proves precisely the orbit assertion used in the fusion exclusion,
without a split-normalizer or ambient-recognition hypothesis.
Source: Aschbacher, “A 2-local characterization of M12”, Lemma 2.3(2)(a)
and proof of Lemma 3.1, printed pp.33–37.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
variable {G : Type*} [Group G] [Finite G] {z g y : G}

private theorem line_nonidentity (h : Hypotheses z) {t : G}
    (ht : t ∈ zpowers z) (ht1 : t ≠ 1) : t = z := by
  have hc : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans h.involution
  obtain ⟨a, _, hu⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp hc
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  exact congrArg (fun u : zpowers z => (u : G))
    ((hu ⟨t, ht⟩ (fun he => ht1 (congrArg Subtype.val he))).trans
      (hu ⟨z, mem_zpowers z⟩ (fun he => hz1 (congrArg Subtype.val he))).symm)

/-- Fixed-point congruences for Q and X force orbit size at least six. -/
theorem centralizerOrbit_card_ge_six (h : Hypotheses z) {x : G}
    (hx : x ∈ coreInG z) (hx2 : orderOf x = 2) (hxz : x ≠ z) :
    6 ≤ (centralizerOrbit z x).ncard := by
  let : MulDistribMulAction (Centralizer z) G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp (Centralizer z).subtype)
  let : MulAction (Centralizer z) G :=
    (inferInstance : MulDistribMulAction (Centralizer z) G).toMulAction
  let Y := MulAction.orbit (Centralizer z) x
  have ht (t : Y) : (t : G) ∈ coreInG z ∧ orderOf (t : G) = 2 ∧ (t : G) ≠ z := by
    obtain ⟨c, hc⟩ := t.property
    change (c : G) * x * (c : G)⁻¹ = t at hc
    have hcn : (c : G) ∈ normalizer (coreInG z : Set G) :=
      h.normalizer_core.symm ▸ c.property
    refine ⟨hc ▸ (hcn x).mp hx, ?_, ?_⟩
    · rw [← hc]
      change orderOf (MulAut.conj (c : G) x) = 2
      rw [(MulAut.conj (c : G)).orderOf_eq, hx2]
    · intro he
      apply hxz
      apply (MulAut.conj (c : G)).injective
      exact (hc.trans he).trans (mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp c.property)).symm
  have hnline (t : Y) : (t : G) ∉ zpowers z := by
    intro hl
    have ht1 : (t : G) ≠ 1 := by intro he; have hi := (ht t).2.1; simp [he] at hi
    exact (ht t).2.2 (line_nonidentity h hl ht1)
  have htwo : 2 ∣ Nat.card Y := by
    let : MulAction (coreInG z) Y := MulAction.compHom Y (inclusion (coreInG_le z))
    have hempty : IsEmpty (MulAction.fixedPoints (coreInG z) Y) := ⟨by
      intro t
      have htZ : (⟨t.val, (ht t.val).1⟩ : coreInG z) ∈ center (coreInG z) := by
        apply mem_center_iff.mpr
        intro a
        apply Subtype.ext
        have he := congrArg (fun y : Y => (y : G)) (t.property a)
        change (a : G) * (t.val : G) * (a : G)⁻¹ = t.val at he
        exact mul_inv_eq_iff_eq_mul.mp he
      apply hnline t.val
      rw [← h.coreInG_center_image]
      exact mem_map_of_mem (coreInG z).subtype htZ⟩
    let _ := hempty
    have hm := (IsPGroup.of_card (p := 2) (n := 5) h.coreInG_card).card_modEq_card_fixedPoints Y
    have hc : Nat.card (MulAction.fixedPoints (coreInG z) Y) = 0 := by simp
    rw [hc] at hm
    exact Nat.modEq_zero_iff_dvd.mp hm
  have hthree : 3 ∣ Nat.card Y := by
    let : MulAction h.X Y := MulAction.compHom Y (h.X : Subgroup (Centralizer z)).subtype
    have hempty : IsEmpty (MulAction.fixedPoints h.X Y) := ⟨by
      intro t
      let tH : Centralizer z := ⟨t.val, coreInG_le z (ht t.val).1⟩
      have htQ : tH ∈ Core z := by
        rw [← coreInG_subgroupOf]
        exact (ht t.val).1
      have htC : tH ∈ centralizer (h.X : Set (Centralizer z)) := by
        intro a ha
        apply Subtype.ext
        have he := congrArg (fun y : Y => (y : G)) (t.property ⟨a, ha⟩)
        change (a : G) * (t.val : G) * (a : G)⁻¹ = t.val at he
        exact mul_inv_eq_iff_eq_mul.mp he
      have hl : tH ∈ zpowers (distinguished z) := h.fixed ▸ ⟨htQ, htC⟩
      apply hnline t.val
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hl
      exact mem_zpowers_iff.mpr ⟨n, congrArg (fun a : Centralizer z => (a : G)) hn⟩⟩
    let _ := hempty
    have hm := h.X.isPGroup'.card_modEq_card_fixedPoints Y
    have hc : Nat.card (MulAction.fixedPoints h.X Y) = 0 := by simp
    rw [hc] at hm
    exact Nat.modEq_zero_iff_dvd.mp hm
  have hsix : 6 ∣ Nat.card Y := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have hpos : 0 < Nat.card Y := by
    apply Finite.card_pos_iff.mpr
    exact ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  exact Nat.le_of_dvd hpos hsix

abbrev endpointSharp (z g y : G) : Set G :=
  ((coreIntersection z g : Set G) ∪ (coreIntersection z y : Set G)) \ {1}

theorem endpointSharp_card (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z) :
    (endpointSharp z g y).ncard = 13 := by
  have hu := Set.ncard_union_add_ncard_inter
    (coreIntersection z g : Set G) (coreIntersection z y : Set G)
  change _ + Nat.card (coreIntersection z g ⊓ coreIntersection z y : Subgroup G) =
    Nat.card (coreIntersection z g) + Nat.card (coreIntersection z y) at hu
  rw [hinter, Nat.card_zpowers, h.involution, d.card, dy.card] at hu
  have hr := Set.ncard_sdiff_singleton_add_one
    (show (1 : G) ∈ (coreIntersection z g : Set G) ∪ (coreIntersection z y : Set G)
      from Or.inl (coreIntersection z g).one_mem)
  change (endpointSharp z g y).ncard + 1 = _ at hr
  omega

omit [Finite G] in
private theorem endpointSharp_subset (d : IntersectionData z g) (dy : IntersectionData z y) :
    endpointSharp z g y ⊆ coreInvolutions z := by
  rintro x ⟨hx | hx, hx1⟩
  · let _ := d.elementary
    exact ⟨coreIntersection_le z g hx,
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1⟩
  · let _ := dy.elementary
    exact ⟨coreIntersection_le z y hx,
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1⟩

theorem thirdCoreOrbit (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    : ThirdCoreOrbit z g y := by
  intro x hx hx2 hxE hxF
  have hxz : x ≠ z := fun he => hxE (he.symm ▸ distinguished_mem_intersection d)
  let R := coreInvolutions z \ endpointSharp z g y
  have hR : R.ncard = 6 := by
    rw [Set.ncard_sdiff (endpointSharp_subset d dy), coreInvolutions_card h,
      endpointSharp_card h d dy hinter]
  have hsub : centralizerOrbit z x ⊆ R := by
    rintro t ⟨c, rfl⟩
    have hcQ : (c : G) ∈ normalizer (coreInG z : Set G) :=
      h.normalizer_core.symm ▸ c.property
    have hcE := intersection_centralizer_le_normalizer d c.property
    have hcF := intersection_centralizer_le_normalizer dy c.property
    refine ⟨⟨(hcQ x).mp hx, ?_⟩, ?_⟩
    · change orderOf (MulAut.conj (c : G) x) = 2
      rw [(MulAut.conj (c : G)).orderOf_eq, hx2]
    · rintro ⟨ht | ht, _⟩
      · exact hxE ((hcE x).mpr ht)
      · exact hxF ((hcF x).mpr ht)
  have he : centralizerOrbit z x = R :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hR]; exact centralizerOrbit_card_ge_six h hx hx2 hxz)
  intro t ht ht2
  by_cases htE : t ∈ coreIntersection z g
  · exact Or.inl htE
  by_cases htF : t ∈ coreIntersection z y
  · exact Or.inr (Or.inl htF)
  apply Or.inr ∘ Or.inr
  change t ∈ centralizerOrbit z x
  rw [he]
  exact ⟨⟨ht, ht2⟩, fun ht => ht.1.elim htE htF⟩


end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
end
