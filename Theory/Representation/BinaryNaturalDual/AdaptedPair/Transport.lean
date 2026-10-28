module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Simultaneous inner transport of a point and its actor

For an index-two subgroup L of a finite group, a Sylow subgroup meeting the
other coset absorbs the outer part of a conjugator. The same argument inside
a point stabilizer puts a prescribed p-subgroup into a prescribed stabilizer
Sylow using an element of L that fixes the point. Composing this element with
a point transporter preserves the actor as well as the point.

These are ordinary Sylow and index-two arguments. In the binary natural-plus-
dual application, the point is a pairing-one pair and the stabilizer Sylow
must first be constructed by the explicit coordinate calculation.

Source: the corrected adapted-pair argument for Aschbacher–Smith H.9.1(4),
combined manuscript (1 March 2004), printed p.390; consumers 12.1.1 and 12.1.3.
-/

public section

namespace BinaryNaturalDual.AdaptedPair

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Sylow conjugacy can be effected inside an index-two subgroup when the
source Sylow contains an element outside that subgroup. -/
theorem exists_inner_sylow_conjugator (L : Subgroup G) (hL : L.index = 2)
    (S T : Sylow p G) (houter : ∃ s ∈ (S : Subgroup G), s ∉ L) :
    ∃ l ∈ L, l • S = T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  by_cases hgL : g ∈ L
  · exact ⟨g, hgL, hg⟩
  obtain ⟨s, hs, hsL⟩ := houter
  refine ⟨g * s, (L.mul_mem_iff_of_index_two hL).mpr (iff_of_false hgL hsL), ?_⟩
  rw [mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr ((S : Subgroup G).le_normalizer hs)]
  exact hg

/-- Inside C, the outer coset of a Sylow P absorbs the outer part of the
Sylow conjugator. No p-group hypothesis on C is needed. -/
theorem exists_inner_conjugator_into_stabilizer_sylow
    (L C A : Subgroup G) (hL : L.index = 2)
    (P : Sylow p C) (houter : ∃ s : C, s ∈ (P : Subgroup C) ∧ (s : G) ∉ L)
    (hA : IsPGroup p A) (hAC : A ≤ C) :
    ∃ l ∈ L, l ∈ C ∧ A.map (MulAut.conj l).toMonoidHom ≤
      (P : Subgroup C).map C.subtype := by
  have hACp : IsPGroup p (A.subgroupOf C) :=
    hA.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨Q, hAQ⟩ := hACp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q P
  have hconj (a : G) (ha : a ∈ A) :
      g * (⟨a, hAC ha⟩ : C) * g⁻¹ ∈ (P : Subgroup C) := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hAQ ha)
  by_cases hgL : (g : G) ∈ L
  · refine ⟨g, hgL, g.property, ?_⟩
    rintro x ⟨a, ha, rfl⟩
    exact Subgroup.mem_map_of_mem C.subtype (hconj a ha)
  obtain ⟨s, hs, hsL⟩ := houter
  refine ⟨(s : G) * g, (L.mul_mem_iff_of_index_two hL).mpr
    (iff_of_false hsL hgL), C.mul_mem s.property g.property, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  have hm := (P : Subgroup C).mul_mem
    ((P : Subgroup C).mul_mem hs (hconj a ha)) ((P : Subgroup C).inv_mem hs)
  have hout := Subgroup.mem_map_of_mem C.subtype hm
  change (s : G) * ((g : G) * a * (g : G)⁻¹) * (s : G)⁻¹ ∈
    (P : Subgroup C).map C.subtype at hout
  change ((s : G) * g) * a * ((s : G) * g)⁻¹ ∈ _
  simpa only [mul_inv_rev, mul_assoc] using hout

variable {X : Type*} [MulAction G X]

/-- Move a point and its prescribed p-subgroup simultaneously. The second
conjugator fixes the target point and belongs to L. -/
theorem exists_inner_pair_transporter
    (L : Subgroup G) (hL : L.index = 2) (v w : X)
    (hvw : ∃ l ∈ L, l • v = w)
    (P : Sylow p (MulAction.stabilizer G w))
    (houter : ∃ s : MulAction.stabilizer G w,
      s ∈ (P : Subgroup (MulAction.stabilizer G w)) ∧ (s : G) ∉ L)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAv : A ≤ MulAction.stabilizer G v) :
    ∃ l ∈ L, l • v = w ∧ A.map (MulAut.conj l).toMonoidHom ≤
      (P : Subgroup (MulAction.stabilizer G w)).map (MulAction.stabilizer G w).subtype := by
  obtain ⟨a, haL, ha⟩ := hvw
  let B := A.map (MulAut.conj a).toMonoidHom
  have hBC : B ≤ MulAction.stabilizer G w := by
    rintro b ⟨b, hb, rfl⟩
    rw [MulAction.mem_stabilizer_iff, ← ha]
    change (a * b * a⁻¹) • (a • v) = a • v
    simp only [mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.mp (hAv hb)]
  obtain ⟨c, hcL, hcw, hc⟩ := exists_inner_conjugator_into_stabilizer_sylow
    L (MulAction.stabilizer G w) B hL P houter (hA.map _) hBC
  refine ⟨c * a, L.mul_mem hcL haL, ?_, ?_⟩
  · rw [mul_smul, ha]
    exact hcw
  · rintro x ⟨b, hb, rfl⟩
    have hm := hc (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hb))
    change c * (a * b * a⁻¹) * c⁻¹ ∈ _ at hm
    change (c * a) * b * (c * a)⁻¹ ∈ _
    simpa only [mul_inv_rev, mul_assoc] using hm

omit [Finite G] in
private theorem sylow_map_ambient {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* K) (P : Sylow p H) (i : H →* G) (j : K →* G) (f : G →* G)
    (h : j.comp e.toMonoidHom = f.comp i) :
    ∃ Q : Sylow p K, (Q : Subgroup K).map j = ((P : Subgroup H).map i).map f := by
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective he, ?_⟩
  change ((P : Subgroup H).map e.toMonoidHom).map j = _
  rw [Subgroup.map_map, Subgroup.map_map, h]


theorem conjugate_stabilizer_sylow
    (w : X) (P : Sylow p (MulAction.stabilizer G w)) (g : G) :
    ∃ Q : Sylow p (MulAction.stabilizer G (g • w)),
      (Q : Subgroup (MulAction.stabilizer G (g • w))).map
          (MulAction.stabilizer G (g • w)).subtype =
        ((P : Subgroup (MulAction.stabilizer G w)).map
          (MulAction.stabilizer G w).subtype).map (MulAut.conj g).toMonoidHom := by
  let e := MulAction.stabilizerEquivStabilizer (g := g) (a := w) rfl
  apply sylow_map_ambient e P
  ext x
  exact MulAction.stabilizerEquivStabilizer_apply rfl x


/-- A single standard stabilizer Sylow meeting the outer coset suffices to
transport an arbitrary point-actor pair to every ambient Sylow. -/
theorem exists_pair_in_arbitrary_sylow
    (L : Subgroup G) (hL : L.index = 2) (S T : Sylow p G) (v w : X)
    (hvw : ∃ l ∈ L, l • v = w)
    (P : Sylow p (MulAction.stabilizer G w))
    (hP : (P : Subgroup (MulAction.stabilizer G w)).map
      (MulAction.stabilizer G w).subtype = (S : Subgroup G) ⊓ MulAction.stabilizer G w)
    (houter : ∃ s : MulAction.stabilizer G w,
      s ∈ (P : Subgroup (MulAction.stabilizer G w)) ∧ (s : G) ∉ L)
    (A : Subgroup G) (hA : IsPGroup p A) (hAv : A ≤ MulAction.stabilizer G v) :
    ∃ g ∈ L, ∃ l ∈ L,
      g • S = T ∧ l • v = g • w ∧
      A.map (MulAut.conj l).toMonoidHom ≤ (T : Subgroup G) ⊓ MulAction.stabilizer G (g • w) ∧
      ∃ Q : Sylow p (MulAction.stabilizer G (g • w)),
        (Q : Subgroup (MulAction.stabilizer G (g • w))).map
          (MulAction.stabilizer G (g • w)).subtype =
          (T : Subgroup G) ⊓ MulAction.stabilizer G (g • w) := by
  have hSouter : ∃ s ∈ (S : Subgroup G), s ∉ L := by
    obtain ⟨s, hs, hsL⟩ := houter
    have hm := Subgroup.mem_map_of_mem (MulAction.stabilizer G w).subtype hs
    rw [hP] at hm
    exact ⟨s, hm.1, hsL⟩
  obtain ⟨g, hgL, hg⟩ := exists_inner_sylow_conjugator L hL S T hSouter
  obtain ⟨a, haL, ha, hA'⟩ := exists_inner_pair_transporter L hL v w hvw P houter A hA hAv
  have hmap :
      ((P : Subgroup (MulAction.stabilizer G w)).map
        (MulAction.stabilizer G w).subtype).map (MulAut.conj g).toMonoidHom =
        (T : Subgroup G) ⊓ MulAction.stabilizer G (g • w) := by
    rw [hP, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have hg' := congrArg Sylow.toSubgroup hg
    exact congrArg (· ⊓ (MulAction.stabilizer G w).map (MulAut.conj g).toMonoidHom) hg'
  refine ⟨g, hgL, g * a, L.mul_mem hgL haL, hg, ?_, ?_, ?_⟩
  · rw [mul_smul, ha]
  · rintro b ⟨b, hb, rfl⟩
    rw [← hmap]
    have hm := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
      (hA' (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hb))
    change g * (a * b * a⁻¹) * g⁻¹ ∈ _ at hm
    change (g * a) * b * (g * a)⁻¹ ∈ _
    simpa only [mul_inv_rev, mul_assoc] using hm
  · obtain ⟨Q, hQ⟩ := conjugate_stabilizer_sylow w P g
    exact ⟨Q, hQ.trans hmap⟩

end BinaryNaturalDual.AdaptedPair
