module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Families
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Actual inner geometry for the order-two elementary core

Source: Aschbacher–Smith, proof of Lemma 2.5.24, printed p.568.
The faithful inner action lifts the involution cover and the conjugator of
its two Klein four-subgroups. The distinguished inner central involution
belongs to the first four-group. At core order two the joins with these
four-groups are elementary of order eight and conjugate by an actual
member of S. Only the two small holomorph membership tables are computed.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

private theorem model_involution_cover (a : Holomorph.Model)
    (ha : a ∈ Holomorph.innerD) (ha2 : a ^ 2 = 1) :
    a ∈ Holomorph.kleinZero ∨ a ∈ Holomorph.kleinOne := by
  rw [Holomorph.mem_innerD] at ha
  rw [Holomorph.mem_kleinZero, Holomorph.mem_kleinOne]
  have table : ∀ a : Holomorph.Model, (∃ b, Holomorph.innerEmbedding b = a) →
      a ^ 2 = 1 → (∃ b, Holomorph.kleinZeroEmbedding b = a) ∨
        (∃ b, Holomorph.kleinOneEmbedding b = a) := by decide +kernel
  exact table a ha ha2

private theorem model_inner_centralizer (a : Holomorph.Model)
    (ha : a ∈ Holomorph.innerD)
    (hc : a ∈ centralizer (Holomorph.kleinZero : Set Holomorph.Model)) :
    a ∈ Holomorph.kleinZero := by
  have hr : Holomorph.reflection ∈ Holomorph.kleinZero :=
    ⟨(1, .ofAdd 1), by decide +kernel⟩
  have h := hc _ hr
  rw [Holomorph.mem_innerD] at ha
  rw [Holomorph.mem_kleinZero]
  have table : ∀ a : Holomorph.Model, (∃ b, Holomorph.innerEmbedding b = a) →
      Holomorph.reflection * a = a * Holomorph.reflection →
      ∃ b, Holomorph.kleinZeroEmbedding b = a := by decide +kernel
  exact table a ha h

variable (d : EarlierSetup κ G)

/-- Involutions in the actual inner dihedral subgroup are covered by its two four-groups. -/
theorem inner_involution_cover (a : G) (ha : a ∈ d.S ⊓ d.K) (ha2 : a ^ 2 = 1) :
    a ∈ fourZero d ∨ a ∈ fourOne d := by
  let b : d.imageSylow := innerEquiv d ⟨a, ha⟩
  let e := Identification.sylowEquiv d.imageSylow
  have hb : b ∈ sylowInner d.imageSylow := (innerEquiv d ⟨a, ha⟩).property
  have hbD : e.symm b ∈ Holomorph.innerD := by
    rwa [← Identification.sylowEquiv_innerD, mem_map_equiv] at hb
  have hb2 : (e.symm b) ^ 2 = 1 := by
    have h : (⟨a, ha⟩ : (d.S ⊓ d.K : Subgroup G)) ^ 2 = 1 := Subtype.ext ha2
    have h' := congrArg (fun k => (innerEquiv d k : d.imageSylow)) h
    have h'' : b ^ 2 = 1 := by simpa only [map_pow, map_one, coe_pow, coe_one] using h'
    simpa only [map_pow, map_one] using congrArg e.symm h''
  rcases model_involution_cover _ hbD hb2 with h | h
  · left
    apply (mem_liftInner d _ ⟨a, ha⟩).mpr
    exact (mem_map_equiv).mpr h
  · right
    apply (mem_liftInner d _ ⟨a, ha⟩).mpr
    exact (mem_map_equiv).mpr h

/-- The marked inner central involution belongs to the first four-group. -/
theorem zK_mem_fourZero : d.zK ∈ fourZero d := by
  have hz : d.zK ∈ centerIn (d.S ⊓ d.K) := d.center_sk ▸ mem_zpowers d.zK
  let b : d.imageSylow := innerEquiv d ⟨d.zK, hz.1⟩
  let e := Identification.sylowEquiv d.imageSylow
  have hb : b ∈ sylowInner d.imageSylow := (innerEquiv d ⟨d.zK, hz.1⟩).property
  have hbD : e.symm b ∈ Holomorph.innerD := by
    rwa [← Identification.sylowEquiv_innerD, mem_map_equiv] at hb
  have hc : e.symm b ∈ centralizer (Holomorph.kleinZero : Set Holomorph.Model) := by
    intro c hc
    have hcI : e c ∈ sylowInner d.imageSylow := by
      rw [← Identification.sylowEquiv_innerD]
      exact ⟨c, Holomorph.kleinZero_le_innerD hc, rfl⟩
    let k := (innerEquiv d).symm ⟨e c, hcI⟩
    have hk := hz.2 k k.property
    have heq : k * ⟨d.zK, hz.1⟩ = ⟨d.zK, hz.1⟩ * k := Subtype.ext hk
    have h := congrArg (fun a => (innerEquiv d a : d.imageSylow)) heq
    have h' : e c * b = b * e c := by
      simpa only [map_mul, coe_mul, k, MulEquiv.apply_symm_apply] using h
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm h'
  apply (mem_liftInner d _ ⟨d.zK, hz.1⟩).mpr
  exact mem_map_equiv.mpr (model_inner_centralizer _ hbD hc)

/-- The actual S-action interchanges its two inner four-groups. -/
theorem four_conjugate : ∃ s ∈ d.S, rightConjugate s (fourZero d) = fourOne d := by
  obtain ⟨s, hs⟩ := toImageSylow_surjective d
    (Identification.sylowEquiv d.imageSylow Holomorph.rotation)
  have hn : d.S ≤ normalizer (d.S ⊓ d.K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.normal_sk
  have hle : rightConjugate (s : G)⁻¹ (fourZero d) ≤ fourOne d := by
    rintro a ⟨k, hk, rfl⟩
    have hkD := fourZero_le d hk
    have hk' : (s : G) * k * (s : G)⁻¹ ∈ d.S ⊓ d.K :=
      (mem_normalizer_iff.mp (hn s.property) k).mp hkD
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    apply (mem_liftInner d _ ⟨_, hk'⟩).mpr
    have hki := (mem_liftInner d _ ⟨k, hkD⟩).mp hk
    have hmap : (innerEquiv d ⟨(s : G) * k * (s : G)⁻¹, hk'⟩ : d.imageSylow) =
        d.toImageSylow s * (innerEquiv d ⟨k, hkD⟩ : d.imageSylow) *
          (d.toImageSylow s)⁻¹ := by
      change d.toImageSylow (s * ⟨k, hkD.1⟩ * s⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [hmap, hs]
    have hmem := mem_map_of_mem
      (MulAut.conj (Identification.sylowEquiv d.imageSylow Holomorph.rotation)).toMonoidHom hki
    rw [SylowGeometry.rotation_conjugates_klein] at hmem
    exact hmem
  refine ⟨(s : G)⁻¹, d.S.inv_mem s.property, eq_of_le_of_card_ge hle ?_⟩
  rw [rightConjugate_card]
  exact le_of_eq (IsKleinFour.card_four.trans IsKleinFour.card_four.symm)

/-- At order two the core is central in S. -/
theorem core_le_center (hcard : Nat.card d.SC = 2) : d.SC ≤ centerIn d.S := by
  rw [core_eq_zpowers_of_card_two d hcard, d.center_s]
  exact le_sup_left

theorem four_join_elementary (hEA : IsElementaryAbelian 2 d.SC)
    (E : Subgroup G) (hE : E ≤ d.K) [IsKleinFour E] :
    IsElementaryAbelian 2 (d.SC ⊔ E : Subgroup G) := by
  let := hEA
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  exact IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp ((d.centralizer_K ▸ inf_le_right).trans (centralizer_le hE)))

theorem four_join_card (hcard : Nat.card d.SC = 2)
    (E : Subgroup G) (hE : E ≤ d.K) [IsKleinFour E] :
    Nat.card (d.SC ⊔ E : Subgroup G) = 8 := by
  have hc : E ≤ centralizer (d.SC : Set G) :=
    le_centralizer_iff.mp ((d.centralizer_K ▸ inf_le_right).trans (centralizer_le hE))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hc.trans (centralizer_le_normalizer _))
    (d.disjoint_k_sc.mono_left hE).symm, hcard, IsKleinFour.card_four]

/-- The two elementary eight-groups in (S ∩ K)S_C form one S-orbit. -/
theorem four_join_conjugate :
    ∃ s ∈ d.S, rightConjugate s (d.SC ⊔ fourZero d) = d.SC ⊔ fourOne d := by
  obtain ⟨s, hs, he⟩ := four_conjugate d
  have hn : d.S ≤ normalizer (d.SC : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.sc_le_s).mp d.normal_sc
  have hc : rightConjugate s d.SC = d.SC :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.SC : Set G)).inv_mem (hn hs))
  refine ⟨s, hs, ?_⟩
  change (d.SC ⊔ fourZero d).map _ = _
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hc he

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
