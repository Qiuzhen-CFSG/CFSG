module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed points of three-elements in the intersection of the normalizers

An element of order three in N(E) ∩ N(F) fixes only the identity on E.
The actual S₅ complement gives |N(F)| = 1920. The marked involution has
stabilizer of order 128 in its conjugation action on F, so its orbit is
all fifteen nonidentity elements. Every such point stabilizer is a
two-group, and an element of order three therefore fixes only 1 on F.

Consequently B = E ∩ C_G(x) embeds in the genuine quotient N(F)/F. Its
image centralizes the nontrivial order-three image of x in S₅, so |B|
divides 6. It also divides |E| = 16, while orbit counting for ⟨x⟩ on E
gives |B| ≡ 16 modulo 3. These constraints force |B| = 1.

The actor x is an explicit input; its construction remains with the
intersection-actor assembly. Only the F-normalizer complement from the
involution-normalizer data is needed, with no ambient three-fusion or
recognition assumption.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed p.8, paragraph preceding Lemma 8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem normalizer_F_card (h2 : InvolutionNormalizerData D k) :
    Nat.card (normalizer (CaseII.F D k : Set G)) = 1920 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := h2.normalizer_F
  have hR : Nat.card ((CaseII.F D k).subgroupOf
      (normalizer (CaseII.F D k : Set G))) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv,
      CaseII.F_card]
  have hC : Nat.card K = 120 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [← hK.card_mul_card, hR, hC]

private theorem normalizer_F_three_fixed_point_free (h2 : InvolutionNormalizerData D k)
    (x : G) (hxF : x ∈ normalizer (CaseII.F D k : Set G)) (hx : orderOf x = 3) :
    ∀ f ∈ CaseII.F D k, Commute x f → f = 1 := by
  let N := normalizer (CaseII.F D k : Set G)
  let z : CaseII.F D k := ⟨D.z, by
    rw [← CaseII.into_z_zero D k, ← CaseII.modelF_map D k]
    exact mem_map_of_mem _ CaseII.modelF_generators.1⟩
  have hz : z ≠ 1 := fun h => D.z_ne_one (congrArg Subtype.val h)
  have hstab : MulAction.stabilizer N z =
      (N ⊓ D.centralizer).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (n : G) * D.z * (n : G)⁻¹ = D.z ↔
      (n : G) ∈ N ∧ (n : G) ∈ D.centralizer
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨n.property, h⟩, fun h => h.2⟩
  have hstabcard : Nat.card (MulAction.stabilizer N z) = 128 := by
    rw [hstab, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
      CaseII.normalizer_F_inf_centralizer]
    exact (Nat.card_congr ((CaseII.caseIISylow D k).equiv D.sylow).toEquiv).trans
      D.sylow_card
  have horbitsub : MulAction.orbit N z ⊆ ({1}ᶜ : Set (CaseII.F D k)) := by
    intro f hf hf1
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hf
    exact hz ((MulAction.injective g) (by simpa using hf1))
  have horbit : MulAction.orbit N z = ({1}ᶜ : Set (CaseII.F D k)) := by
    apply Set.eq_of_subset_of_ncard_le horbitsub
    have hc := (MulAction.stabilizer N z).card_mul_index
    rw [hstabcard, MulAction.index_stabilizer, normalizer_F_card D k h2] at hc
    rw [Set.ncard_compl, Set.ncard_singleton, CaseII.F_card]
    omega
  intro f hf hxf
  by_contra hf1
  let fF : CaseII.F D k := ⟨f, hf⟩
  have hfO : fF ∈ MulAction.orbit N z := by
    rw [horbit]
    exact fun h => hf1 (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hfO
  have hfcard : Nat.card (MulAction.stabilizer N fF) = 128 := by
    rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv,
      hstabcard]
  let q : N := ⟨x, hxF⟩
  have hq : q ∈ MulAction.stabilizer N fF := by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hxf.eq
  have hq3 : orderOf q = 3 := (orderOf_coe q).symm.trans hx
  have hd := (MulAction.stabilizer N fF).orderOf_dvd_natCard hq
  rw [hq3, hfcard] at hd
  norm_num at hd


private theorem fixed_subgroup_card_mod_three (H : Subgroup G) (x : G)
    (hxH : x ∈ normalizer (H : Set G)) (hx : orderOf x = 3) :
    Nat.card ↥(H ⊓ centralizer ({x} : Set G)) % 3 = Nat.card H % 3 := by
  let N := normalizer (H : Set G)
  let q : N := ⟨x, hxH⟩
  let Q := zpowers q
  have hq : orderOf q = 3 := (orderOf_coe q).symm.trans hx
  have hQ : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hq, pow_one])
  have hfixed (y : H) : y ∈ MulAction.fixedPoints Q H ↔ Commute x (y : G) := by
    constructor
    · intro hy
      have h := hy ⟨q, mem_zpowers q⟩
      have he : x * (y : G) * x⁻¹ = (y : G) := congrArg Subtype.val h
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hy
      have hstab : Q ≤ MulAction.stabilizer N y := zpowers_le.mpr (by
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr hy.eq)
      intro a
      exact hstab a.property
  let e : MulAction.fixedPoints Q H ≃ ↥(H ⊓ centralizer ({x} : Set G)) :=
    { toFun := fun y => ⟨y.val, y.val.property,
        mem_centralizer_singleton_iff.mpr ((hfixed y.val).mp y.property).symm.eq⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩, (hfixed _).mpr
        (mem_centralizer_singleton_iff.mp y.property.2).symm⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }
  have hmod := hQ.card_modEq_card_fixedPoints H
  change Nat.card H % 3 = Nat.card (MulAction.fixedPoints Q H) % 3 at hmod
  rw [Nat.card_congr e] at hmod
  exact hmod.symm

private theorem quotient_centralizer_card_dvd_six {A : Type*} [Group A]
    (R B : Subgroup A) [R.Normal] (hR : ¬ 3 ∣ Nat.card R)
    (q : A) (hq : orderOf q = 3) (hB : Disjoint B R)
    (hcomm : B ≤ centralizer ({q} : Set A))
    (e : A ⧸ R ≃* Equiv.Perm (Fin 5)) : Nat.card B ∣ 6 := by
  let f : A →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' R)
  have hfq : orderOf (f q) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, (orderOf_eq_prime_iff.mp hq).1, map_one]
    · intro h
      have hqR : q ∈ R := (QuotientGroup.eq_one_iff q).mp (e.injective (by
        simpa [f] using h))
      exact hR (hq ▸ R.orderOf_dvd_natCard hqR)
  let g : B →* Equiv.Perm (Fin 5) := f.comp B.subtype
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_one g).mpr
    intro b hb
    have hbR : (b : A) ∈ R := (QuotientGroup.eq_one_iff (b : A)).mp (e.injective (by
      simpa [f, g] using hb))
    exact Subtype.ext (Subgroup.disjoint_def.mp hB b.property hbR)
  apply Theory.SpecificGroups.SymmetricFive.card_dvd_six_of_centralizes_three (f q) hfq g hg
  intro b
  simpa only [map_mul, g, MonoidHom.comp_apply, Subgroup.subtype_apply] using
    congrArg f (mem_centralizer_singleton_iff.mp (hcomm b.property))

/-- Every element of order three normalizing E and F fixes only the identity on E. -/
public theorem intersection_three_fixed_point_free (h2 : InvolutionNormalizerData D k)
    (x : G) (hxE : x ∈ normalizer (CaseII.E D k : Set G))
    (hxF : x ∈ normalizer (CaseII.F D k : Set G)) (hx : orderOf x = 3) :
    ∀ e ∈ CaseII.E D k, Commute x e → e = 1 := by
  let N := normalizer (CaseII.F D k : Set G)
  let R := (CaseII.F D k).subgroupOf N
  let B := CaseII.E D k ⊓ centralizer ({x} : Set G)
  have hEN : CaseII.E D k ≤ N :=
    (CaseII.E_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_F D k)
  have hBN : B ≤ N := inf_le_left.trans hEN
  have hRcard : Nat.card R = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv,
      CaseII.F_card]
  let q : N := ⟨x, hxF⟩
  have hq : orderOf q = 3 := (orderOf_coe q).symm.trans hx
  have hdis : Disjoint (B.subgroupOf N) R := by
    apply Subgroup.disjoint_def.mpr
    intro b hb hbR
    apply Subtype.ext
    exact normalizer_F_three_fixed_point_free D k h2 x hxF hx b hbR
      (mem_centralizer_singleton_iff.mp hb.2).symm
  have hcomm : B.subgroupOf N ≤ centralizer ({q} : Set N) := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hb.2)
  obtain ⟨K, hK, ⟨eK⟩⟩ := h2.normalizer_F
  let eqS : N ⧸ R ≃* Equiv.Perm (Fin 5) := hK.symm.QuotientMulEquiv.trans eK
  have hd6 := quotient_centralizer_card_dvd_six R (B.subgroupOf N)
    (by rw [hRcard]; norm_num) q hq hdis hcomm eqS
  rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv] at hd6
  have hd16 : Nat.card B ∣ 16 := by
    have h := card_dvd_of_le (show B ≤ CaseII.E D k from inf_le_left)
    rwa [CaseII.E_card] at h
  have hmod := fixed_subgroup_card_mod_three (CaseII.E D k) x hxE hx
  rw [CaseII.E_card] at hmod
  change Nat.card B % 3 = 16 % 3 at hmod
  have hd2 : Nat.card B ∣ 2 := Nat.dvd_gcd hd6 hd16
  have hcard : Nat.card B = 1 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd2
    omega
  have hbot : B = ⊥ := Subgroup.card_eq_one.mp hcard
  intro e he hxe
  have hb : e ∈ B := ⟨he, mem_centralizer_singleton_iff.mpr hxe.symm.eq⟩
  rwa [hbot, mem_bot] at hb

end Theory.GroupTheory.HeldM22A10.M22Identification
