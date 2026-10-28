module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import Theory.GroupTheory.SolvableRadical.SolvableKernel


/-!
# Quotients, Sylow normalizers and all conjugate components in 15.3.49(k)

The restriction of the star projection identifies each relatively subnormal
subgroup modulo its intrinsic two-core with its actual image. For L₀ = ⟨L^T⟩,
Sylow maximality puts the kernel in T₀ = T ∩ L₀. The relative normalizer then
maps onto the intrinsic normalizer of T₀*, with kernel its intersection with
O₂(H). The first-isomorphism equivalence and solvability equivalence retain
these actual subgroups, without replacing L₀ by L.

The finite family of all T-conjugate star components generates L₀*. Each
member is Y₀*-invariant and is multiplicatively equivalent to L*. Once the
classification supplies quasisimplicity, distinct members commute. These
facts prepare the componentwise Borel and automorphism calculations.

This module does not classify L*, exclude the exceptional models, or prove
solvability of the concrete model Borels. In particular the two-core quotient
here is not identified with A.3.18's prime-to-three core quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144, proof of 15.3.49(i)–(k); the elementary quotient correspondence
and Sylow restriction are the steps implicit in the Borel identification.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection
universe u
variable {G : Type u} [Group G]

/-- Restriction of the actual star projection to an ambient subgroup. -/
noncomputable def starProjection (H K : Subgroup G) (hKH : K ≤ H) :
    K →* starImage H K :=
  ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (K.subgroupOf H)).comp
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom

theorem starProjection_surjective (H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starProjection H K hKH) :=
  ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hKH).symm.surjective

theorem starProjection_map (H K D : Subgroup G) (hKH : K ≤ H) (hDK : D ≤ K) :
    (D.subgroupOf K).map (starProjection H K hKH) =
      (starImage H D).subgroupOf (starImage H K) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hKH a.property⟩, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, hDK ha⟩, ha, Subtype.ext he⟩

theorem starProjection_ker [Finite G] (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) :
    (starProjection H K hKH).ker = pCore 2 K := by
  let e := (subgroupOfEquivOfLe hKH).symm
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso]
  change ((MonoidHom.ker ((QuotientGroup.mk' (pCore 2 H)).subgroupMap
    (K.subgroupOf H))).comap e.toMonoidHom).map e.toMonoidHom = _
  rw [map_comap_eq_self_of_surjective e.surjective, ker_subgroupMap,
    QuotientGroup.ker_mk', pCore_subnormal_eq_comap 2 hK]
  rfl

/-- The full relatively subnormal subgroup has its intrinsic two-core quotient
as its star image; it need not be a single component. -/
noncomputable def starQuotientEquiv [Finite G] (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) :
    (K ⧸ pCore 2 K) ≃* starImage H K :=
  (QuotientGroup.quotientMulEquivOfEq (starProjection_ker H K hKH hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (starProjection_surjective H K hKH))

/-- Normalizers commute with this quotient when its kernel is in the subgroup. -/
theorem starProjection_normalizer_comap (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    (normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K))).comap
      (starProjection H K hKH) = (K ⊓ normalizer (D : Set G)).subgroupOf K := by
  rw [← starProjection_map H K D hKH hDK,
    comap_normalizer_eq_of_surjective _ (starProjection_surjective H K hKH),
    comap_map_eq_self hk]
  change normalizer (D.subgroupOf K) = K.subgroupOf K ⊓
    (normalizer (D : Set G)).subgroupOf K
  rw [subgroupOf_self, top_inf_eq, subgroupOf_normalizer_eq hDK]

theorem starProjection_normalizer_map (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    ((K ⊓ normalizer (D : Set G)).subgroupOf K).map (starProjection H K hKH) =
      normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K)) := by
  rw [← starProjection_normalizer_comap H K D hKH hDK hk,
    map_comap_eq_self_of_surjective (starProjection_surjective H K hKH)]

/-- The actual relative normalizer maps onto the intrinsic star normalizer. -/
noncomputable def normalizerProjection (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    (K ⊓ normalizer (D : Set G) : Subgroup G) →*
      normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K)) :=
  (MulEquiv.subgroupCongr (starProjection_normalizer_map H K D hKH hDK hk)).toMonoidHom.comp
    (((starProjection H K hKH).subgroupMap
      ((K ⊓ normalizer (D : Set G)).subgroupOf K)).comp
        (subgroupOfEquivOfLe (show K ⊓ normalizer (D : Set G) ≤ K from inf_le_left)).symm.toMonoidHom)

theorem normalizerProjection_surjective (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    Function.Surjective (normalizerProjection H K D hKH hDK hk) :=
  (MulEquiv.subgroupCongr (starProjection_normalizer_map H K D hKH hDK hk)).surjective.comp
    (((starProjection H K hKH).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe (show K ⊓ normalizer (D : Set G) ≤ K from inf_le_left)).symm.surjective)

/-- The kernel is the intersection with O₂(H), with the relative inclusion explicit. -/
theorem normalizerProjection_ker (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    (normalizerProjection H K D hKH hDK hk).ker =
      (pCore 2 H).comap (inclusion
        ((show K ⊓ normalizer (D : Set G) ≤ K from inf_le_left).trans hKH)) := by
  ext x
  constructor
  · intro hx
    change (⟨(x : G), hKH x.property.1⟩ : H) ∈ pCore 2 H
    apply (QuotientGroup.eq_one_iff _).mp
    have hx' : normalizerProjection H K D hKH hDK hk x = 1 := hx
    exact congrArg (fun y : normalizer
      ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K)) =>
        ((y : starImage H K) : H ⧸ pCore 2 H)) hx'
  · intro hx
    change (⟨(x : G), hKH x.property.1⟩ : H) ∈ pCore 2 H at hx
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hx

/-- First-isomorphism identification of the genuine normalizer quotient. -/
noncomputable def normalizerQuotientEquiv (H K D : Subgroup G) (hKH : K ≤ H)
    (hDK : D ≤ K) (hk : (starProjection H K hKH).ker ≤ D.subgroupOf K) :
    ((K ⊓ normalizer (D : Set G) : Subgroup G) ⧸
      (normalizerProjection H K D hKH hDK hk).ker) ≃*
      normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K)) :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (normalizerProjection_surjective H K D hKH hDK hk)

variable [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

omit [Finite G] in
theorem closure_le : localSpan L T ≤ H := d.replacement ▸ le_sup_left

omit [Finite G] in
theorem sylow_le : (T : Subgroup G) ≤ H :=
  d.replacement ▸ le_sup_right.trans le_sup_right

omit [Finite G] in
theorem component_le : L ≤ H := (le_conjugateSpanBy L T).trans (closure_le d)

omit [Finite G] in
theorem closure_normal : ((localSpan L T).subgroupOf H).Normal := by
  rw [d.replacement]
  exact componentClosure_normal_in_replacement L Y0 (T : Subgroup G)
    (le_normalizer_iff_commutator_le_left.mpr d.commutator_eq.ge) d.sylow_normalizes

omit [Finite G] in
theorem sylow_in_H : IsSylowIn 2 (T : Subgroup G) H := by
  refine ⟨T.subtype (sylow_le d), ?_⟩
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (sylow_le d)]

theorem closure_inter_sylow :
    IsSylowIn 2 ((T : Subgroup G) ⊓ localSpan L T) (localSpan L T) ∧
    IsSylowIn 2 (starImage H ((T : Subgroup G) ⊓ localSpan L T))
      (starImage H (localSpan L T)) := by
  have hs := CFSG.Quasithin.Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (sylow_in_H d) (closure_le d) (closure_normal d).isSubnormal
  exact ⟨hs, BinaryModels.starImage_isSylowIn _ _ _
    (inf_le_right.trans (closure_le d)) (closure_le d) hs⟩

omit [Finite G] in
theorem closure_projection_ker_le_inter :
    (starProjection H (localSpan L T) (closure_le d)).ker ≤
      ((T : Subgroup G) ⊓ localSpan L T).subgroupOf (localSpan L T) := by
  intro x hx
  have hx' : (⟨x, closure_le d x.property⟩ : H) ∈ pCore 2 H :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
  exact ⟨pCore_isPGroup.le_sylow_of_normal (T.subtype (sylow_le d)) hx', x.property⟩

/-- Solvability of the intrinsic star normalizer is equivalent to solvability
of the actual relative normalizer in G. -/
theorem borel_isSolvable_iff :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) ↔
    Group.IsSolvable (normalizer
      ((starImage H ((T : Subgroup G) ⊓ localSpan L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T)))) := by
  let K := localSpan L (T : Subgroup G)
  let D := (T : Subgroup G) ⊓ K
  let B := K ⊓ normalizer (D : Set G)
  let f := starProjection H K (closure_le d)
  let N := normalizer ((starImage H D).subgroupOf (starImage H K) : Set (starImage H K))
  have he : N.comap f = B.subgroupOf K :=
    starProjection_normalizer_comap H K D (closure_le d) inf_le_right
      (closure_projection_ker_le_inter d)
  have hm : (B.subgroupOf K).map f = N :=
    starProjection_normalizer_map H K D (closure_le d) inf_le_right
      (closure_projection_ker_le_inter d)
  let e := subgroupOfEquivOfLe (show B ≤ K from inf_le_left)
  constructor
  · intro hB
    let _ := hB
    let : Group.IsSolvable (B.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    change Group.IsSolvable N
    rw [← hm]
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  · intro hN
    let _ := hN
    have hk : IsPGroup 2 f.ker := by
      rw [starProjection_ker H K (closure_le d) (closure_normal d).isSubnormal]
      exact pCore_isPGroup
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let : Group.IsSolvable (B.subgroupOf K) :=
      he ▸ isSolvable_comap_of_solvable_ker f N
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

/-- The selected component remains a C-component in the actual two-core quotient. -/
theorem star_isCComponent : (starImage H L).IsCComponent := by
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact d.component_in_H.map_quotient (pCore 2 H)

/-- The relative component on which B.5.3 must be applied. -/
theorem star_isCComponent_in_span :
    ((starImage H L).subgroupOf (starImage H (localSpan A H))).IsCComponent :=
  (star_isCComponent d).subgroupOf (map_mono (comap_mono d.component_le))

/-- Quasisimplicity transports across the actual intrinsic quotient equivalence. -/
theorem component_quotient_quasisimple_iff :
    Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L) ↔
      Theory.GroupTheory.IsQuasisimple (starImage H L) := by
  let e := starQuotientEquiv H L (component_le d) d.component_in_H.subnormal
  constructor
  · intro h
    let _ := h
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv e
  · intro h
    let _ := h
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm

omit [Finite G] in
/-- Conjugate components have isomorphic star images, via actual conjugation. -/
noncomputable def conjugateStarEquiv (t : T) :
    starImage H L ≃* starImage H (L.map (MulAut.conj (t : G)).toMonoidHom) := by
  rw [starImage_map_conj H L (component_le d) ⟨t, sylow_le d t.property⟩]
  exact (starImage H L).equivMapOfInjective
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨t, sylow_le d t.property⟩)).toMonoidHom
    (MulAut.conj _).injective

theorem conjugate_star_isCComponent (t : T) :
    (starImage H (L.map (MulAut.conj (t : G)).toMonoidHom)).IsCComponent := by
  rw [starImage_map_conj H L (component_le d) ⟨t, sylow_le d t.property⟩]
  exact (star_isCComponent d).map_equiv (MulAut.conj _)

omit d [Finite G] in
theorem lieModel_transport {D E : Type u} [Group D] [Group E]
    (f : D ≃* E) {e : ℕ} (h : LieComponentModel D e) : LieComponentModel E e := by
  cases h with
  | linear_two he F hF m => exact .linear_two he F hF (m.map (f.symm.trans ·))
  | linear_three he F hF m => exact .linear_three he F hF (m.map (f.symm.trans ·))
  | symplectic he F hF m => exact .symplectic he F hF (m.map (f.symm.trans ·))
  | g2 he F hF m => exact .g2 he F hF (m.map (f.symm.trans ·))
  | binary_linear he n hn m => exact .binary_linear he n hn (m.map (f.symm.trans ·))

omit [Finite G] in
theorem conjugate_lieModel {e : ℕ} (h : LieComponentModel (starImage H L) e) (t : T) :
    LieComponentModel (starImage H (L.map (MulAut.conj (t : G)).toMonoidHom)) e :=
  lieModel_transport (conjugateStarEquiv d t) h

omit d [Finite G] in
private theorem localSpan_eq_iSup (L T : Subgroup G) :
    localSpan L T = ⨆ t : T, L.map (MulAut.conj (t : G)).toMonoidHom := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro x ⟨t, ht, l, hl, rfl⟩
    exact (le_iSup (fun t : T => L.map (MulAut.conj (t : G)).toMonoidHom) ⟨t, ht⟩)
      ⟨l, hl, rfl⟩
  · apply iSup_le
    intro t x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact subset_closure ⟨t, t.property, l, hl, rfl⟩

/-- All distinct T-conjugate star components, with no orbit-size restriction. -/
noncomputable def conjugateFactors (H L : Subgroup G) (T : Sylow 2 G) :
    Finset (Subgroup (H ⧸ pCore 2 H)) := by
  classical
  let _ := Fintype.ofFinite T
  exact Finset.univ.image (fun t : T => starImage H (L.map (MulAut.conj (t : G)).toMonoidHom))

omit d in
theorem mem_conjugateFactors {C : Subgroup (H ⧸ pCore 2 H)} :
    C ∈ conjugateFactors H L T ↔
      ∃ t : T, C = starImage H (L.map (MulAut.conj (t : G)).toMonoidHom) := by
  classical
  simp only [conjugateFactors, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem conjugateFactors_properties (C : Subgroup (H ⧸ pCore 2 H))
    (hC : C ∈ conjugateFactors H L T) :
    C.IsCComponent ∧ C ≤ starImage H (localSpan L T) ∧
      starImage H Y0 ≤ normalizer (C : Set (H ⧸ pCore 2 H)) ∧
      Nonempty (starImage H L ≃* C) := by
  obtain ⟨t, rfl⟩ := mem_conjugateFactors.mp hC
  refine ⟨conjugate_star_isCComponent d t, ?_,
    d.conjugate_star_normalized t t.property, ⟨conjugateStarEquiv d t⟩⟩
  apply map_mono (comap_mono ?_)
  intro x hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact subset_closure ⟨t, t.property, l, hl, rfl⟩

/-- The finite family generates the whole star closure, including every orbit. -/
theorem conjugateFactors_sup :
    (conjugateFactors H L T).sup id = starImage H (localSpan L T) := by
  have hCH (t : T) : L.map (MulAut.conj (t : G)).toMonoidHom ≤ H := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact closure_le d (subset_closure ⟨t, t.property, l, hl, rfl⟩)
  have hi : (localSpan L T).subgroupOf H =
      ⨆ t : T, (L.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (closure_le d), Subgroup.map_iSup]
    simp_rw [map_subgroupOf_eq_of_le (hCH _)]
    exact localSpan_eq_iSup L T
  have hstar : starImage H (localSpan L T) =
      ⨆ t : T, starImage H (L.map (MulAut.conj (t : G)).toMonoidHom) := by
    unfold starImage
    rw [hi, Subgroup.map_iSup]
  apply le_antisymm
  · exact Finset.sup_le fun C hC => (conjugateFactors_properties d C hC).2.1
  · rw [hstar]
    apply iSup_le
    intro t
    exact Finset.le_sup (f := id) (mem_conjugateFactors.mpr ⟨t, rfl⟩)

/-- Once classification establishes quasisimplicity, all distinct members
of the actual factor family commute. -/
theorem conjugateFactors_commute
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (C D : Subgroup (H ⧸ pCore 2 H))
    (hC : C ∈ conjugateFactors H L T) (hD : D ∈ conjugateFactors H L T)
    (hne : C ≠ D) : C ≤ centralizer (D : Set (H ⧸ pCore 2 H)) := by
  let _ := hq
  obtain ⟨hCc, _, _, ⟨eC⟩⟩ := conjugateFactors_properties d C hC
  obtain ⟨hDc, _, _, ⟨eD⟩⟩ := conjugateFactors_properties d D hD
  have hC' : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) C :=
    ⟨hCc.subnormal, Theory.GroupTheory.IsQuasisimple.of_mulEquiv eC⟩
  have hD' : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) D :=
    ⟨hDc.subnormal, Theory.GroupTheory.IsQuasisimple.of_mulEquiv eD⟩
  exact commutator_eq_bot_iff_le_centralizer.mp (hC'.commutator_eq_bot_of_ne hD' hne)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection
