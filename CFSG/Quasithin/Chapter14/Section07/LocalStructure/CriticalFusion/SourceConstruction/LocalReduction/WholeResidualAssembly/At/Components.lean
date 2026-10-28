module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CComponent.UniqueResidual

/-!
# The original component and its full movement from 14.7.47

All structural input is at the same original G,T. The earlier component
rows give simple intrinsic two-core quotients. Thus the actual images in
I/O₂(I) are centerless ordinary components. Their common nonzero point
cubic proves uniqueness, hence relative normality in I. Normality and
[V,L₁] = V then prove movement of the entire original conjugate span.

We also construct the literal reduced local C T and prove that the
centralizer of the component image is solvable. Neither the existence of
a component nor vanishing of that solvable centralizer is assumed here.
Those are the remaining earlier 14.7.27–29 steps in the guarded assembly.
The universal exports are unchanged.
Source: Aschbacher–Smith 14.7.47–48, printed pp.1063–1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

/-- Simplicity belongs to the actual carriers in the preceding source list. -/
theorem ComponentRows.isSimpleGroup {X : Type*} [Group X]
    (hm : ComponentRows X) : IsSimpleGroup X := by
  rcases hm with ⟨n,hn,_,⟨e⟩⟩ | ⟨n,hn,_,⟨e⟩⟩ | he
  · let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
      Atlas.psl_simple_high_rank n hn
    let : IsSimpleGroup SL(n,ZMod 2) :=
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm.isSimpleGroup
    exact e.isSimpleGroup
  · let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    exact e.isSimpleGroup

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual quotient component is ordinary and centerless directly from
14.7.47; no universal structural classification is needed. -/
theorem local_component_star_of_earlier14747
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    IsComponent (HStar I) (C.map (QuotientGroup.mk' (pCore 2 I))) ∧
      center (C.map (QuotientGroup.mk' (pCore 2 I))) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let := pCore_isNilpotent (p := 2) (G := I)
  have hB := hC.map_quotient (pCore 2 I)
  let := hB.perfect
  have hm : ComponentRows B :=
    (source47 I hI C hC).2.of_equiv (cComponentTwoCoreQuotientEquiv hC)
  let : IsSimpleGroup B := hm.isSimpleGroup
  have hz : center B = ⊥ := hm.center_and_outer.1
  exact ⟨⟨hB.subnormal,⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩⟩,hz⟩

/-- Quasisimplicity of the intrinsic component quotient, transported through
its exact image in the original star quotient. -/
theorem local_component_twoCore_of_earlier14747
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) : IsQuasisimple (C ⧸ pCore 2 C) := by
  let := (local_component_star_of_earlier14747 source47 I hI C hC).1.2
  exact IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm

private theorem local_point_image_ne_bot_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≠ ⊥ := by
  intro he
  have hAQ : (F.Li L 1).subgroupOf I ≤ pCore 2 I := by
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hA2 : IsPGroup 2 (F.Li L 1) :=
    (pCore_isPGroup.to_le hAQ).of_equiv (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI))
  have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
    have hd := card_quotient_dvd_card (pCore 2 (F.Li L 1))
    rwa [pointResidual_core_quotient_card_at h structural] at hd
  obtain ⟨n,hn⟩ := hA2.exists_card_eq
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hn ▸ hdiv)
  norm_num at h32

omit [Finite G] in
private theorem point_le_component_image
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
      C.map (QuotientGroup.mk' (pCore 2 I)) := by
  apply map_mono
  intro x hx
  obtain ⟨c,hc,he⟩ := (source47 I hI C hC).1 hx
  exact (show c = x from Subtype.ext he) ▸ hc

/-- Common containment of the actual nonzero point cubic forces uniqueness
at the original local subgroup. -/
theorem local_unique_component_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ∀ D : Subgroup I, D.IsCComponent → D = C := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let A := ((F.Li L 1).subgroupOf I).map q
  let B := C.map q
  let := pCore_isNilpotent (p := 2) (G := I)
  obtain ⟨hB,hz⟩ := local_component_star_of_earlier14747 source47 I hI C hC
  change center B = ⊥ at hz
  have hAB : A ≤ B := point_le_component_image source47 I hI C hC
  intro D hD
  by_contra hne
  have hD' := (local_component_star_of_earlier14747 source47 I hI D hD).1
  have hne' : D.map q ≠ B := fun he => hne (hD.eq_of_map_quotient_eq hC _ he)
  have hc := hD'.commutator_eq_bot_of_ne hB hne'
  have hAD : A ≤ D.map q := point_le_component_image source47 I hI D hD
  apply local_point_image_ne_bot_at h structural I hI
  apply eq_bot_iff.mpr
  intro a ha
  have hh : (⟨a,hAB ha⟩ : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hc) (hAD ha) b b.property)
  have he : (⟨a,hAB ha⟩ : B) = 1 := by simpa only [hz,mem_bot] using hh
  exact congrArg Subtype.val he

/-- Relative normality is derived from source component uniqueness. -/
theorem local_component_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) : C.Normal :=
  hC.normal_of_unique (local_unique_component_at h structural source47 I hI C hC)

/-- Source 14.7.48(2) for the entire original span, before any residual or
Sylow-supplement identification. -/
theorem local_component_full_movement_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ⁅F.UH I,C.map I.subtype⁆ = F.UH I := by
  let := local_component_normal_at h structural source47 I hI C hC
  have hn : I ≤ normalizer (C.map I.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
      (inferInstance : C.Normal)
  let := h.chosen.elementary
  exact (conjugateSpanBy_eq_commutator_of_seed V I (C.map I.subtype)
    (F.Li L 1) (map_subtype_le C) hn (source47 I hI C hC).1 (seed_commutator h F)).symm

/-- Full movement places the actual conjugate span inside the component,
with containment proved in the original ambient group. -/
theorem local_span_le_component_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) : F.UH I ≤ C.map I.subtype := by
  let := local_component_normal_at h structural source47 I hI C hC
  have hn : I ≤ normalizer (C.map I.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      C.le_normalizer_map I.subtype
  have hUI : F.UH I ≤ I :=
    conjugateSpanBy_le_self (h.chosen.le_sylow.trans (F.sylow_le_of_mem_Hz hI))
  rw [←local_component_full_movement_at h structural source47 I hI C hC]
  exact le_normalizer_iff_commutator_le_right.mp (hUI.trans hn)

/-- The literal component centralizer in I/O₂(I) is solvable: any component
in it would also be the unique component of I/O₂(I), forcing that perfect
component to be abelian. -/
theorem local_component_star_centralizer_solvable_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    Group.IsSolvable (centralizer
      (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I))) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let := pCore_isNilpotent (p := 2) (G := I)
  have hu := local_unique_component_at h structural source47 I hI C hC
  let := hC.normal_of_unique hu
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let N := centralizer (B : Set (HStar I))
  by_contra hs
  obtain ⟨D,hD⟩ := exists_isCComponent_of_not_isSolvable hs
  have he : D.map N.subtype = B := hC.unique_map_quotient hu _
    (hD.map_subtype (inferInstance : N.Normal).isSubnormal)
  have hBN : B ≤ N := he ▸ map_subtype_le D
  exact (hC.map_quotient _).not_isSolvable (Group.isSolvable_of_comm
    (fun a b : B => Subtype.ext ((hBN a.property) b b.property).symm))

/-- The source reduction is literally C T after common point containment;
its placement is derived from component escape at the same G,T. -/
theorem local_component_sylow_join_mem_Hz_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    C.map I.subtype ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)) := by
  let A := C.map I.subtype
  have hn : I ≤ normalizer (A : Set G) := by
    let := local_component_normal_at h structural source47 I hI C hC
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      C.le_normalizer_map I.subtype
  have he : conjugateSpanBy A (T : Subgroup G) = A :=
    le_antisymm (conjugateSpanBy_le le_rfl
      ((F.sylow_le_of_mem_Hz hI).trans hn)) (le_conjugateSpanBy _ _)
  have hJ := (local_component_reduced_mem_Hz_at h structural I hI C hC).2.2
  rw [he,←sup_assoc,sup_eq_left.mpr (source47 I hI C hC).1] at hJ
  exact hJ

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
