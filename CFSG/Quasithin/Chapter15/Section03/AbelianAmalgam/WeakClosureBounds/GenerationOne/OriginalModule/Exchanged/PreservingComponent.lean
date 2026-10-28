module
public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.ImageRatio
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Restriction
public import Theory.Representation.BinaryOffender.Homogeneous.TypeSelection
public import Theory.Representation.BinaryOffender.SemisimpleFixedSpace
public import Theory.Representation.BinaryOffender.SemisimpleIrrPlus

/-!
# Borel fixation from a component-preserving minimal actor

Select a homogeneous member of the same type as each nontrivial simple
component constituent. Clifford semisimplicity removes its central fixed
space. D.2.5 and the quadratic orbit argument preserve this member and give
the ratio bound in the actual image of the component-actor supplement.
The B.4 classifier then recognizes its natural action, whose actual Sylow
normalizer has zero fixed space. Type transport and the semisimple direct
sum give the fixed-space inclusion on the original component restriction.

This argument permits the original actor to have a kernel on the component;
only its noncentral conjugation action is required. It is the restriction
and multiplicity step of the preserving branch of Aschbacher–Smith D.3.6–7,
pp.196–199, used in F.9.18 and original 15.3.65, p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) G V)

private def centralImageEquiv (K : Subgroup G) (I : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ I) (hf : I ⊓ fixedSpace ρ K = ⊥) :
    (invariantSubspace ρ K I hs).toRepresentation ≃ₗ
      (quotientImage ρ K I hs).toRepresentation := by
  let q := (fixedSpace ρ K).mkQ
  let f : I →ₗ[ZMod 2] (quotientImage ρ K I hs).toSubmodule :=
    (q.comp I.subtype).codRestrict _ (fun v => ⟨v,v.property,rfl⟩)
  have hfi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hc : (v : V) - w ∈ fixedSpace ρ K := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change q ((v : V) - w) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val he)
    have hz : (v : V) - w ∈ I ⊓ fixedSpace ρ K :=
      ⟨I.sub_mem v.property w.property,hc⟩
    rwa [hf] at hz
  have hfs : Function.Surjective f := by
    rintro ⟨v,w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hfi,hfs⟩,?_⟩
  intro k
  ext v
  rfl

omit [Finite G] [Finite V] in
theorem fixedSpace_eq_bot_of_same_central_type
    {K : Subgroup G} {I J : Submodule (ZMod 2) V}
    (hI : K ≤ subspaceStabilizer ρ I) (hJ : K ≤ subspaceStabilizer ρ J)
    (hfI : I ⊓ fixedSpace ρ K = ⊥) (hfJ : J ⊓ fixedSpace ρ K = ⊥)
    (he : SameModule (quotientImage ρ K I hI) (quotientImage ρ K J hJ))
    (B : Subgroup K) (hz : fixedSpace (invariantSubspace ρ K J hJ).toRepresentation B = ⊥) :
    fixedSpace (invariantSubspace ρ K I hI).toRepresentation B = ⊥ := by
  let e := ((centralImageEquiv ρ K I hI hfI).trans
    ((sameModule_iff_repEquiv _ _).mp he).some).trans (centralImageEquiv ρ K J hJ hfJ).symm
  apply bot_unique
  intro v hv
  have hev : e v ∈ fixedSpace (invariantSubspace ρ K J hJ).toRepresentation B := by
    intro b
    have h := LinearMap.congr_fun (e.isIntertwining' b) v
    exact h.symm.trans (congrArg e (hv b))
  have he0 : e v = 0 := by rwa [hz] at hev
  exact e.toLinearEquiv.injective (he0.trans (map_zero e.toLinearEquiv).symm)

theorem stable_constituent_borel_zero
    {K C : Subgroup G} [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple G)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K C I)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hC : C ∈ RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    (hn : ¬ C ≤ centralizer (K : Set G))
    {f : ℕ} (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (invariantSubspace ρ K I hI.invariant).toRepresentation B = ⊥ := by
  obtain ⟨hD,hbound⟩ := stable_section_image_bound ρ hI
    (hI.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ) hZ hC hq hn
  let D := K ⊔ C
  let L := K.subgroupOf D
  let σ : Representation (ZMod 2) D I := (invariantSubspace ρ D I hD).toRepresentation
  let e : L ≃* K := subgroupOfEquivOfLe (show K ≤ D from le_sup_left)
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer (show K ≤ D from le_sup_left)).mpr
    (sup_le K.le_normalizer hI.normalizes)
  let : IsQuasisimple L := Normal.componentInSup_quasisimple K C
  have hquot : IsPGroup 2 (D ⧸ L) := by
    let : IsElementaryAbelian 2 C := hC.1.1.2
    exact isPGroup_quotient_of_sup_eq_top L (C.subgroupOf D)
      (IsElementaryAbelian.isPGroup 2 C).comap_subtype (Normal.componentInSup_generated K C)
  have hi : IsIrreducible (σ.comp L.subtype) := by
    have hir := hI.isIrrPlus.irreducible_of_semisimple ρ
    let τ := (invariantSubspace ρ K I hI.invariant).toRepresentation
    have heq : σ.comp L.subtype = τ.comp e.toMonoidHom := rfl
    rw [heq]
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective τ).mpr hir
  have hnσ : ¬ (⊤ : Submodule (ZMod 2) I) ≤ fixedSpace σ L := by
    intro h
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    intro v hv k
    exact congrArg Subtype.val (h (show (⟨v,hv⟩ : I) ∈ (⊤ : Submodule (ZMod 2) I) from Submodule.mem_top) (e.symm k))
  let B' := B.comap e.toMonoidHom
  have hB' : ∃ P : Sylow 2 L, normalizer (P : Set L) = B' :=
    exists_sylow_normalizer_of_equiv e B' B
      (Subgroup.map_comap_eq_self_of_surjective e.surjective B) hB
  have hz := Normal.fixedSpace_eq_bot_of_image_quadraticRatio σ L (hs.subgroup D)
    hquot (Normal.componentInSup_center K C hZ) hi hnσ hbound
    (Normal.componentInSup_model K C hm) hf ho
    B' hB'
  apply bot_unique
  intro v hv
  have hv' : v ∈ fixedSpace (σ.comp L.subtype) B' := by
    intro b
    exact hv ⟨e b,b.property⟩
  rwa [hz] at hv'

theorem component_fixedSpace_le_of_minimal_actor
    (K C : Subgroup G) [IsQuasisimple K]
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple G)
    [IsSemisimpleRepresentation (ρ.comp K.subtype)]
    (hCN : C ≤ normalizer (K : Set G)) (hn : ¬ C ≤ centralizer (K : Set G))
    (hC : C ∈ RPlusBound ρ 2) (hq : IsQuadratic ρ C)
    {f : ℕ} (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  have hfix : fixedSpace (ρ.comp K.subtype) ⊤ = fixedSpace ρ K := by
    ext v
    exact ⟨fun h k => h ⟨k,mem_top k⟩,fun h k => h k⟩
  apply fixedSpace_le_top_of_semisimple_alternatives (ρ.comp K.subtype) B
  intro S hS
  by_cases hnS : S.toSubmodule ≤ fixedSpace ρ K
  · exact Or.inl (hfix ▸ hnS)
  · right
    have hSI := isIrrPlus_of_simple_noncentral ρ K S hS hnS
    let : IsElementaryAbelian 2 C := hC.1.1.2
    obtain ⟨J,_,hJ,htype⟩ := exists_isIrrPlusWith_le_orbitSpan_sameModule ρ hCN
      (IsElementaryAbelian.isPGroup 2 C) hSI
    have hz := stable_constituent_borel_zero ρ hZ hs hJ hC hq hn hm hf ho B hB
    exact fixedSpace_eq_bot_of_same_central_type ρ hSI.choose hJ.invariant
      (hSI.inf_fixedSpace_eq_bot_of_semisimple ρ)
      (hJ.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple ρ) htype B hz

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
