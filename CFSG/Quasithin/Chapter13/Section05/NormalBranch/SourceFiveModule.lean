module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairQuotient
public import Theory.Representation.BinaryPermutation.SixFiveRestriction

/-!
# The original six-letter natural module restricted to the A₅ pair

The chosen five-letter subgroup is the stabilizer of the fixed sixth letter.
The reusable restriction equivalence identifies its four-dimensional natural
module with the five-letter even core. In the original n=6 branch, the source
pair producer supplies the conjugated image of K and the same source
representatives; the quotient map and module action are transported literally.
No normalization by the original T is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.5.14(3–4), printed p.919.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveModule
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open BinaryPermutation.SixFiveRestriction
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  {K : Subgroup G} (hK : K ≤ D.L) (a : alternatingGroup (Fin 6))
  (hi : (K.subgroupOf D.L).map (localMap d) =
    FivePair.five.map (MulAut.conj a.val).toMonoidHom)

include hi in
private theorem image_mem (k : K) :
    localMap d (inclusion hK k) ∈ FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
  rw [← hi]
  exact mem_map_of_mem (localMap d) k.property

/-- Restrict the original natural actor and undo the source's chosen conjugation. -/
noncomputable def restrictedActor : K →* alternatingGroup (Fin 5) :=
  (conjugateActorEquiv a.val).toMonoidHom.comp
    (((localMap d).comp (inclusion hK)).codRestrict _ (by
      intro k
      exact image_mem d hK a hi k))

theorem restrictedActor_surjective : Function.Surjective (restrictedActor d hK a hi) := by
  intro b
  let x := (conjugateActorEquiv a.val).symm b
  have hx : x.val ∈ (K.subgroupOf D.L).map (localMap d) := hi.symm ▸ x.property
  obtain ⟨k,hk,he⟩ := hx
  have hk' : k.val ∈ K := hk
  refine ⟨⟨k.val,hk'⟩,?_⟩
  change conjugateActorEquiv a.val _ = b
  exact (congrArg (conjugateActorEquiv a.val) (show
    (((localMap d).comp (inclusion hK)).codRestrict _
      (fun k => image_mem d hK a hi k)) ⟨k.val,hk'⟩ = x from Subtype.ext he)).trans
      ((conjugateActorEquiv a.val).apply_symm_apply b)

theorem restrictedActor_ker : (restrictedActor d hK a hi).ker =
    (localMap d).ker.comap (inclusion hK) := by
  ext k
  change conjugateActorEquiv a.val _ = 1 ↔ localMap d (inclusion hK k) = 1
  rw [(conjugateActorEquiv a.val).map_eq_one_iff]
  exact Subtype.ext_iff

theorem restrictedActor_ker_eq_twoCore
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    (restrictedActor d hK a hi).ker = pCore 2 K := by
  have hk : IsPGroup 2 (restrictedActor d hK a hi).ker := by
    rw [restrictedActor_ker]
    exact (SourceStar.local_kernel_two d e).comap_of_injective (inclusion hK)
      (inclusion_injective hK)
  have hh := (restrictedActor d hK a hi).comap_pCore_of_ker_isPGroup
    (restrictedActor_surjective d hK a hi) hk
  rwa [FivePair.alternating_five_twoCore, MonoidHom.comap_bot] at hh

/-- The intrinsic K/O₂(K) marking agrees with the restricted actor on each representative. -/
noncomputable def quotientEquiv
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (restrictedActor_ker_eq_twoCore d hK a hi e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (restrictedActor d hK a hi)
      (restrictedActor_surjective d hK a hi))

theorem quotientEquiv_mk
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) (k : K) :
    quotientEquiv d hK a hi e (QuotientGroup.mk' (pCore 2 K) k) =
      restrictedActor d hK a hi k := rfl

/-- The given V coordinates restricted to the actual conjugate five-letter subgroup. -/
noncomputable def moduleEquiv : D.V ≃* Multiplicative (core (Fin 5)) :=
  d.coordinate.trans (conjugateModuleEquiv a.val).toAddEquiv.toMultiplicative

theorem moduleEquiv_equivariant
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) (k : K) (v : D.V) :
    (moduleEquiv d a (D.V.normalizerMonoidHom
      ⟨k.val,d.normalizes_V (mem_sup_left (hK k.property))⟩ v)).toAdd =
      alternatingCoreRepresentation (Fin 5)
        (quotientEquiv d hK a hi e (QuotientGroup.mk' (pCore 2 K) k))
        (moduleEquiv d a v).toAdd := by
  rw [quotientEquiv_mk]
  change conjugateModuleEquiv a.val (d.coordinate (D.V.normalizerMonoidHom _ v)).toAdd = _
  exact (congrArg (conjugateModuleEquiv a.val)
    (d.conjugation (inclusion hK k) v)).trans
      (conjugateModuleEquiv_equivariant a.val
        ⟨localMap d (inclusion hK k),image_mem d hK a hi k⟩ (d.coordinate v).toAdd)

/-- The original nonabelian-closure branch has the actual restricted natural
four-dimensional A₅ module on its selected pair K=L⁻. -/
theorem exists_original_five_module (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L), g.val ∉ D.Gz ∧
      ∃ hK : NormalBranch.K D g.val ≤ D.L,
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      ∃ hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom,
      ∀ (k : NormalBranch.K D g.val) (v : D.V),
        (moduleEquiv d a (D.V.normalizerMonoidHom
          ⟨k.val,d.normalizes_V (mem_sup_left (hK k.property))⟩ v)).toAdd =
          alternatingCoreRepresentation (Fin 5)
            (quotientEquiv d hK a hi e (QuotientGroup.mk' (pCore 2 _) k))
            (moduleEquiv d a v).toAdd := by
  obtain ⟨a,g,hg,_,hK,hL,_,hp,hr,hi⟩ :=
    SourcePairResidual.exists_pair_with_local_residual d h e hseed hn hU
  exact ⟨a,g,hg,hK,hL,hp,hr,hi,moduleEquiv_equivariant d hK a hi e⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveModule
