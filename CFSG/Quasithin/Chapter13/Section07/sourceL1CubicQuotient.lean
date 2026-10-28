module
public import CFSG.Quasithin.Chapter13.Section07.localCubicMarking
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.fourLetter

/-!
# Literal quotient maps for the original cubic comparison

The actual original S₃ pair and the L₁ conjugate both map onto their literal
cubic quotients. Their kernels are the restrictions of the original LT
2-core, preserving the source subgroup and quotient maps exactly.
-/


@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction ChapterF.Section09.Setup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_local_residual_surjection
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    ∃f:F.L₁→*alternatingGroup (Fin 4),Function.Surjective f ∧ f.ker=Q.subgroupOf F.L₁ := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X:=L⊔(T:Subgroup G)
  let J:=F.L₁
  let R:=(J.subgroupOf X).map (permutation d)
  have hJX:J≤X:=((map_subtype_le _).trans inf_le_left).trans le_sup_left
  let k:J→*Equiv.Perm (Fin 6):=(permutation d).comp (inclusion hJX)
  have hr:k.range=R:=by rw [MonoidHom.range_comp,inclusion_range]
  obtain ⟨l,hl⟩:=source_local_residual_even_marking d h hU hV
  let e:R≃*alternatingGroup (Fin 4):=
    (((MulAut.conj (permutation d (inclusion le_sup_left l))).subgroupMap R).trans
      (MulEquiv.subgroupCongr hl)).trans fourLetterEquiv
  let j:k.range≃*alternatingGroup (Fin 4):=(MulEquiv.subgroupCongr hr).trans e
  let f:J→*alternatingGroup (Fin 4):=j.toMonoidHom.comp k.rangeRestrict
  refine ⟨f,j.surjective.comp k.rangeRestrict_surjective,?_⟩
  have hk:f.ker=k.ker:=(MonoidHom.ker_comp_of_injective k.rangeRestrict
    j.toMonoidHom j.injective).trans (MonoidHom.ker_rangeRestrict k)
  rw [hk]
  ext x
  constructor
  · intro hx
    have hx':inclusion hJX x∈(permutation d).ker:=hx
    rw [nonabelian_permutation_kernel d h hU hV] at hx'
    exact mem_map_of_mem X.subtype hx'
  · intro hx
    obtain ⟨y,hy,he⟩:=hx
    have he':y=inclusion hJX x:=Subtype.ext he
    have hx':inclusion hJX x∈pCore 2 X:=he' ▸ hy
    rw [←nonabelian_permutation_kernel d h hU hV] at hx'
    exact hx'

theorem conjugate_local_residual_surjection
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) (l:L) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let J:=conjugate F.L₁ (l:G)
    ∃f:J→*alternatingGroup (Fin 4),Function.Surjective f ∧ f.ker=Q.subgroupOf J := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X:=L⊔(T:Subgroup G)
  let Q:=X.pCoreIn 2
  let J:=conjugate F.L₁ (l:G)
  obtain ⟨f,hf,hker⟩:=source_local_residual_surjection d h hU hV
  let e:F.L₁≃*J:=(MulAut.conj (l:G)⁻¹).subgroupMap F.L₁
  let j:J→*alternatingGroup (Fin 4):=f.comp e.symm.toMonoidHom
  refine ⟨j,hf.comp e.symm.surjective,?_⟩
  have hQX:X≤normalizer (Q:Set G):=X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  ext x
  change f (e.symm x)=1 ↔ (x:G)∈Q
  rw [←MonoidHom.mem_ker,hker]
  change (e.symm x:G)∈Q ↔ (x:G)∈Q
  have he:(e.symm x:G)=(l:G)*(x:G)*(l:G)⁻¹:=by
    have hh:=congrArg (fun z:J=>(z:G)) (e.apply_symm_apply x)
    change (l:G)⁻¹*(e.symm x:G)*((l:G)⁻¹)⁻¹=(x:G) at hh
    have hm:=congrArg (fun z:G=>(l:G)*z*(l:G)⁻¹) hh
    simpa [mul_assoc] using hm
  rw [he]
  exact (mem_normalizer_iff.mp (hQX (mem_sup_left l.property)) (x:G)).symm

theorem pair_symmetricThree_surjection
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let I:=Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    ∃f:I→*Equiv.Perm (Fin 3),Function.Surjective f ∧ f.ker=Q.subgroupOf I := by
  dsimp only
  let I:=Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  obtain ⟨hc,⟨e⟩⟩:=pair_twoCore_quotient d h hU hV g hout
  let f:I→*Equiv.Perm (Fin 3):=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  refine ⟨f,e.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  have hk:f.ker=pCore 2 I:=by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  rw [hk]
  apply map_injective I.subtype_injective
  change I.pCoreIn 2=(Q.subgroupOf I).map I.subtype
  rw [hc,subgroupOf_map_subtype,inf_comm]
end CFSG.Quasithin.Chapter13.Section07
