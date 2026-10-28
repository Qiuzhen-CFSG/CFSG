module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActors
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The literal radical join on a reduced source module

The normal kernel actor together with the two-core of L₁T gives a normal
subgroup of K(L₁T), with a two-group quotient by the kernel actor. Surjective
images preserve this structure. For the faithful conjugation action on an
actual reduced elementary module, its normal image has trivial two-core.

Source: Aschbacher--Smith 13.7.4(1), printed p.937, the group E=C R₁⁺.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G D : Type*} [Group G] [Finite G] [Group D]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

theorem source_kernel_radical_join_image
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (f : ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))) →* D)
    (hf : Function.Surjective f) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let R := P.pCoreIn 2
    let X := K ⊔ P
    let C := (K.subgroupOf X).map f
    let Rplus := (R.subgroupOf X).map f
    let E := C ⊔ Rplus
    E.Normal ∧ C.Normal ∧ IsPGroup 2 Rplus ∧
      ∃ hn : (C.subgroupOf E).Normal, letI := hn; IsPGroup 2 (E ⧸ C.subgroupOf E) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ P
  let C := (K.subgroupOf X).map f
  let Rplus := (R.subgroupOf X).map f
  let E := C ⊔ Rplus
  obtain ⟨hEX,hXn,hEn,_⟩ := source_kernel_radical_join_normal h hKH hKn
  have hXH : X ≤ H := sup_le hKH h.local_le
  let : (K.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hKn)
  let := hEn
  have hE : E = ((K ⊔ R).subgroupOf X).map f := by
    rw [subgroupOf_sup (show K ≤ X from le_sup_left)
      (show R ≤ X from (pCoreIn_le 2 P).trans le_sup_right),Subgroup.map_sup]
  have hEn' : E.Normal := hE ▸ (inferInstance : ((K ⊔ R).subgroupOf X).Normal).map f hf
  let := hEn'
  let : C.Normal := (inferInstance : (K.subgroupOf X).Normal).map f hf
  have hRp : IsPGroup 2 Rplus := (isPGroup_pCoreIn 2 P).comap_subtype.map f
  let : (C.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer le_normalizer_of_normal
  refine ⟨hEn',inferInstance,hRp,inferInstance,?_⟩
  have hgen : C.subgroupOf E ⊔ Rplus.subgroupOf E = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ E from le_sup_left) (show Rplus ≤ E from le_sup_right)]
    exact subgroupOf_self E
  exact isPGroup_quotient_of_sup_eq_top _ _ hRp.comap_subtype hgen

theorem source_kernel_radical_join_image_core
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (f : ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))) →* D)
    (hf : Function.Surjective f) (hcore : pCore 2 D = ⊥) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    let E := (K.subgroupOf X).map f ⊔ ((P.pCoreIn 2).subgroupOf X).map f
    pCore 2 E = ⊥ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let E := (K.subgroupOf X).map f ⊔ ((P.pCoreIn 2).subgroupOf X).map f
  have hEn := (source_kernel_radical_join_image h hKH hKn f hf).1
  let := hEn
  have hn : ((pCore 2 E).map E.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore 2 E).map E.subtype ≤ pCore 2 D :=
    le_sSup ⟨hn,pCore_isPGroup.map E.subtype⟩
  apply (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).mp
  exact le_bot_iff.mp (hcore ▸ hl)

theorem source_kernel_reduced_actor_image
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : Theory.GroupTheory.IsPReduced 2 U) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    letI := hred.normal
    letI := hred.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let C := (K.subgroupOf X).map q
    let Rplus := ((P.pCoreIn 2).subgroupOf X).map q
    let E := C ⊔ Rplus
    let ρ := Representation.NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    E.Normal ∧ C.Normal ∧ IsPGroup 2 Rplus ∧ pCore 2 E = ⊥ ∧
      Function.Injective ρ ∧
      ∃ hn : (C.subgroupOf E).Normal, letI := hn; IsPGroup 2 (E ⧸ C.subgroupOf E) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  obtain ⟨hEn,hCn,hR,hquot⟩ := source_kernel_radical_join_image h hKH hKn q
    (QuotientGroup.mk'_surjective _)
  exact ⟨hEn,hCn,hR,
    source_kernel_radical_join_image_core h hKH hKn q
      (QuotientGroup.mk'_surjective _) hred.quotient_pCore_eq_bot,
    Representation.NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _),hquot⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
