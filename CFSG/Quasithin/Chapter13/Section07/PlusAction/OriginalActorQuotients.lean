module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActorImages
public import Theory.GroupTheory.ReducedNormal.SimpleActorImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
/-!
# The original kernel actor and its SQTK cover

On a nonzero reduced elementary subgroup fully moved by a normal primitive
kernel actor, the faithful image is the actor's original simple quotient.
The selected cubic, A₅ and binary PSL₃ models therefore transport to exactly
the same image used by the B.5 consumer. The field marking in the binary PSL₃
case is preserved through entrywise field transport and the canonical SL₃
projection.

The image of the kernel actor together with the point-parabolic radical
also has an actual finite SQTK cover: the source group K(L₁T) lies in the
two-local normalizer of V₁. Pulling back its conjugation quotient along the
literal image subgroup supplies the cover required by B.5.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
theorem source_primitive_reduced_actor_equiv
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (U : Subgroup ↥(J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hU : IsPReduced 2 U) (hne : U≠⊥)
    (hm : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆=U)
    (hs : IsSimpleGroup (J ⧸ pCore 2 J)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    letI := hU.normal
    Nonempty ((J ⧸ pCore 2 J) ≃* (K.subgroupOf X).map
      (QuotientGroup.mk' (centralizer (U : Set X)))) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
  let KX := K.subgroupOf X
  let := hU.normal
  have hKH : K≤H := hJC.trans (kernel_le_H (D:=F))
  have hXH : X≤H := sup_le hKH h.local_le
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let eK : KX ≃* K := subgroupOfEquivOfLe le_sup_left
  let eJ : J ≃* K := J.equivMapOfInjective H.subtype H.subtype_injective
  let e : KX ≃* J := eK.trans eJ.symm
  let eQ : (KX ⧸ pCore 2 KX) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hs
  have hsX : IsSimpleGroup (KX ⧸ pCore 2 KX) := eQ.isSimpleGroup
  obtain ⟨eA⟩ := reduced_simple_actor_image U KX hU hsX hne hm
  exact ⟨eQ.symm.trans eA⟩
theorem source_primitive_reduced_actor_models
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (U : Subgroup ↥(J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hU : IsPReduced 2 U) (hne : U≠⊥)
    (hm : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆=U)
    (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hmodels : Nat.card (J ⧸ pCore 2 J) = 3 ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    letI := hU.normal
    let C := (K.subgroupOf X).map (QuotientGroup.mk' (centralizer (U : Set X)))
    Nat.card C = 3 ∨ Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let := hU.normal
  obtain ⟨e⟩ := source_primitive_reduced_actor_equiv h J hJC hJn U hU hne hm hs
  rcases hmodels with hc | ha | hl
  · exact Or.inl ((Nat.card_congr e.toEquiv).symm.trans hc)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨e.symm.trans a⟩)
  · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hl
    let := hF
    let := hfin
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
    exact Or.inr (Or.inr ⟨(e.symm.trans a).trans
      ((Atlas.fieldEquivPSL 3 f).trans Matrix.PSL3Two.equiv.symm)⟩)

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open ChapterB.SourceInduction Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_kernel_reduced_actor_cover
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K : Subgroup G} (hKH : K ≤ H)
    (U : Subgroup ↥(K ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    letI := hred.normal
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let E := (K.subgroupOf X).map q ⊔ ((P.pCoreIn 2).subgroupOf X).map q
    Nonempty (SQTKQuotient KnownSimple.IsKnownSimple E) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let := hred.normal
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let E := (K.subgroupOf X).map q ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hn : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he,card_bot] at hc
    contradiction
  have hloc : IsTwoLocal (normalizer (V₁ : Set G)) := ⟨V₁,hn,hp,rfl⟩
  have hXN : X ≤ normalizer (V₁ : Set G) :=
    (sup_le hKH h.local_le).trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXN)).mp
      ((d.counterexample.qtke.twoLocal_sqtk hloc).subgroup
        (X.subgroupOf (normalizer (V₁ : Set G))))
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (X ⧸ centralizer (U : Set X)) :=
    { Cover := X
      kernel := centralizer (U : Set X)
      sqtk := hX
      equiv := MulEquiv.refl _ }
  exact ⟨cover.subgroup E⟩
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
