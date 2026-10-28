module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalFFRows
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActorQuotients
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOffenderMovement
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalConclusion

/-!
# Excluding the original cubic plus-kernel actor

The source minimal reduced tilde-one subgroup is moved by both the kernel
actor and the point residual. Its exact centralizer quotient has an actor
of order three, an actual SQTK cover, and the offender containment supplied
by B.2.10. The commuting fixed-free cubic image therefore invokes the
three-row B.5 conclusion, whose doubled natural action identifies this same
actor with SL₃(2). Their orders contradict one another.

The final source application constructs the minimal subgroup and removes
the odd-chief alternative from the original nonfaithful kernel selection.
The genuine earlier Baumann normalizer bound remains explicit; neither an
A₅ module marking nor a component catalogue is used in this branch.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938, using B.2.10
and B.5.6.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_reduced_cubic_false
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (U : Subgroup ↥(J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U) (hne : U ≠ ⊥)
    (hUK : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hUL : ⁅U,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)))⁆ = U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G))))
    (hUR : U ≤ (⁅commutatorPreimage
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.pCoreIn 2)
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).V₁,J.map H.subtype⁆).subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)))) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hcomm : ⁅K,F.L₁⁆ ≤ K.pCoreIn 2 :=
    source_primitive_cubic_centralized h J hJn hcard
  have hs : IsSimpleGroup (J ⧸ pCore 2 J) := isSimpleGroup_of_prime_card hcard
  obtain ⟨ec⟩ := source_primitive_reduced_actor_equiv h J hJC hJn U hred hne hUK hs
  have hC3 : Nat.card C = 3 := (Nat.card_congr ec.toEquiv).symm.trans hcard
  let eK := J.equivMapOfInjective H.subtype H.subtype_injective
  have hK3 : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).toEquiv]
    exact hcard
  obtain ⟨hn,hff⟩ := source_reduced_odd_doubleThree d h eL hJC hJn hp hcomm U
    hred hne hUK hUL hUR
  let := hn
  obtain ⟨cover⟩ := source_kernel_reduced_actor_cover d h
    (hJC.trans (kernel_le_H (D := F))) U hred
  have hCN := source_cubic_kernel_le_restricted_offender h hJC hJn hcomm hout hB
    hK3 U hred hU0 hne hUK
  have hA5 : Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
        (C.subgroupOf E).subtype) (alternatingNatural 5)) := by
    intro h60
    have hf : (3 : ℕ) = 60 := hC3.symm.trans h60
    norm_num at hf
  obtain ⟨a⟩ := hff cover hCN (Or.inl hC3) hA5
  have hc := Nat.card_congr a.groupEquiv.toEquiv
  change Nat.card C = Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) at hc
  rw [hC3,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear] at hc
  norm_num at hc

theorem source_primitive_cubic_false
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
  obtain ⟨U,hUD,hUU₂,hr,hne,hUK,hUL,_⟩ :=
    source_primitive_cubic_minimal_tilde_module d h1221 h hU eL hm J hJC hJn hp hout hcard
  have hcomm : ⁅K,F.L₁⁆ ≤ K.pCoreIn 2 := source_primitive_cubic_centralized h J hJn hcard
  have hU0 : U ≤ (fixedLayer F).subgroupOf X :=
    hUU₂.trans (comap_mono (source_kernel_mixed_geometry d h hJC hJn hp hcomm).2.2.1)
  have hDR := (source_kernel_tilde_geometry d h hJC hJn hp hcomm).2.2.2.2.2.2.1
  exact source_reduced_cubic_false d h eL J hJC hJn hp hout hcard hB U hr hne hUK hUL
    hU0 (hUD.trans (subgroupOf_mono X hDR))

/-- On the original nonfaithful plus-kernel branch the odd-chief case is
excluded, leaving an actual primitive C-component. -/
theorem source_ordinary_kernel_component_branch
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hk : kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) ≠ H.pCoreIn 2)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    ∃ J : Subgroup H, let K := J.map H.subtype
      K ≤ kernel F ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (fixedLayer F : Set G) = K.pCoreIn 2 ∧
      J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J) := by
  obtain ⟨J,hJC,hp,hJne,hnot,hcent,hcases⟩ :=
    source_ordinary_kernel_cubic_branch d h1221 h hU eL hne hV hk hB
  rcases hcases with hcomponent | ⟨hJn,hout,_,_,hcard,_⟩
  · exact ⟨J,hJC,hp,hJne,hnot,hcent,hcomponent⟩
  · exact (source_primitive_cubic_false d h1221 h hU eL hm J hJC hJn hp hout hcard hB).elim

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
