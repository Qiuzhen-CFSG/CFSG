module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelAction
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.SL2NaturalOffenders.AutomorphismRank

/-!
# Rank bounds and Sylow offenders in the original natural action

Transport the literal automizer representation through the natural marking.
The scalar-centralizer rank bound applies to every elementary image, and
B.4.2(1) makes each offender a Sylow subgroup of the image of L. Surjective
Sylow lifting then gives a Sylow subgroup of the original L with that action.

Source: Aschbacher--Smith, 6.1.10--11, printed p.670, and B.4.2(1), p.86.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
variable {G : Type*} [Group G] [Finite G] {L B : Subgroup G} [IsElementaryAbelian 2 B]

omit [Finite G] [IsElementaryAbelian 2 B] in
theorem induced_map_layerAction (hLB : L ≤ normalizer (B : Set G)) (X : Subgroup L) :
    ChapterE.inducedAutomizer B (X.map L.subtype) =
      (X.map (layerAction hLB)).map (ChapterE.inducedAutomizer B L).subtype := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨l,hl,hlb⟩ := hb
    have hh : b = ⟨l,hLB l.property⟩ := Subtype.ext hlb.symm
    subst b
    exact ⟨layerAction hLB l, ⟨l,hl,rfl⟩, layerAction_coe hLB l⟩
  · rintro ⟨_,⟨l,hl,rfl⟩,rfl⟩
    exact ⟨⟨l,hLB l.property⟩, ⟨l,hl,rfl⟩,(layerAction_coe hLB l).symm⟩

theorem elementaryActionRankBound {n : ℕ} (hn : 2 ≤ n)
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G)) :
    ElementaryActionRankBound B n := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j,E,hE⟩ := marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := induced_normal hNL
  let τ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hτ : Function.Injective τ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, τ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  have hr := Representation.SL2NaturalOffenders.faithful_extension_rank_le C j τ hτ hnat hn hF
  intro A hA hAN
  let := hA
  have he := ChapterE.inducedAutomizer_elementary B A hAN
  have hc := (primeRank_le_iff_elementary_card_le (ChapterE.Automizer B)).mp hr _ he
  rw [←ChapterE.rank_inducedAutomizer B A hAN]
  exact (Nat.log_mono_right (b := 2) hc).trans_eq (Nat.log_pow (by decide : 1 < 2) n)

theorem offender_lifts_sylow {n : ℕ} (hn : 2 ≤ n)
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    {A : Subgroup G}
    (hA : IsOffender (ChapterE.automizerRepresentation B) (ChapterE.inducedAutomizer B A)) :
    ∃ P : Sylow 2 L, ChapterE.inducedAutomizer B A =
      ChapterE.inducedAutomizer B ((P : Subgroup L).map L.subtype) := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j,E,hE⟩ := marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := induced_normal hNL
  let τ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hτ : Function.Injective τ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, τ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  have hAτ : IsOffender τ (ChapterE.inducedAutomizer B A) := by
    have hh := hA.map_equivariant (ChapterE.automizerRepresentation B) τ
      (MonoidHom.id _) Function.injective_id E (fun a v => by
        change E (ChapterE.automizerRepresentation B a v) =
          E (ChapterE.automizerRepresentation B a (E.symm (E v)))
        rw [E.symm_apply_apply])
    simpa only [map_id] using hh
  have hsize : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨P,hP⟩ := Representation.SL2NaturalOffenders.exists_sylow hsize C j τ hτ hnat hAτ
  have hm : IsConjugationModel L B (Representation.specialLinearNatural (k := F) 2) := ⟨e,f,hf⟩
  obtain ⟨Q,hQ⟩ := Sylow.mapSurjective_surjective (layerAction_surjective hm.normalizes) 2 P
  refine ⟨Q,?_⟩
  rw [induced_map_layerAction hm.normalizes]
  have hh := congrArg (fun S : Sylow 2 C => (S : Subgroup C)) hQ
  change (Q : Subgroup L).map (layerAction hm.normalizes) = (P : Subgroup C) at hh
  rw [hh]
  exact hP.symm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
