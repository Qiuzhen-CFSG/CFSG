module
public import Theory.Representation.BinaryAlternatingSixModels.CubicMovement
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.SectionModels

/-!
# The cubic contribution of the actual tensor quotient

A quotient carrying the published sixteen-dimensional tensor action has
cubic length six. Together with the natural V section and the parabolic
two-core quotient, the same actor has length at least eight on the common
local two-core. The coordinate maps retain their exact kernels and the
outer marking. No noncentral-factor count is an input.

Source: Aschbacher--Smith 13.8.6(4) and the nonabelian-span argument of
13.8.33, printed pp.948,967. The actual source application is
CaseOne.SteinbergObstruction. Construction of its remaining L-side maps
belongs to qt-d-138-a6-endgame-source.
-/

@[expose] public section
open Subgroup Representation.BinaryFixedPoints
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
variable {G : Type*} [Group G]

/-- A literal Steinberg quotient with the L-side marking of the common actor. -/
abbrev OppositeTensorSection (A E R : Subgroup G) (f : A →* cubicActor) :=
  letI := action (BinaryAlternatingSix.tensorAction.comp duadCubicActor.subtype)
  ConjugationSection (Y := Multiplicative BinaryAlternatingSix.TensorModule)
    A E R (cubicActorEquiv.toMonoidHom.comp f)

theorem opposite_tensor_section_length [Finite G]
    {A E R : Subgroup G} {f : A →* cubicActor}
    (t : OppositeTensorSection A E R f)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A E R = 6 := by
  let := action (BinaryAlternatingSix.tensorAction.comp duadCubicActor.subtype)
  have hc : Nat.card duadCubicActor = 3 :=
    (Nat.card_congr cubicActorEquiv.toEquiv).symm.trans cubicActor_card
  exact (t.length_eq hA hR (cubicActorEquiv.surjective.comp hf)).trans
    (BinaryAlternatingSix.CubicMovement.tensor_cubic_length duadCubicActor hc)

/-- The Steinberg quotient contributes six, and the actual natural V and
parabolic two-core quotient each contribute one. The same cubic actor is
used throughout; no chief count or abelianness of R is assumed. -/
theorem steinberg_filtration_lower_bound [Finite G]
    (A V E R Q P : Subgroup G) (f : A →* cubicActor)
    (hf : Function.Surjective f) (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (v : OppositeSection A ⊥ V f .natural)
    (t : OppositeTensorSection A E R f)
    (q : LocalCoreQuotient A Q P duadCubicActor
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 (cubicActorEquiv.toMonoidHom.comp f))
    (hVE : V ≤ E) (hRQ : R ≤ Q) :
    8 ≤ conjugationCubicLength A (P.pCoreIn 2) := by
  let := action (BinaryAlternatingSix.tensorAction.comp duadCubicActor.subtype)
  have hVR : V ≤ R := hVE.trans t.le
  have hR2 : IsPGroup 2 R := hQ.to_le hRQ
  have hv := opposite_section_length .natural v hA (hR2.to_le hVR) hf
  simp only [sectionCubicLength,conjugationCubicLength_bot,Nat.sub_zero] at hv
  have ht := opposite_tensor_section_length t hA hR2 hf
  have hmon := sectionCubicLength_mono A hVE (show R ≤ R from le_rfl)
  have hlower : 6 ≤ sectionCubicLength A V R := by
    exact ht ▸ hmon
  let core := q.coreSection hQ duadCubicActor_normalizes_parabolic_core
  have htop := duad_core_section_length core hA (isPGroup_pCoreIn 2 P) hf
  have hrq := conjugationCubicLength_mono A hRQ
  unfold sectionCubicLength at hlower htop
  omega
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
