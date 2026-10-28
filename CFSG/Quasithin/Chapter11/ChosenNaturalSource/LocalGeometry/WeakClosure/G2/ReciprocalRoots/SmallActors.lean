module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Source

/-!
# Recognizing the reciprocal G₂ actor as a long-root subgroup

An elementary subgroup of the full original automizer with fixed codimension
at most 2n is inner: the existing involution bound excludes field operators.
On the natural quotient a short-root involution has codimension 3n. A long
root has codimension 2n, so its fixed space is already the fixed space of the
entire actor. The pointwise-fixer theorem puts that actor inside the same
actual field root. This works in every positive field degree on the model;
the original source application retains the nonbinary hypothesis.

The final theorem constructs the original ambient actor homomorphism, its
literal centralizer kernel and its action on the full chosen module. Transfer
uses it on C_V(D) acting on Vᵍ. Source: Aschbacher--Smith B.4.6(4,7) and
11.2.2(5), printed pp.88,768. The source assembly remains with
qt-d-1222-natural-weak-closure-source. No central splitting is used.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Finite F]

theorem small_model_actor_root {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0 < n)
    (B : Subgroup (Model F)) [IsElementaryAbelian 2 B]
    (hsmall : fixedCodim (NaturalOffenders.binaryNatural (F:=F)) B ≤ 2*n) :
    ∃ u : Model F, B ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom := by
  rcases B.bot_or_exists_ne_one with hbot | ⟨b,hb,hne⟩
  · exact ⟨1,hbot ▸ bot_le⟩
  have hmono := fixedCodim_mono (NaturalOffenders.binaryNatural (F:=F)) (zpowers_le.mpr hb)
  rcases EvenInvolutionGeometry.involution_isRoot
    (elemPow_eq_one_of_isElementaryAbelian b hb) hne with
    ⟨u,r,hr,he⟩ | ⟨u,r,hr,he⟩
  · have hlong : fixedCodim (NaturalOffenders.binaryNatural (F:=F)) (zpowers b) = 2*n := by
      rw [NaturalOffenders.natural_fixedCodim_eq]
      exact NaturalOffenders.fixedCodim_longRoot hc ⟨r,hr,u,he⟩
    have hle := ChapterE.fixedSpace_antitone
      (NaturalOffenders.binaryNatural (F:=F)) (zpowers_le.mpr hb)
    have hf := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F:=F)) B
    have hfb := fixedCodim_add_finrank (NaturalOffenders.binaryNatural (F:=F)) (zpowers b)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    refine ⟨u,?_⟩
    rw [←NaturalLongRootFixer.subspaceKernel_fixedSpace_longRoot u r hr,←he,←heq]
    intro x hx
    exact ⟨mem_top _,fun v hv => hv ⟨x,hx⟩⟩
  · have hshort : fixedCodim (NaturalOffenders.binaryNatural (F:=F)) (zpowers b) = 3*n := by
      rw [he,NaturalOffenders.natural_fixedCodim_eq]
      change fixedCodim (NaturalOffenders.binaryAction (F:=F))
        (zpowers ((MulAut.conj u).toMonoidHom (rootC r))) = _
      rw [←MonoidHom.map_zpowers,fixedCodim_map_conj]
      exact NaturalOffenders.fixedCodim_rootC hc r hr
    omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
open Parameters.FullAutomizer

include m in
theorem small_original_actor_inner (B : Subgroup (Automizer V)) [IsElementaryAbelian 2 B]
    (hsmall : letI := D.elementary
      fixedCodim (automizerRepresentation V) B ≤ 2*S.field.degree) :
    B ≤ inducedAutomizer V L := by
  let := D.elementary
  intro b hb
  by_cases h1 : b = 1
  · rw [h1]
    exact one_mem _
  · exact Parameters.MinimalFixed.g2_small_involution_inner D S m b
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) h1)
      ((fixedCodim_mono (automizerRepresentation V) (zpowers_le.mpr hb)).trans hsmall)

theorem small_original_actor_root (B : Subgroup (Automizer V)) [IsElementaryAbelian 2 B]
    (hsmall : letI := D.elementary
      fixedCodim (automizerRepresentation V) B ≤ 2*S.field.degree) :
    ∃ (hinner : B ≤ inducedAutomizer V L) (u : Model S.field.Carrier),
      ((layerEquiv D S (Coordinates.g2 m)).toMonoidHom.comp (inclusion hinner)).range ≤
        LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom := by
  let := D.elementary
  let c := Coordinates.g2 m
  have hinner := small_original_actor_inner D S m B hsmall
  let j : B →* Model S.field.Carrier := (layerEquiv D S c).toMonoidHom.comp (inclusion hinner)
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let E : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective
      (({toFun := id,map_zero' := rfl,map_add' := fun _ _ => rfl} :
        c.Space →+ Natural.Space S.field.Carrier).toZModLinearMap 2) Function.bijective_id
  let q := E.toLinearMap.comp (projectionLinear D S c)
  have hq : Function.Surjective q := E.surjective.comp (projectionLinear_surjective D S c)
  have heq (b : B) (v : Additive V) :
      q (automizerRepresentation V b v) = NaturalOffenders.binaryNatural (j b) (q v) := by
    have hh := congrArg E (he b v)
    change E (projectionLinear D S c (automizerRepresentation V b v)) =
      E (ρ b (projectionLinear D S c v)) at hh
    have hs := hres (inclusion hinner b) (projectionLinear D S c v)
    change ρ b (projectionLinear D S c v) = c.modelAction (j b) (projectionLinear D S c v) at hs
    exact hh.trans (congrArg E hs)
  have hcost := fixedCodim_le_of_equivariant_surjection
    ((automizerRepresentation V).comp B.subtype)
    ((NaturalOffenders.binaryNatural (F:=S.field.Carrier)).comp j) q hq heq ⊤
  have hbound : fixedCodim (NaturalOffenders.binaryNatural (F:=S.field.Carrier)) j.range ≤
      2*S.field.degree := by
    unfold fixedCodim at hcost
    rw [fixedSpace_comp_map,fixedSpace_comp_map,←MonoidHom.range_eq_map,
      ←MonoidHom.range_eq_map,range_subtype] at hcost
    exact hcost.trans hsmall
  obtain ⟨u,hu⟩ := small_model_actor_root S.field.card_eq (by have := S.nonbinary; omega)
    j.range hbound
  exact ⟨hinner,u,hu⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots


namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

theorem small_ambient_actor_root (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hBN : B ≤ normalizer (V : Set G))
    (hsmall : subgroupCorank V (V ⊓ centralizer (B : Set G)) ≤ 2*S.field.degree) :
    ∃ (b : B →* Model S.field.Carrier) (u : Model S.field.Carrier),
      (∀ (x : B) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (b x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      b.ker = (centralizer (V : Set G)).subgroupOf B ∧
      b.range ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom := by
  let := D.elementary
  let := inducedAutomizer_elementary V B hBN
  have hcod : fixedCodim (automizerRepresentation V) (inducedAutomizer V B) ≤
      2*S.field.degree := by
    rw [fixedCodim_inducedAutomizer V B hBN]
    exact hsmall
  obtain ⟨hinner,u,hu⟩ := small_original_actor_root D S m (inducedAutomizer V B) hcod
  refine ⟨RootPullback.innerActor D S m hBN hinner,u,
    RootPullback.innerActor_action D S m hBN hinner,
    RootPullback.innerActor_ker D S m hBN hinner,?_⟩
  rw [ActorRecognition.innerActor_range D S m hBN hinner]
  exact hu
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
