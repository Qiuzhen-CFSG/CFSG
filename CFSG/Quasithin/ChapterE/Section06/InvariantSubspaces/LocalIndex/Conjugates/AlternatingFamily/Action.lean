module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.ModelMarking
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.ThompsonImage

/-!
# Assembly of the genuine alternating-five coordinates

After choosing permutation labels for the Thompson image D = ⟨(01),(23)⟩,
the factorization S = UˣQ makes the Baumann image elementary abelian.
It contains D, so D's self-centralization forces equality. The full image
of H is S₅, and the Sylow image therefore contains the even exchange
(02)(13). Since the action kernel O₂(H) lies in R, this exchange lifts
through the alternating image of L to an element of R ∩ L.

The core embedding uses the actual U-action, via the odd-degree natural
module equivalence. No elementary-family conclusion, index-two assumption,
or SQTK hypothesis on the join is used. The calculation does not need
Φ(D) = 1; that extra contract hypothesis belongs to the family enumeration.

`actionInput_of_earlier_inputs` separates three earlier source inputs:
C_H(U) = O₂(H), the full natural-action model (including removal of C_U(L)),
and the actual Thompson-image calculation. `actionInput` discharges all three
using their proved constructions, completing the published coordinate contract.
These inputs are shared with the independent Baumann alpha calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.11 and
C.1.13(c), printed pp.124–125; C.5.4(3), p.155; C.5.6, pp.157–158;
and B.3.2(4), pp.83–84.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action
open Subgroup
open Baumann.AlternatingFive
universe u
variable {G : Type u} [Group G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

private theorem J_le_S : Stellmacher.elementaryAbelianMaxJ R ≤ S R := by
  refine le_inf (sSup_le fun _ hE => hE.1) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro w hw
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 j hj |>.symm

private theorem image_restrict (q : H →* Perm) (hRH : R ≤ H)
    {B : Subgroup G} (hBR : B ≤ R) :
    actionImage (q.comp (inclusion hRH)) B = (B.subgroupOf H).map q := by
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨inclusion hRH r, hr, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hBR hb⟩, hb, rfl⟩

private theorem quotient_eq_one_iff (m : NaturalActionModel H L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) (r : H) :
    m.quotient r = 1 ↔ (r : G) ∈ centralizer (U L : Set G) := by
  rw [← MonoidHom.mem_ker, m.kernel]
  constructor
  · intro hr
    have he : (r : G) ∈ pCoreIn 2 H := mem_map_of_mem H.subtype hr
    rw [← hc] at he
    exact he.2
  · intro hr
    have he : (r : G) ∈ pCoreIn 2 H := hc ▸ ⟨r.property, hr⟩
    obtain ⟨s, hs, he⟩ := he
    exact (show s = r from Subtype.ext he) ▸ hs

variable [Finite G]

/-- Assemble all coordinate fields from the genuine H-action and a marked
Thompson image. The conjugate-module factorization forces the Baumann image
to be elementary abelian; self-centralization of D makes that image exactly D.
The Sylow exchange lifts into R ∩ L because the kernel lies in R. -/
theorem coordinates_of_marked (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    {x : G} (hp : Factorization R L x) (m : NaturalActionModel H L)
    (hJ : ((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient =
      ChapterB.Offenders.D 5) : Nonempty (ActionCoordinates R L) := by
  have hRH : R ≤ H := h.join_eq ▸ le_sup_right
  have hSR : S R ≤ R := inf_le_left
  have hQR : Q R L ≤ R := (hb.core_eq ▸ inf_le_left).trans hSR
  have hVR : (U L).map (MulAut.conj x).toMonoidHom ≤ R :=
    (le_sup_left.trans hp.span.ge).trans hSR
  let σ : R →* Perm := m.quotient.comp (inclusion hRH)
  have hker (r : R) : σ r = 1 ↔ (r : G) ∈ centralizer (U L : Set G) :=
    quotient_eq_one_iff m hc (inclusion hRH r)
  have hQ : actionImage σ (Q R L) = ⊥ := by
    rw [actionImage, Subgroup.map_eq_bot_iff]
    intro q hq
    exact (hker q).mpr (hb.core_eq ▸ hq).2
  have hspan : actionImage σ (S R) = actionImage σ ((U L).map (MulAut.conj x).toMonoidHom) := by
    rw [hp.span, actionImage_sup σ hVR hQR, hQ, sup_bot_eq]
  have hD : ChapterB.Offenders.D 5 ≤ actionImage σ (S R) := by
    rw [← hJ, ← image_restrict m.quotient hRH (J_le_S.trans hSR)]
    exact actionImage_mono σ J_le_S
  have hS : actionImage σ (S R) = ChapterB.Offenders.D 5 := by
    let : IsElementaryAbelian 2 (U L) := elementary_U h
    let : IsElementaryAbelian 2 ((U L).map (MulAut.conj x).toMonoidHom) :=
      IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 (((U L).map (MulAut.conj x).toMonoidHom).subgroupOf R) :=
      IsElementaryAbelian.subgroupOf hVR
    let : IsElementaryAbelian 2 (actionImage σ ((U L).map (MulAut.conj x).toMonoidHom)) :=
      IsElementaryAbelian.map σ
    have habel : IsMulCommutative (actionImage σ (S R)) := by rw [hspan]; infer_instance
    let := habel
    exact le_antisymm
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        ((centralizer_le hD).trans centralizer_D_le)) hD
  have hsurj : Function.Surjective m.quotient :=
    quotient_surjective_of_image m _ (by
      rw [hJ]
      exact ChapterB.Offenders.IsConjugateTo.refl _)
  obtain ⟨P, hP⟩ := h.sylow
  have hRP : R.subgroupOf H = (P : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH]
    exact hP.symm
  let T := P.mapSurjective hsurj
  have hT : (R.subgroupOf H).map m.quotient = (T : Subgroup Perm) := by
    rw [hRP, Sylow.coe_mapSurjective]
  have hDT : ChapterB.Offenders.D 5 ≤ T := by
    rw [← hT, ← hJ]
    exact map_mono (comap_mono (J_le_S.trans hSR))
  have heT : exchange ∈ (T : Subgroup Perm) := exchange_mem_sylow T hDT
  rw [← hT] at heT
  obtain ⟨r, hr, her⟩ := heT
  have heA : exchange ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  rw [← m.block_image] at heA
  obtain ⟨l, hl, hel⟩ := heA
  have hrl : r * l⁻¹ ∈ pCore 2 H := by
    rw [← m.kernel]
    change m.quotient (r * l⁻¹) = 1
    simp [her, hel]
  have hrlR : r * l⁻¹ ∈ R.subgroupOf H := by
    rw [hRP]
    exact pCore_isPGroup.le_sylow_of_normal P hrl
  have hlR : l ∈ R.subgroupOf H := by
    have he := (R.subgroupOf H).mul_mem ((R.subgroupOf H).inv_mem hrlR) hr
    simpa using he
  refine ⟨{
    action := σ
    moduleMap := coreMap m
    moduleMap_injective := coreMap_injective m
    moduleMap_range := coreMap_range m
    equivariant := fun r v => coreMap_equivariant m (inclusion hRH r) v
    kernel := hker
    baumann_image := hS
    inner_exchange := ?_ }⟩
  exact ⟨⟨l, hlR⟩, ⟨hlR, hl⟩, hel⟩

/-- The complete coordinate contract follows from the three earlier source
inputs, instantiated by `actionInput` below. -/
theorem actionInput_of_earlier_inputs (K : GroupClass.{u})
    (hc : Baumann.SingleBlockCentralizerInput (G := G))
    (ha : NaturalActionInput (G := G) K)
    (hj : ThompsonImageInput (G := G) K) : ActionInput (G := G) K := by
  intro A H R L h hb hL x _hx _hne hp _hF
  have hc' := hc H R L h.characteristicTwo h.sylow h.normalizes_L h.join_eq h.block
  obtain ⟨m⟩ := ha A H R L h hc' hL
  obtain ⟨m', hm'⟩ := exists_marked m _ (hj A H R L h hc' hL m)
  exact coordinates_of_marked h hb hc' hp m' hm'

/-- The genuine alternating-five coordinates, including the centralizer kernel,
the marked Baumann image, and an exchange actor in `R ∩ L`, follow from the
published local hypotheses with no additional source inputs. -/
theorem actionInput (K : GroupClass.{u}) : ActionInput (G := G) K :=
  actionInput_of_earlier_inputs K Baumann.singleBlockCentralizerInput
    naturalActionInput thompsonImageInput

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action

end
