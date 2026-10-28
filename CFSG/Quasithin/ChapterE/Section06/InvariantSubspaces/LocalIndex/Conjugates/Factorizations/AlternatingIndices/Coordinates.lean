module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.Inputs
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.ModelMarking
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices.Geometry

/-!
# Permutation coordinates before the conjugate-block factorization

The fixed subspace C_U(J(R)) is elementary abelian and centralizes J(R), hence
lies in its omega-center. Baum(R) therefore fixes this plane pointwise. In the
actual degree-five action its pointwise stabilizer is the pair-swap four-group;
since J(R) lies in Baum(R), both images equal that four-group. Sylow transport
then lifts the even pair exchange into R intersect L.

The full action model on U and the Thompson-image identification remain
explicit earlier inputs. No factorization, Frattini-zero or target index is
assumed. This strengthens the coordinate construction used by the later
maximum-elementary-family calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155, and C.5.6, printed p.157; B.2.3 and B.3.2(4), pp.75,83–84.
-/

public section


open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices
open Baumann.AlternatingFive AlternatingFamily AlternatingFamily.Action
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

private theorem coreMap_fixed_iff (m : NaturalActionModel H L)
    {B : Subgroup G} (hB : B ≤ H) (v : Multiplicative Vector) :
    coreMap m v ∈ centralizer (B : Set G) ↔
      v.toAdd ∈ fixedSpace (coreRepresentation (Fin 5)) ((B.subgroupOf H).map m.quotient) := by
  rw [mem_centralizer_iff, mem_fixedSpace_iff]
  constructor
  · intro hv p hp
    obtain ⟨r, hr, rfl⟩ := hp
    apply Multiplicative.ofAdd.injective
    apply coreMap_injective m
    rw [← coreMap_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (hv r.val hr)
  · intro hv b hb
    let r : H := ⟨b, hB hb⟩
    have he := congrArg (fun z : Vector => coreMap m (Multiplicative.ofAdd z))
      (hv (m.quotient r) (mem_map_of_mem m.quotient hb))
    rw [← coreMap_equivariant] at he
    exact mul_inv_eq_iff_eq_mul.mp he

variable [Finite G]

/-- The Baumann image is D because it fixes the plane centralized by J(R).
This uses the Baumann definition, without a conjugate-module factorization. -/
theorem baumann_image_of_marked (h : Configuration K A H R L)
    (m : NaturalActionModel H L)
    (hJ : ((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient =
      ChapterB.Offenders.D 5) :
    ((S R).subgroupOf H).map m.quotient = ChapterB.Offenders.D 5 := by
  have hJR : Stellmacher.elementaryAbelianMaxJ R ≤ R := J_le_S.trans inf_le_left
  have hRH : R ≤ H := h.join_eq ▸ le_sup_right
  let V := U L ⊓ centralizer (Stellmacher.elementaryAbelianMaxJ R : Set G)
  have hVR : V ≤ R := inf_le_left.trans (Baumann.module_le_R h)
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (show V ≤ U L from inf_le_left)
  have hVa : V ≤ ChapterB.thompsonAlpha R :=
    Stellmacher.elementary_centralizer_maxJ_le_omegaCenter R V hVR inf_le_right
  apply le_antisymm
  · rintro p ⟨s, hs, rfl⟩
    apply fixed_plane_stabilizer
    intro v hv
    have hvc : coreMap m (Multiplicative.ofAdd v) ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [← coreMap_range m]
        exact ⟨_, rfl⟩
      · apply (coreMap_fixed_iff m (hJR.trans hRH) _).mpr
        rwa [hJ]
    have hcomm := mem_centralizer_iff.mp
      (show (s : G) ∈ centralizer (ChapterB.thompsonAlpha R : Set G) from hs.2)
      _ (hVa hvc)
    apply Multiplicative.ofAdd.injective
    apply coreMap_injective m
    exact (coreMap_equivariant m s (Multiplicative.ofAdd v)).symm.trans
      (mul_inv_eq_iff_eq_mul.mpr hcomm.symm)
  · rw [← hJ]
    exact map_mono (comap_mono J_le_S)

/-- Genuine coordinates before factorization or Frattini reduction. -/
theorem coordinates_of_marked (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (m : NaturalActionModel H L)
    (hJ : ((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient =
      ChapterB.Offenders.D 5) : Nonempty (ActionCoordinates R L) := by
  have hRH : R ≤ H := h.join_eq ▸ le_sup_right
  have hSR : S R ≤ R := inf_le_left
  let σ : R →* Perm := m.quotient.comp (inclusion hRH)
  have hker (r : R) : σ r = 1 ↔ (r : G) ∈ centralizer (U L : Set G) :=
    quotient_eq_one_iff m hc (inclusion hRH r)
  have hS : actionImage σ (S R) = ChapterB.Offenders.D 5 := by
    rw [image_restrict m.quotient hRH hSR]
    exact baumann_image_of_marked h m hJ
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

/-- The action and Thompson inputs supply coordinates without factorization. -/
theorem coordinates_of_inputs (ha : NaturalActionInput (G := G) K)
    (hj : ThompsonImageInput (G := G) K) (h : Configuration K A H R L)
    (hL : ChapterC.IsAlternatingBlock L 5) : Nonempty (ActionCoordinates R L) := by
  have hc := Baumann.singleBlockCentralizerInput H R L h.characteristicTwo
    h.sylow h.normalizes_L h.join_eq h.block
  obtain ⟨m⟩ := ha A H R L h hc hL
  obtain ⟨m', hm'⟩ := exists_marked m _ (hj A H R L h hc hL m)
  exact coordinates_of_marked h hc m' hm'

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices

end
