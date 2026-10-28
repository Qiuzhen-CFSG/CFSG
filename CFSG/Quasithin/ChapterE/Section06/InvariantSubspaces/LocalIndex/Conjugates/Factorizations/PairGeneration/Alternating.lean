module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.LocalAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.ModelMarking
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.Transport

/-!
# Generation from the actual alternating-five action

The supplied span S = UˣQ makes the permutation image of S elementary.
After marking the Thompson image as the commuting-transposition four-group,
self-centralization forces the Baumann image to be that same four-group.
The checked even five-cycle construction supplies a second conjugate, and
its evenness lets us lift the conjugator into L.

Restricting the actual H-action to LS identifies its kernel with O₂(LS),
using O₂(LS) = LS ∩ O₂(H). The quotient lifting theorem then gives the
required generation modulo Q without using later factorizations.
The independently owned natural-action and Thompson-image inputs remain
explicit in the conditional assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3)
and C.5.6, printed pp.155–157 (PDF pp.166–168).
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
open Subgroup Baumann.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

omit [Finite G] in
private theorem J_le_S : Stellmacher.elementaryAbelianMaxJ R ≤ S R := by
  refine le_inf (sSup_le fun _ hE => hE.1) ?_
  intro j hj
  apply mem_centralizer_iff.mpr
  intro w hw
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 j hj |>.symm

private theorem marked_baumann_image (h : Configuration K A H R L)
    {x : G} (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L)
    (m : NaturalActionModel H L)
    (hJ : ((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient =
      ChapterB.Offenders.D 5) :
    ((S R).subgroupOf H).map m.quotient = ChapterB.Offenders.D 5 := by
  have hSH : S R ≤ H := inf_le_left.trans (h.join_eq ▸ le_sup_right)
  have hVH : (U L).map (MulAut.conj x).toMonoidHom ≤ H :=
    (hspan ▸ le_sup_left).trans hSH
  have hQH : Q R L ≤ H := (pCoreIn_le 2 _).trans (Baumann.block_baumann_join_le_H h)
  have hQ : ((Q R L).subgroupOf H).map m.quotient = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, m.kernel]
    intro q hq
    have hh := Baumann.localCore_le_HCore h hq
    obtain ⟨a, ha, he⟩ := hh
    exact (show a = q from Subtype.ext he) ▸ ha
  have he : ((S R).subgroupOf H).map m.quotient =
      (((U L).map (MulAut.conj x).toMonoidHom).subgroupOf H).map m.quotient := by
    rw [hspan, subgroupOf_sup hVH hQH, Subgroup.map_sup, hQ, sup_bot_eq]
  have hD : ChapterB.Offenders.D 5 ≤ ((S R).subgroupOf H).map m.quotient := by
    rw [← hJ]
    exact map_mono (comap_mono J_le_S)
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  let : IsElementaryAbelian 2 ((U L).map (MulAut.conj x).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (((U L).map (MulAut.conj x).toMonoidHom).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2
      ((((U L).map (MulAut.conj x).toMonoidHom).subgroupOf H).map m.quotient) :=
    IsElementaryAbelian.map _
  have hc : IsMulCommutative (((S R).subgroupOf H).map m.quotient) := by
    rw [he]
    infer_instance
  let := hc
  exact le_antisymm
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      ((centralizer_le hD).trans AlternatingFamily.Action.centralizer_D_le)) hD

/-- The marked permutation action and Thompson image give the desired pair
modulo the actual two-core; the even five-cycle lifts into L. -/
theorem alternating_pair_of_action (h : Configuration K A H R L)
    {x : G} (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L)
    (m : NaturalActionModel H L)
    (hJ : ChapterB.Offenders.IsConjugateTo
      (((Stellmacher.elementaryAbelianMaxJ R).subgroupOf H).map m.quotient)
      (ChapterB.Offenders.D 5)) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨m, hm⟩ := AlternatingFamily.Action.exists_marked m _ hJ
  have hS := marked_baumann_image h hspan m hm
  obtain ⟨g, hg, hgen, _⟩ := exists_model_conjugate_pair
    (show ChapterB.Offenders.IsConjugateTo (((S R).subgroupOf H).map m.quotient)
      (ChapterB.Offenders.D 5) by rw [hS]; exact ChapterB.Offenders.IsConjugateTo.refl _)
  rw [← m.block_image] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  let T := L ⊔ S R
  let hTH : T ≤ H := Baumann.block_baumann_join_le_H h
  let f := m.quotient.comp (inclusion hTH)
  let y' : T := ⟨y, mem_sup_left hy⟩
  have hk := restriction_kernel h m.quotient m.kernel
  refine ⟨y, hy, lift_quotient_pair (y := y') hspan f hk ?_⟩
  change ((S R).subgroupOf T).map f ⊔
    (((S R).subgroupOf T).map f).map (MulAut.conj (f y')).toMonoidHom = ⊤
  rw [restrict_image hTH le_sup_right]
  exact hgen

/-- Conditional permutation branch, using the independently owned action
construction and actual Thompson-image theorem. -/
theorem alternating_pair_of_inputs (ha : NaturalActionInput (G := G) K)
    (hj : ThompsonImageInput (G := G) K) (h : Configuration K A H R L)
    (hL : ChapterC.IsAlternatingBlock L 5) {x : G}
    (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  have hc := Baumann.singleBlockCentralizerInput H R L h.characteristicTwo h.sylow
    h.normalizes_L h.join_eq h.block
  obtain ⟨m⟩ := ha A H R L h hc hL
  exact alternating_pair_of_action h hspan m (hj A H R L h hc hL m)
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration

end
