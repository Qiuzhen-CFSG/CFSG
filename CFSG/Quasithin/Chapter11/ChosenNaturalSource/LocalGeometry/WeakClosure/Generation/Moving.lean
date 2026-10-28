module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Cartan
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The moving Hall branch before the doubled-module recognition

The preceding Sp₄/G₂ normalization clause excludes both of those models.
The full SL₃ marking kills C_V(L), so the proved TI theorem forces C_V(B)=1
for every subgroup B of M moving V. In particular C_V(H)=1. A central
involution in the original nonzero T-invariant V is then moved by H;
3.1.8(3) and the FSU commutator theorem give L=[L,J(T)].

Source: Aschbacher--Smith, 11.2.1, second paragraph on printed p.767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The moving branch selects the actual full SL₃ action on V/C_V(L). -/
theorem linear_of_moving (hrows : OtherRowsNormalize D S)
    {H B : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hBH : B ≤ H) (hBM : B ≤ normalizer (L : Set G))
    (hmove : ¬ B ≤ normalizer (V : Set G)) :
    Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) := by
  cases S.natural with
  | sl3 hm => exact hm
  | sp4 hm => exact (hmove ((le_inf hBH hBM).trans (hrows H hH (Or.inl hm)))).elim
  | g2 hm => exact (hmove ((le_inf hBH hBM).trans (hrows H hH (Or.inr hm)))).elim

/-- TI of the literal seed makes every moving subgroup of M fixed-free. -/
theorem fixed_eq_bot_of_moving
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {B : Subgroup G} (hBM : B ≤ normalizer (L : Set G))
    (hmove : ¬ B ≤ normalizer (V : Set G)) :
    V ⊓ centralizer (B : Set G) = ⊥ := by
  obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp hmove
  have hTI := Preliminary.ti_of_centralizer_eq_bot D S
    (Preliminary.sl3_centralizer_eq_bot D S m) b (hBM hb)
  have hzero : V ⊓ V.map (MulAut.conj b).toMonoidHom = ⊥ :=
    hTI.resolve_right (fun he => hbn (mem_normalizer_iff_map_conj_eq.mpr he))
  apply _root_.eq_bot_iff.mpr
  rintro v ⟨hv,hc⟩
  have hconj : b * v * b⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr (hc b hb)
  exact mem_bot.mp (hzero ▸ (show v ∈ V ⊓ V.map (MulAut.conj b).toMonoidHom from
    ⟨hv, v, hv, hconj⟩))

/-- A nonzero normal elementary subgroup of T contains an original central
involution; the subgroup and its ambient embedding are unchanged. -/
theorem seed_central_involution :
    ∃ z : G, z ∈ V ∧ z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 := by
  let U := V.subgroupOf (T : Subgroup G)
  let : U.Normal := normal_subgroupOf_of_le_normalizer S.sylow_normalizes
  have hU : U ≠ ⊥ := by
    intro hz
    have he := map_subgroupOf_eq_of_le D.le_sylow
    change U.map (T : Subgroup G).subtype = V at he
    rw [hz, Subgroup.map_bot] at he
    exact D.ne_bot he.symm
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hU
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨x,hx,hz⟩ := exists_nontrivial_center_mem_normal (p := 2) U
  have hx2 : (x.val : G) ^ 2 = 1 := by
    let := D.elementary
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x.val : G) x.property
  refine ⟨x.val,x.property,?_,fun he => hx (Subtype.ext (Subtype.ext he))⟩
  refine ⟨x.val, ⟨⟨x.val,hz⟩, subset_closure ?_, rfl⟩, rfl⟩
  change (⟨x.val,hz⟩ : center T) ^ (2 ^ 1) = 1
  apply Subtype.ext
  apply Subtype.ext
  simpa using hx2

/-- The source's Thompson equality follows from fixed-freeness on H. -/
theorem thompson_of_fixed_eq_bot {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hfixed : V ⊓ centralizer (H : Set G) = ⊥) :
    L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let E := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) E.maximalLocal :=
    (maximalLocal_eq D S).symm ▸ hH
  have hz : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      (center H).map H.subtype := by
    intro hc
    obtain ⟨z,hzV,hzZ,hzne⟩ := seed_central_involution D S
    obtain ⟨c,hc,rfl⟩ := hc hzZ
    apply hzne
    apply mem_bot.mp
    rw [← hfixed]
    refine ⟨hzV,?_⟩
    intro h hh
    exact congrArg H.subtype (mem_center_iff.mp hc ⟨h,hh⟩)
  have huniq := E.lemma_3_2_3_uniqueness hu
  have hJ := (E.qrcHypotheses hu hH').thompson_moves_of_noncentral_omega
    S.source.simpleQTKE huniq.1 huniq.2.2 E.module_ne_bot hz
  have he := E.actor_eq_commutator_of_thompson_not_centralizes hu hJ
  simpa only [D.localOrbit_eq] using he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
