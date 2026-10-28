module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction.Image
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.SectionAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# Radical factorization from the actual marked component residual

In the PSL₃(2) branch, R normalizes Y_L and fixes Y_L/O₂(Y_L).
The marked parabolic calculation represents every induced R-action by an
inner element of O₂(Y_L). The correction acts trivially on L/O₂(L)
and lies in O₂(LR). Radical saturation gives the reverse containment.

This supplies the factorization R = O₂(LR)O₂(Y_L) used in 15.3.23,
without a classification assumption from C.2.7(3). The parabolic marking
is supplied independently from the original Sylow intersection.

Source: Aschbacher–Smith, 15.3.23, printed p.1128.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions.NaturalActions.SylowAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem actor_section_kernel_le_core {L R : Subgroup G}
    (hR : IsPGroup 2 R) (hn : R ≤ normalizer (L : Set G)) (hc : L.pCoreIn 2 ≤ R) :
    R ⊓ Chapter4.sectionCentralizer L ≤ (L ⊔ R).pCoreIn 2 := by
  let K := R ⊓ Chapter4.sectionCentralizer L
  have hN : normalizer (L : Set G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hRK : R ≤ normalizer (K : Set G) := by
    apply (le_inf R.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact commutatorPreimage_normalized _ _ _ _ hN
      (hn.trans (normalizer (L : Set G)).le_normalizer) hn (hn.trans hN)
  have hCK : L.pCoreIn 2 ≤ K := le_inf hc
    ((Chapter4.le_sectionCentralizer_iff _ L).mpr
      ⟨(L.pCoreIn_le 2).trans L.le_normalizer,
        le_normalizer_iff_commutator_le_left.mp (L.le_normalizer.trans hN)⟩)
  have hLK : L ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((Chapter4.le_sectionCentralizer_iff K L).mp inf_le_right).2.trans hCK)
  exact le_pCoreIn_of_normalizes (hR.to_le inf_le_left)
    (inf_le_left.trans le_sup_right) (sup_le hLK hRK)

/-- A marked parabolic residual absorbs the radical action through its own
two-core. The kernel correction belongs to the actual two-core of LR. -/
theorem radical_factor_of_marked_residual {L R A : Subgroup G}
    (hR : IsPGroup 2 R) (hRL : R ≤ normalizer (L : Set G))
    (hcore : L.pCoreIn 2 ≤ R) (hsat : (L ⊔ R).pCoreIn 2 ≤ R)
    (hAL : A ≤ L) (hAR : A.pCoreIn 2 ≤ R)
    (hRA : R ≤ normalizer (A : Set G)) (hcomm : ⁅R, A⁆ ≤ A.pCoreIn 2)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hmark : (A.subgroupOf L).map (quotientMap L e) = residual P) :
    R = (L ⊔ R).pCoreIn 2 ⊔ A.pCoreIn 2 := by
  have hfker : IsPGroup 2 (quotientMap L e).ker := by
    unfold quotientMap
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  apply le_antisymm ?_ (sup_le hsat hAR)
  intro r hr
  let rn : normalizer (L : Set G) := ⟨r, hRL hr⟩
  have hstable : (residual P).map (CoreActions.NaturalActions.SylowAction.action L e rn).toMonoidHom = residual P := by
    rw [← hmark]
    exact action_preserves_image L A e rn (hRA hr)
  have hdisp : ∀ a ∈ residual P,
      CoreActions.NaturalActions.SylowAction.action L e rn a * a⁻¹ ∈ (residual P).pCoreIn 2 := by
    intro a ha
    rw [← hmark] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [CoreActions.NaturalActions.SylowAction.action_apply, ← map_inv, ← map_mul]
    rw [← hmark, ← map_pCoreIn_of_ker_isPGroup (quotientMap L e) hfker,
      pCoreIn_subgroupOf 2 A L hAL]
    apply mem_map_of_mem
    change r * (x : G) * r⁻¹ * (x : G)⁻¹ ∈ A.pCoreIn 2
    exact hcomm (commutator_mem_commutator hr hx)
  have hpow : ∃ n : ℕ, CoreActions.NaturalActions.SylowAction.action L e rn ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    have hrn : rn ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun x : R => (x : G)) hn)
    exact ⟨n, by rw [← map_pow, hrn, map_one]⟩
  obtain ⟨g, hg, hact⟩ := two_quotient_fixer_is_conj P hP (CoreActions.NaturalActions.SylowAction.action L e rn)
    hstable hdisp hpow
  rw [← hmark, ← map_pCoreIn_of_ker_isPGroup (quotientMap L e) hfker,
    pCoreIn_subgroupOf 2 A L hAL] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  let an : normalizer (L : Set G) := ⟨a, L.le_normalizer a.property⟩
  have hact' : CoreActions.NaturalActions.SylowAction.action L e rn = CoreActions.NaturalActions.SylowAction.action L e an :=
    hact.trans (action_inner L e a).symm
  have hzero : CoreActions.NaturalActions.SylowAction.action L e (an⁻¹ * rn) = 1 := by
    rw [map_mul, map_inv, hact', inv_mul_cancel]
  have hsection : (a : G)⁻¹ * r ∈ Chapter4.sectionCentralizer L := by
    apply (ComponentIntersection.InnerSplitting.sectionAction_eq_one_iff L (an⁻¹ * rn)).mp
    apply (MulAut.congr e).injective
    exact hzero.trans (map_one (MulAut.congr e)).symm
  have hcorr : (a : G)⁻¹ * r ∈ (L ⊔ R).pCoreIn 2 :=
    actor_section_kernel_le_core hR hRL hcore
      ⟨R.mul_mem (R.inv_mem (hAR ha)) hr, hsection⟩
  have hh := ((L ⊔ R).pCoreIn 2 ⊔ A.pCoreIn 2).mul_mem
    (mem_sup_right ha) (mem_sup_left hcorr)
  simpa only [subtype_apply, mul_inv_cancel_left] using hh

/-- The actual source radical fixes Y_L/O₂(Y_L): its commutators lie both
in Y_L and in the two-core of Y₊S. This supplies the model's quotient-fixing
premise before any assertion that S normalizes L. -/
theorem radical_factor (d : LocalData G) (L : Subgroup G)
    (hRL : d.R ≤ normalizer (L : Set G))
    (hcores : L.pCoreIn 2 ⊔ (YL d L).pCoreIn 2 ≤ d.R)
    (hsat : (L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hmark : ((YL d L).subgroupOf L).map (quotientMap L e) = residual P) :
    d.R = (L ⊔ d.R).pCoreIn 2 ⊔ (YL d L).pCoreIn 2 := by
  have hAY : YL d L ≤ d.Yplus ⊔ d.S :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans le_sup_left
  have hRA : d.R ≤ normalizer (YL d L : Set G) := by
    change d.R ≤ normalizer
      (ComponentIntersection.intersectionResidual d.Yplus L : Set G)
    rw [ComponentIntersection.intersectionResidual,
      ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
      (d.Yplus ⊓ L) (pResidual 2 (d.Yplus ⊓ L : Subgroup G)))
    exact (le_inf (((d.Yplus ⊔ d.S).pCoreIn_le 2).trans
      (sup_le d.Yplus.le_normalizer
        (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice))) hRL).trans
      inf_normalizer_le_normalizer_inf
  have hAR : YL d L ≤ normalizer (d.R : Set G) :=
    hAY.trans ((d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))))
  have hcomm : ⁅d.R, YL d L⁆ ≤ (YL d L).pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_right.mp hRA)
      (le_normalizer_iff_commutator_le_left.mp hAR)).trans
      (inf_pCoreIn_le_of_le 2 hAY)
  exact radical_factor_of_marked_residual (isPGroup_pCoreIn 2 _) hRL
    (le_sup_left.trans hcores) hsat
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right)
    (le_sup_right.trans hcores) hRA hcomm e P hP hmark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
