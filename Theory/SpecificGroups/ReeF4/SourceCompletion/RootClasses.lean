module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizer
import all Theory.SpecificGroups.ReeF4.LinearLocalFixer
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry

/-!
# The two native Ree root involution classes

The end-node torus scales the additive end-root parameter by a square. Every
nonzero ratio in the finite coefficient field has a square root. Conjugating
this torus action by the fixed fourth-root Weyl word proves conjugacy of all
nonzero short-root parameters. The established Borel orbit gives the long
class. Sylow conjugacy and the exact unipotent-center calculation identify
long-root involutions with the two-central involutions. The short centralizer
contains a perfect PSL₂ subgroup, whereas the long centralizer lies in the
three-free Suzuki parabolic; hence these two classes are distinct.

All statements concern the actual exceptional-twist fixed carrier. The root
orbit results include m=0; separation and the two-central identification hold
for every m>0, including q=8. Exhaustion of arbitrary involutions by these two
classes is a separate obligation, not asserted in this module.
Source: Aschbacher–Smith F.4.27(3), printed p.288 (`refs/quasithin.pdf`),
and GLS3 Table 2.4 (`refs/KGroup/GLS3/chapter2.tex`). Internal imports reuse
existing coroot and Weyl calculations without changing their public boundary.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Theory.GroupTheory Parabolics LargeLocalSeeds EvenInvolutionGeometry
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Binary.FixedGeometry LinearCommutators
open Parabolics.OuterLocal.SuzukiCommutators
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open BlockParameters.FieldRecovery

private theorem end_pairing (i j : Fin 4) (hi : i = 0 ∨ i = 3)
    (hj : j = 0 ∨ j = 3) :
    typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
      (typeF4SimpleRootIndex j) = if i = j then 2 else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [show (↑(typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
    (typeF4SimpleRootIndex j)) : ℝ) =
      typeF4RootPairing.pairing (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) from
        typeF4RootPairing.algebraMap_pairingIn ℤ _ _]
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot,
    typeF4SimpleRootIndex_val, typeF4SimpleRootIndex_val]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    norm_num [typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

private theorem endTorus_endRoot (m : ℕ) (u : (CoefficientField m)ˣ)
    (a : CoefficientField m) :
    endTorusWord m u * endRootWord m a * (endTorusWord m u)⁻¹ =
      endRootWord m ((u : CoefficientField m)^2 * a) := by
  calc
    _ = (endTorusWord m u * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) a *
        (endTorusWord m u)⁻¹) *
        (endTorusWord m u * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
          (rootFieldEnd m (typeF4SimpleRootIndex 0) a) * (endTorusWord m u)⁻¹) := by
      simp only [endRootWord]; group
    _ = _ := by
      rw [LinearLocalFixer.endTorusWord_root, LinearLocalFixer.endTorusWord_root]
      simp [end_pairing _ _ (Or.inl rfl) (Or.inr rfl),
        end_pairing _ _ (Or.inr rfl) (Or.inl rfl),
        endRootWord]

/-- All nonzero parameters on the actual short-root curve are conjugate. -/
theorem shortRoot_isConj (m : ℕ) {a b : CoefficientField m}
    (ha : a ≠ 0) (hb : b ≠ 0) : IsConj (shortRootElement m a) (shortRootElement m b) := by
  obtain ⟨c,hc⟩ := (Finite.surjective_of_injective (frobenius_inj (CoefficientField m) 2)) (b/a)
  have hc' : c^2 = b/a := hc
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0,zero_pow (by decide)] at hc'
    exact div_ne_zero hb ha hc'.symm
  let u := Units.mk0 c hc0
  let w : Model m := ⟨simpleWord m fourthWord, by simpa only [mem_fixedSubgroup] using fourthWord_fixed m⟩
  let z : Model m := seedEquiv m .linear (endTorusElement (canonicalLocalBlockInput m) u)
  apply isConj_iff.mpr
  refine ⟨w*z*w⁻¹, ?_⟩
  apply toSplitGroup_injective m
  simp only [map_mul,map_inv,shortRootElement_coe]
  have hw : toSplitGroup m w = simpleWord m fourthWord := toSplitGroup_apply m w
  have hz : toSplitGroup m z = endTorusWord m u := by
    simp only [z,seedEquiv_coe,endTorusElement]
  rw [hw,hz]
  change (simpleWord m fourthWord * endTorusWord m u * (simpleWord m fourthWord)⁻¹) *
    rootWord m 3 a *
      (simpleWord m fourthWord * endTorusWord m u * (simpleWord m fourthWord)⁻¹)⁻¹ = _
  rw [←fourthWord_conjugate_end,←fourthWord_conjugate_end]
  calc
    _ = simpleWord m fourthWord *
        (endTorusWord m u * endRootWord m a * (endTorusWord m u)⁻¹) *
          (simpleWord m fourthWord)⁻¹ := by group
    _ = _ := by
      rw [endTorus_endRoot]
      rw [fourthWord_conjugate_end, fourthWord_conjugate_end]
      have he : c^2*a = b := by rw [hc', div_mul_cancel₀ _ ha]
      simpa [u] using congrArg (rootWord m 3) he

/-- Each nonzero long-root parameter belongs to the same actual conjugacy class. -/
theorem longRoot_isConj (m : ℕ) {a b : CoefficientField m}
    (ha : a ≠ 0) (hb : b ≠ 0) : IsConj (longRootElement m a) (longRootElement m b) := by
  obtain ⟨g,_,hg⟩ := longRoot_borel_orbit m _ _
    ((mem_longRootGroup m _).mpr ⟨a,rfl⟩)
    ((mem_longRootGroup m _).mpr ⟨b,rfl⟩) (by simpa using ha) (by simpa using hb)
  exact isConj_iff.mpr ⟨g,hg.symm⟩

/-- Any two native long-root involutions are conjugate. -/
theorem long_class_isConj {m : ℕ} {x y : Model m}
    (hx : IsLongRootInvolution x) (hy : IsLongRootInvolution y) : IsConj x y := by
  obtain ⟨a,ha,hax⟩ := hx
  obtain ⟨b,hb,hby⟩ := hy
  exact hax.symm.trans ((longRoot_isConj m ha hb).trans hby)

/-- Any two native short-root involutions are conjugate. -/
theorem short_class_isConj {m : ℕ} {x y : Model m}
    (hx : IsShortRootInvolution x) (hy : IsShortRootInvolution y) : IsConj x y := by
  obtain ⟨a,ha,hax⟩ := hx
  obtain ⟨b,hb,hby⟩ := hy
  exact hax.symm.trans ((shortRoot_isConj m ha hb).trans hby)

private theorem twoCentral_map {m : ℕ} {x : Model m}
    (hx : IsTwoCentralInvolution x) (e : MulAut (Model m)) :
    IsTwoCentralInvolution (e x) := by
  obtain ⟨ho,S,hx,hc⟩ := hx
  refine ⟨(e.orderOf_eq x).trans ho,S.mapSurjective e.surjective,
    mem_map_of_mem e.toMonoidHom hx,?_⟩
  rintro y ⟨z,hz,rfl⟩
  exact (hc z hz).map e.toMonoidHom

/-- Long-root involutions are exactly the involutions in Sylow centers. -/
theorem long_iff_twoCentral {m : ℕ} (hm : 0 < m) (x : Model m) :
    IsLongRootInvolution x ↔ IsTwoCentralInvolution x := by
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  have hU' : (U : Subgroup (Model m)) = unipotent m :=
    hU.trans (unipotent_eq_rootUnipotent m)
  constructor
  · rintro ⟨a,ha,hax⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp hax
    have ht : IsTwoCentralInvolution (longRootElement m a) := by
      refine ⟨longRootElement_orderOf m ha,U,?_,?_⟩
      · change longRootElement m a ∈ (U : Subgroup (Model m))
        rw [hU']; exact longRootElement_mem_unipotent m a
      · intro y hy
        change y ∈ (U : Subgroup (Model m)) at hy
        rw [hU'] at hy
        exact longRootElement_commute_unipotent m a y hy
    exact hg ▸ twoCentral_map ht (MulAut.conj g)
  · rintro ⟨ho,P,hx,hc⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model m) P U
    have hxU : (MulAut.conj g) x ∈ unipotent m := by
      rw [←hU',←hg]
      exact ⟨x,hx,rfl⟩
    have hcomm : ∀ y ∈ unipotent m, Commute ((MulAut.conj g) x) y := by
      intro y hy
      rw [←hU',←hg] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      exact (hc z hz).map (MulAut.conj g).toMonoidHom
    obtain ⟨a,ha,he⟩ := central_involution_eq_longRootElement m hm _ hxU
      (((MulAut.conj g).orderOf_eq x).trans ho) hcomm
    refine ⟨a,ha,?_⟩
    have hh : IsConj x ((MulAut.conj g) x) := isConj_iff.mpr ⟨g,rfl⟩
    rw [he] at hh
    exact hh.symm

/-- The two native root classes are disjoint, using their different cubic centralizers. -/
theorem long_not_short {m : ℕ} (hm : 0 < m) {x : Model m}
    (hx : IsLongRootInvolution x) : ¬ IsShortRootInvolution x := by
  obtain ⟨a,ha,hax⟩ := hx
  rintro ⟨b,hb,hbx⟩
  have hs : IsShortRootInvolution (longRootElement m a) := ⟨b,hb,hbx.trans hax.symm⟩
  have hd := (short_centralizer_residual_three_dvd hm hs).trans (card_subgroup_dvd_card _)
  have hP := long_centralizer_le_parabolic hm
    ((mem_longRootGroup m _).mpr ⟨a,rfl⟩) (by simpa using ha)
  have h3 := hd.trans (card_dvd_of_le hP)
  rw [←parabolic_eq_rootParabolic] at h3
  exact ConverseParabolics.suzuki_parabolic_three_free hm h3

end ReeF4.SourceCompletion
