module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.SpecificGroups.ReeF4.LinearLocalFixer
public import Theory.SpecificGroups.ReeF4.ParabolicResiduals
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.EightAmbient

/-!
# The long-root center and its actual Ree parabolic orbit

Characteristic two puts each residual center inside the unipotent group.
The native positive-center calculation then places it on the long-root
curve. The Suzuki seed commutes with that whole curve, giving equality
for its center. The end-node torus scales its parameter by every nonzero
field element, so its nonidentity elements form one Borel orbit.

These results supply the nontrivial center and transitivity needed by the
original full-normalizer centralizer argument in source 5.3.3 and F.4.34.
They use the actual fixed matrix group at every positive parameter,
including q=8, and assume neither ambient simplicity nor recognition.
Source: Aschbacher–Smith, printed pp.659,291, and GLS3 Table 2.4;
`refs/quasithin.pdf`, `refs/KGroup/GLS3/chapter2.tex`.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Theory.GroupTheory Parabolics LargeLocalSeeds EvenInvolutionGeometry
open LinearCommutators
open Theory.AlgebraicGroup.StandardRootSystem

/-- Every residual-center element belongs to the actual long-root group. -/
theorem localFactor_center_le_longRoot {m : ℕ} (hm : 0 < m) (s : Side) :
    (center (localFactor m s)).map (localFactor m s).subtype ≤ longRootGroup m := by
  have hc : center (localFactor m s) ≤ pCore 2 (localFactor m s) :=
    (center_le_centralizer (pCore 2 (localFactor m s) : Set (localFactor m s))).trans
      (by
        rw [←localFactor_generalizedFitting hm s]
        exact centralizer_generalizedFitting_le _)
  intro z hz
  have hzU : z ∈ unipotent m := by
    have hr := (map_mono (f := (localFactor m s).subtype) hc) hz
    rw [local_pCore_map] at hr
    exact radical_le_unipotent m s hr
  obtain ⟨a,ha,rfl⟩ := hz
  have hcomm : ∀ u ∈ unipotent m, Commute a.val u := by
    intro u hu
    exact (congrArg Subtype.val
      (mem_center_iff.mp ha ⟨u,unipotent_le_localFactor m s hu⟩)).symm
  obtain ⟨t,ht⟩ := eq_longRootElement_of_central_unipotent m hm a.val hzU hcomm
  exact (mem_longRootGroup m _).mpr ⟨t,ht.symm⟩

/-- The right residual's center is precisely the genuine long-root group. -/
theorem suzuki_center_eq_longRoot {m : ℕ} (hm : 0 < m) :
    (center (localFactor m .suzuki)).map (localFactor m .suzuki).subtype = longRootGroup m := by
  apply le_antisymm (localFactor_center_le_longRoot hm .suzuki)
  intro z hz
  obtain ⟨t,rfl⟩ := (mem_longRootGroup m z).mp hz
  refine ⟨⟨longRootElement m t, unipotent_le_localFactor m .suzuki
    (longRootElement_mem_unipotent m t)⟩,mem_center_iff.mpr ?_,rfl⟩
  intro x
  apply Subtype.ext
  have h := CentralCovers.TwoPrimary.QuartetSplitting.EightAmbient.central_fifth_commute_seed
    m t x (by rw [seed_eq_localFactor]; exact x.property)
  exact h.eq.symm

/-- Nonzero long-root parameters form one orbit under the actual fixed torus. -/
theorem longRoot_borel_orbit (m : ℕ) (x y : Model m)
    (hx : x ∈ longRootGroup m) (hy : y ∈ longRootGroup m)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ borel m, y = g*x*g⁻¹ := by
  obtain ⟨a,rfl⟩ := (mem_longRootGroup m x).mp hx
  obtain ⟨b,rfl⟩ := (mem_longRootGroup m y).mp hy
  have ha : a ≠ 0 := by simpa using hx1
  have hb : b ≠ 0 := by simpa using hy1
  let u : (CoefficientField m)ˣ := Units.mk0 (b/a) (div_ne_zero hb ha)
  let z := seedEquiv m .linear (endTorusElement (canonicalLocalBlockInput m) u)
  have hzT : (z : Model m) ∈ fixedTorus m := by
    change toSplitGroup m z ∈ splitTorus m
    rw [splitTorus_eq_diagonalTorus]
    simpa only [z,seedEquiv_coe,endTorusElement] using
      (show endTorusWord m u ∈ diagonalTorus m from by
        exact (diagonalTorus m).mul_mem (torusWord_mem_diagonalTorus m _ _)
          (torusWord_mem_diagonalTorus m _ _))
  refine ⟨z, (show fixedTorus m ≤ borel m from by
    rw [borel_eq_unipotent_sup_fixedTorus]; exact le_sup_right) hzT, ?_⟩
  apply toSplitGroup_injective m
  simp only [map_mul,map_inv,longRootElement_coe,z,seedEquiv_coe,endTorusElement]
  rw [LinearLocalFixer.endTorus_longRoot]
  congr 1
  simp [u,ha]

/-- The right center has one nonidentity parabolic orbit at every positive parameter. -/
theorem suzuki_center_orbit {m : ℕ} (hm : 0 < m)
    (x y : Model m)
    (hx : x ∈ (center (localFactor m .suzuki)).map (localFactor m .suzuki).subtype)
    (hy : y ∈ (center (localFactor m .suzuki)).map (localFactor m .suzuki).subtype)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ parabolic m .suzuki, y = g*x*g⁻¹ := by
  obtain ⟨g,hg,he⟩ := longRoot_borel_orbit m x y
    (localFactor_center_le_longRoot hm .suzuki hx)
    (localFactor_center_le_longRoot hm .suzuki hy) hx1 hy1
  exact ⟨g,borel_le_parabolic m .suzuki hg,he⟩

/-- The literal right center contains a long-root involution. -/
theorem suzuki_center_involution {m : ℕ} (hm : 0 < m) :
    ∃ z : center (localFactor m .suzuki), orderOf z = 2 := by
  have hz : longRootElement m 1 ∈
      (center (localFactor m .suzuki)).map (localFactor m .suzuki).subtype := by
    rw [suzuki_center_eq_longRoot hm]
    exact (mem_longRootGroup m _).mpr ⟨1,rfl⟩
  obtain ⟨z,hz,he⟩ := hz
  refine ⟨⟨z,hz⟩,?_⟩
  rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
  change orderOf ((localFactor m .suzuki).subtype z) = 2
  rw [he]
  exact longRootElement_orderOf m one_ne_zero

end ReeF4.SourceCompletion
