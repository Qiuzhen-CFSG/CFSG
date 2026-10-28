module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourReturn
import all CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourOrbits
import all CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourReturn

/-!
# Literal long- and short-root representatives of the unitary plane core

Normalize a nonzero Hermitian matrix under the actual plane parabolic. Its
zero-determinant orbit gives the opposite root center; its nonzero-determinant
orbit gives the specified short root. Transport the conjugator through the
whole marked amalgam, retaining the original residual core and opposite center.

The `import all` edges intentionally share the internal matrix normalization
and root identification proofs of FourOrbits and FourReturn; public statements
use only the native root marks and the literal subgroup maps.

Source: Aschbacher--Smith F.4.30,35,43, pp.291--292,296.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourRootClasses
open GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open SourceNormalizer.FourOrbits
variable (m : ℕ) (hm : 1 ≤ m) [NeZero m]
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm

private theorem short_normalize :
    ∃ g ∈ planeParabolic m hm,
      g * FourShortTransport.shortRoot m hm * g⁻¹ =
        FourOrbits.element m hm (representative m 1) := by
  let Y := planeHermitianEquiv m (shortParameter F σ)
  have hY : Y ≠ 0 := by
    intro he
    have hh := congrArg (fun X : Space m => X.val 0 1) he
    simp [Y,planeHermitianEquiv,shortParameter] at hh
  have hf : form m Y = 1 := by
    apply Subtype.ext
    simp [FiniteModel.form,determinant,Y,planeHermitianEquiv,shortParameter,Matrix.det_fin_two,CharTwo.neg_eq]
  obtain ⟨g,hg,hge⟩ := FourOrbits.element_normalize m hm Y hY
  have he : FourOrbits.element m hm Y = FourShortTransport.shortRoot m hm := by
    rw [FourOrbits.element_eq]
    change projection m hm (unipotentSU F σ hσ
      ((planeHermitianEquiv m).symm (planeHermitianEquiv m (shortParameter F σ)))) = _
    rw [(planeHermitianEquiv m).symm_apply_apply]
    rfl
  exact ⟨g,hg,by rwa [he,hf] at hge⟩

/-- The two explicit root marks cover the native plane core under the full
plane parabolic, retaining the conjugator needed for literal transports. -/
theorem core_root_orbits (x : ProjectiveGroup m hm)
    (hx : x ∈ FourPlacement.planeCore m hm) (hx1 : x ≠ 1) :
    ∃ g ∈ planeParabolic m hm,
      g*x*g⁻¹ = projection m hm (longLocal F σ hσ).val ∨
      g*x*g⁻¹ = FourShortTransport.shortRoot m hm := by
  obtain ⟨a,ha,rfl⟩ := hx
  change (a : ProjectiveGroup m hm) ≠ 1 at hx1
  change ∃ g ∈ planeParabolic m hm,
    g*(a : ProjectiveGroup m hm)*g⁻¹ = projection m hm (longLocal F σ hσ).val ∨
    g*(a : ProjectiveGroup m hm)*g⁻¹ = FourShortTransport.shortRoot m hm
  obtain ⟨X,hX⟩ := (L2TwoCoreEquiv m hm).surjective ⟨a,ha⟩
  have hxe : (a : ProjectiveGroup m hm) = FourOrbits.element m hm X.toAdd :=
    (congrArg (fun v : pCore 2 (L2 m hm) => (v.val : ProjectiveGroup m hm)) hX).symm
  have hX0 : X.toAdd ≠ 0 := by
    intro he
    rw [hxe,he,FourOrbits.element_zero] at hx1
    exact hx1 rfl
  obtain ⟨g,hg,hgX⟩ := FourOrbits.element_normalize m hm X.toAdd hX0
  by_cases hc : form m X.toAdd = 0
  · refine ⟨g,hg,Or.inl ?_⟩
    rw [hxe,hgX,hc,FourReturn.long_element]
  · obtain ⟨k,hk,hkc⟩ := FourOrbits.representative_torus m hm (form m X.toAdd) hc
    obtain ⟨s,hs,hse⟩ := short_normalize m hm
    refine ⟨s⁻¹*(k*g),(planeParabolic m hm).mul_mem ((planeParabolic m hm).inv_mem hs)
      ((planeParabolic m hm).mul_mem hk hg),Or.inr ?_⟩
    rw [hxe]
    calc
      _ = s⁻¹*(k*(g*FourOrbits.element m hm X.toAdd*g⁻¹)*k⁻¹)*s := by group
      _ = s⁻¹*FourOrbits.element m hm (representative m 1)*s := by rw [hgX,hkc]
      _ = FourShortTransport.shortRoot m hm := by rw [←hse]; group


variable {G : Type*} [Group G] [Finite G]
/-- The specified endpoint and whole-middle maps carry the two native root
orbits to the original residual, including the original opposite center. -/
theorem marked_core_root_orbits (P : Fin 2 → Subgroup G) (L K : Subgroup G)
    (hr : ∀ i, (solvableResidual (P i)).map (P i).subtype = ![L,K] i)
    (hm' : 1 < m)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (amalgam m hm).reverse) :
    ∃ z ∈ L.pCoreIn 2, z ∈ (center K).map K.subtype ∧ orderOf z=2 ∧
      ∀ x ∈ L.pCoreIn 2, x ≠ 1 → ∃ g ∈ P 0,
        g*x*g⁻¹=z ∨ g*x*g⁻¹=(FourShortTransport.sourceShort m hm e).val := by
  obtain ⟨f,hf,ht,hzcenter⟩ := FourShortMarked.marked_plane_equiv_with_map P L K hr m hm hm' e
  let B := localFactor F (UnitaryFourFlag.form F σ hσ)
  let z₀ : B := longLocal F σ hσ
  let z := f z₀
  have hz₀ : z₀ ∈ pCore 2 B := by
    rw [←radical_eq_twoCore]
    exact (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).property
  have hzL : z ∈ pCore 2 L := by
    rw [←pCore_map_iso 2 f]
    exact mem_map_of_mem _ hz₀
  have hz2 : orderOf z.val=2 := (Subgroup.orderOf_coe z).trans
    ((f.orderOf_eq z₀).trans ((Subgroup.orderOf_coe
      (SourceNormalizer.FourShortRoot.longMark F σ hσ)).trans
        (SourceNormalizer.FourShortRoot.longMark_order F σ hσ)))
  have hLP : L ≤ P 0 := by
    rw [←show (solvableResidual (P 0)).map (P 0).subtype = L from hr 0]
    exact map_subtype_le _
  refine ⟨z.val,mem_map_of_mem L.subtype hzL,hzcenter,hz2,?_⟩
  intro x hx hx1
  let xL : L := ⟨x,pCoreIn_le 2 L hx⟩
  have hxL : xL ∈ pCore 2 L := (mem_map_iff_mem L.subtype_injective).mp hx
  have hxB : f.symm xL ∈ pCore 2 B := by
    rw [←pCore_map_iso 2 f.symm]
    exact mem_map_of_mem _ hxL
  have hnative : projection m hm (f.symm xL).val ∈ FourPlacement.planeCore m hm := by
    rw [←FourPlacement.matrix_plane_core_map]
    exact mem_map_of_mem _ ⟨f.symm xL,hxB,rfl⟩
  let xP : P 0 := ⟨x,hLP xL.property⟩
  have hxmark : (e.left xP).val = projection m hm (f.symm xL).val := by
    have hh := hf (f.symm xL) (hLP (f _).property)
    simpa only [f.apply_symm_apply] using hh
  have hnative1 : projection m hm (f.symm xL).val ≠ 1 := by
    rw [←hxmark]
    intro he
    have hxe : xP = 1 := e.left.injective ((Subtype.ext he).trans e.left.map_one.symm)
    exact hx1 (congrArg Subtype.val hxe)
  obtain ⟨g,hg,hgroot⟩ := core_root_orbits m hm _ hnative hnative1
  let k : P 0 := e.left.symm ⟨g,hg⟩
  have transport (y : B) (he : g*projection m hm (f.symm xL).val*g⁻¹=projection m hm y.val) :
      k.val*x*k.val⁻¹=(f y).val := by
    have hh : k*xP*k⁻¹ = ⟨(f y).val,hLP (f y).property⟩ := by
      apply e.left.injective
      apply Subtype.ext
      simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
      rw [show e.left k = ⟨g,hg⟩ from e.left.apply_symm_apply _,hxmark,hf y _]
      exact he
    exact congrArg Subtype.val hh
  refine ⟨k.val,k.property,?_⟩
  rcases hgroot with he | he
  · exact Or.inl (transport z₀ he)
  · exact Or.inr ((transport (shortLocal F σ hσ) he).trans ht)

end CFSG.Quasithin.ChapterF.UnitarySource.FourRootClasses
