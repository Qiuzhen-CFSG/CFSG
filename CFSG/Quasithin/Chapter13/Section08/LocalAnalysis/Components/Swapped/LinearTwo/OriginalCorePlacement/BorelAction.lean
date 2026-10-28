module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalCorePlacement.Automorphisms
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.FullMarkedImages
public import Theory.GroupTheory.PCoreRestriction

/-!
# Parabolic two-cores in the actual component quotient

For A normal in P, an element of O₂(P) acts trivially on A/O₂(A).
The literal residual of the source Borel surjects onto its binary Borel.
Thus the core action fixes that Borel modulo its Sylow two-subgroup.
The inner-automorphism calculation and the trivial component centralizer
then place its image in K₀*, through the original map H → H/O₂(H).

This is the marked-core step in Aschbacher--Smith, 13.8.16(1), printed
pp.952--953 (PDF pp.969--970). The source assembly supplies the Borel,
residual, normality and centralizer premises in the companion module.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.OriginalCorePlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite G] in
private theorem core_displacement (A P : Subgroup G) (hAP : A ≤ P)
    (hn : P ≤ normalizer (A : Set G)) {g : G} (hg : g ∈ P.pCoreIn 2)
    {x : G} (hx : x ∈ A) : g * x * g⁻¹ * x⁻¹ ∈ A.pCoreIn 2 := by
  have hgP := P.pCoreIn_le 2 hg
  have hnQ : P ≤ normalizer (P.pCoreIn 2 : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  apply inf_pCoreIn_le_of_le 2 hAP
  refine ⟨A.mul_mem ((hn hgP x).mp hx) (A.inv_mem hx), ?_⟩
  have hh := (P.pCoreIn 2).mul_mem hg
    ((hnQ (hAP hx) g⁻¹).mp ((P.pCoreIn 2).inv_mem hg))
  change g * x * g⁻¹ * x⁻¹ ∈ P.pCoreIn 2
  simpa only [mul_assoc] using hh

private theorem core_productAction (H K₀ A P : Subgroup G) (hK : K₀ ≤ H)
    (hPH : P ≤ H) (hPK : P ≤ normalizer (K₀ : Set G))
    (e : Source.starImage H K₀ ≃* Q × Q)
    (S : Sylow 2 (Source.starImage H K₀))
    (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (hAP : A ≤ P) (hAB : A ≤ SourceTorus.chosenLift H K₀ hK S)
    (hPB : P ≤ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (hres : A = residual (SourceTorus.chosenLift H K₀ hK S))
    {g : G} (hg : g ∈ P.pCoreIn 2) :
    ∀ x ∈ BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S),
      SourceActions.productAction H K₀ hK e (hPH (P.pCoreIn_le 2 hg))
        (hPK (P.pCoreIn_le 2 hg)) x * x⁻¹ ∈
      (SourceTorus.chosenSylow H K₀ e S : Subgroup (Q × Q)) := by
  let B := SourceTorus.chosenLift H K₀ hK S
  let S' := SourceTorus.chosenSylow H K₀ e S
  let f : A →* BinaryBorel.borel S' :=
    (SourceTorus.toBinary H K₀ hK e S).comp (inclusion hAB)
  have hf : Function.Surjective f :=
    SourceConclusion.residual_binary_surjective H K₀ hK e S hmodel A hAB hres
  have hcore : (pCore 2 A).map f ≤ pCore 2 (BinaryBorel.borel S') :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  have hnA : P ≤ normalizer (A : Set G) := by
    rw [hres]
    exact hPB.trans (normalizer_le_residual_normalizer B)
  intro x hx
  obtain ⟨y, hy⟩ := hf ⟨x, hx⟩
  have hd := core_displacement A P hAP hnA hg y.property
  obtain ⟨z, hz, hzg⟩ := hd
  have hz' := hcore (mem_map_of_mem f hz)
  rw [BinaryBorel.twoCore] at hz'
  have heq : (f z : Q × Q) =
      SourceActions.productAction H K₀ hK e (hPH (P.pCoreIn_le 2 hg))
        (hPK (P.pCoreIn_le 2 hg)) (f y) * (f y : Q × Q)⁻¹ := by
    let b := inclusion hAB y
    let a := B.normalizerMonoidHom ⟨g, hPB (P.pCoreIn_le 2 hg)⟩
    have he : inclusion hAB z = a b * b⁻¹ := Subtype.ext hzg
    change (SourceTorus.toBinary H K₀ hK e S (inclusion hAB z) : Q × Q) = _
    rw [he, map_mul, map_inv, coe_mul, coe_inv]
    rw [← SourceActions.productAction_toBinary H K₀ hK e S
      (hPH (P.pCoreIn_le 2 hg)) (hPK (P.pCoreIn_le 2 hg)) (hPB (P.pCoreIn_le 2 hg))]
    rfl
  change (f z : Q × Q) ∈ (S' : Subgroup (Q × Q)) at hz'
  rw [heq, hy] at hz'
  exact hz'

/-- The relative parabolic core lands in the marked component orbit. -/
theorem star_core_le (H K₀ A P : Subgroup G) (hK : K₀ ≤ H)
    (hPH : P ≤ H) (hPK : P ≤ normalizer (K₀ : Set G))
    (e : Source.starImage H K₀ ≃* Q × Q)
    (S : Sylow 2 (Source.starImage H K₀))
    (hmodel : ClassicalGroup.IsPSL Q 2 4)
    [IsQuasisimple Q]
    [(Source.starImage H K₀).Normal]
    (hcentral : centralizer (Source.starImage H K₀ : Set (Source.Hstar H)) = ⊥)
    (hAP : A ≤ P) (hAB : A ≤ SourceTorus.chosenLift H K₀ hK S)
    (hPB : P ≤ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (hres : A = residual (SourceTorus.chosenLift H K₀ hK S)) :
    Source.starImage H (P.pCoreIn 2) ≤ Source.starImage H K₀ := by
  have hZ := center_eq_bot_of_psl2 hmodel
  have hm := hmodel
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eQ := eF.trans eA
  rintro _ ⟨g, hg, rfl⟩
  let a := SourceActions.productAction H K₀ hK e
    (hPH (P.pCoreIn_le 2 hg)) (hPK (P.pCoreIn_le 2 hg))
  obtain ⟨z, hz⟩ := binary_inner eQ hZ hmodel
    (SourceTorus.chosenSylow H K₀ e S) a
    (core_productAction H K₀ A P hK hPH hPK e S
      hmodel hAP hAB hPB hres hg)
  have hin : (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) g) :
      MulAut (Source.starImage H K₀)) ∈ MulAut.innerSubgroup (Source.starImage H K₀) := by
    refine ⟨e.symm z, ?_⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hh := SourceActions.productAction_star H K₀ hK e
      (hPH (P.pCoreIn_le 2 hg)) (hPK (P.pCoreIn_le 2 hg)) (e y)
    change (e.symm (a (e y)) : Source.Hstar H) = _ at hh
    rw [hz, MulAut.conj_apply, map_mul, map_mul, map_inv, e.symm_apply_apply] at hh
    exact hh
  change QuotientGroup.mk' (pCore 2 H) g ∈
    (MulAut.innerSubgroup (Source.starImage H K₀)).comap MulAut.conjNormal at hin
  rw [MulAut.conjNormal_comap_innerSubgroup, hcentral, sup_bot_eq] at hin
  exact hin

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.OriginalCorePlacement
