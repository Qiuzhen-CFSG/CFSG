module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.SpecificGroups.SL2.BinaryThreeSection

/-!
# Excluding ordinary binary symplectic-four components

The literal perfect residual of the original doubled witness has a binary
SL₃(2) quotient with a two-group kernel. If the ordinary component quotient is
PSp₄(2ⁿ), its image normalizes the nontrivial radical intersection. The
symplectic two-local cover conjugates that normalizer into a point or plane
parabolic; perfectness moves the residual image into the determinant kernel,
whose quotient is SL₂. The binary-three section obstruction then gives a
contradiction.

Source: Aschbacher--Smith C.3.5, printed p.150, and the symplectic local
normalizer calculation used in C.4.5--7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original ordinary component cannot have central quotient PSp₄(2ⁿ),
for any n ≥ 2. All source maps and the full component center remain literal. -/
theorem sourceOrbit_binary_witness_ordinary_not_sp4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (_hn : 2 ≤ n) : ¬ ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n) := by
  rintro ⟨E,_,_,hE,⟨eE⟩⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := EvenProjective.charTwo_of_card hE
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let X := (LH.subgroupOf H).subgroupOf K
  let R := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
  let qK := QuotientGroup.mk' (center K)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLK : LH.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  let eX : X ≃* LH := (subgroupOfEquivOfLe hLK).trans
    (subgroupOfEquivOfLe (hc.component_le.trans hc.local_le))
  have hnormLH := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hnormLH) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := eX.symm.toMonoidHom) eX.symm.surjective
  obtain ⟨_,_,_,_,_,_,e,_,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let eQ : (X ⧸ pCore 2 X) ≃* BinaryLinearThree.Group :=
    (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).trans e
  let π := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hπ : Function.Surjective π := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  let eSp := eE.trans (EvenProjective.equiv (F := E)).symm
  let f0 := eSp.toMonoidHom.comp (qK.comp X.subtype)
  have hker0 : IsPGroup 2 f0.ker := by
    have he : f0.ker = (qK.comp X.subtype).ker :=
      MonoidHom.ker_comp_of_injective _ _ eSp.injective
    rw [he]
    exact pCore_isPGroup.to_le
      (DoubledBinaryOddPlacement.central_kernel_le_twoCore eQ X.subtype X.subtype_injective)
  have hl := hc.ordinary_quotient_local_data K hK
  rw [hspan] at hl
  let P := (R.map qK).map eSp.toMonoidHom
  have hP : IsPGroup 2 P := hl.2.1.map eSp.toMonoidHom
  have hPne : P ≠ ⊥ := fun he => hl.2.2.1
    ((map_eq_bot_iff_of_injective _ eSp.injective).mp he)
  have hnorm : f0.range ≤ normalizer (P : Set (Sp E)) := by
    have hh := (map_mono (f := eSp.toMonoidHom) hl.2.2.2.1).trans
      ((R.map qK).le_normalizer_map eSp.toMonoidHom)
    simpa only [f0,MonoidHom.range_comp,range_subtype] using hh
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (normalizer (P : Set (Theory.SpecificGroups.SymplecticFour.Sp E)))
    ⟨P,hPne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp f0
  have hj : IsPGroup 2 j.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective]
    exact hker0
  have hjP : j.range ≤ (normalizer (P : Set (Theory.SpecificGroups.SymplecticFour.Sp E))).map
      (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hnorm ⟨x,rfl⟩)
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hpt | hpl
  · have him : j.range ≤ pointLocal :=
      (le_map_solvableResidual_of_isPerfect _ _ (hjP.trans hpt)).trans
        pointParabolic_solvableResidual_le
    let a : X →* pointLocal (F := E) := j.codRestrict _ (fun x => him ⟨x,rfl⟩)
    have ha : IsPGroup 2 a.ker := by
      have he : a.ker = j.ker := MonoidHom.ker_codRestrict _ _ _
      rwa [he]
    let r := pointQuotient (F := E)
    have hr : IsPGroup 2 r.ker := by
      rw [pointQuotient_ker]
      exact IsElementaryAbelian.isPGroup 2 _
    apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_kernel π hπ (r.comp a)
    change IsPGroup 2 (r.ker.comap a)
    exact hr.comap_of_ker_isPGroup a ha
  · have him : j.range ≤ planeLocal :=
      (le_map_solvableResidual_of_isPerfect _ _ (hjP.trans hpl)).trans
        planeParabolic_solvableResidual_le
    let a : X →* planeLocal (F := E) := j.codRestrict _ (fun x => him ⟨x,rfl⟩)
    have ha : IsPGroup 2 a.ker := by
      have he : a.ker = j.ker := MonoidHom.ker_codRestrict _ _ _
      rwa [he]
    let r := Plane.quotientMap (F := E)
    have hr : IsPGroup 2 r.ker := by
      rw [Plane.quotientMap_ker]
      exact IsElementaryAbelian.isPGroup 2 _
    apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_kernel π hπ (r.comp a)
    change IsPGroup 2 (r.ker.comap a)
    exact hr.comap_of_ker_isPGroup a ha

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
