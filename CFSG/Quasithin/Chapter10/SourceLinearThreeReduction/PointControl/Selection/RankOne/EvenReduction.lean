module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.OddFixedLayer
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The remaining even-degree rank-one fixed-layer case

Odd-degree natural coordinates fix both original moved kernels, so they
supply all three rank-one point-geometry clauses and the actual point-Sylow
control. A zero kernel also gives the fixed-layer clause directly. Degree
two is excluded by the genuine SL₂(4) = A₅ quotient isomorphism.

Thus the rank-one assembly retains only even field degree at least four
with a positive fixed kernel. This remaining ambient fixed-layer assertion
is not inferred from the natural cover. Its proof remains with
qt-d-10-nona5-point-selection, as does the selected-module classification.
Source: Aschbacher--Smith, 10.1.1(1) and10.2.9, printed pp.741 and750.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A natural quotient over a specified odd-degree field discharges the entire
rank-one geometry, with the original exchanger and full fixed kernel. -/
theorem point_geometry_of_odd_degree
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (n : ℕ) (hn : 1 < n) (hodd : Odd n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (c : letI : NeZero n := ⟨by omega⟩
      letI : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
      Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    RankOnePointGeometry D t := by
  let : NeZero n := ⟨by omega⟩
  have hm : RankOneNatural D := ⟨n,hn,e,⟨c⟩⟩
  exact point_geometry_of_fixed_layer D hnotA5 hm ht htn
    (fixed_layer_centralizes_half_sylow_of_odd_degree D e c hodd
      (GaloisField.card 2 n (by omega)) ht htn hcross)

/-- Actual point control for the odd-degree rank-one family, including every
initially component-fixed point. Half-Sylow uniqueness is the permitted input. -/
theorem pointSylowControl_of_odd_degree
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (n : ℕ) (hn : 1 < n) (hodd : Odd n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (c : letI : NeZero n := ⟨by omega⟩
      letI : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
      Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t := by
  have hg := point_geometry_of_odd_degree D hnotA5 n hn hodd e c ht htn hcross
  exact pointSylowControl_of_baumann_orbits D hhalf hg.fixed_layer ht htn hcross
    hg.baumann_normalizer hg.fixed_orbits

/-- For any marked rank-one field, a trivial moved kernel gives the full
fixed-layer assertion without an assertion about field automorphisms. -/
theorem fixed_layer_eq_bot_of_zero_kernel
    (hzero : sourceMovedFixed D = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  rw [BinaryThree.fixed_layer_eq_moved_kernels D ht htn hcross,hzero,Subgroup.map_bot,sup_bot_eq]

omit D in
/-- Only the even-degree positive-kernel branch remains for the rank-one
geometry. Every original source hypothesis is retained explicitly. -/
def EvenPositiveFixedLayerAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (n : ℕ) (hn : 4 ≤ n), Even n →
      letI : NeZero n := ⟨by omega⟩
      letI : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
      ∀ (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)),
        Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
          (Representation.SL2.BinarySmall.natural.comp
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) →
        sourceMovedFixed D ≠ ⊥ →
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
        ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
          (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
          HalfSylowUnique D →
          D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
            centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)

omit D in
/-- The old full rank-one fixed-layer interface reduces to its even-degree,
positive-kernel cases; no point or quotient has been replaced. -/
theorem fixedLayerAt_of_even_positive (heven : EvenPositiveFixedLayerAt T) :
    FixedLayerAt T := by
  intro hmany L D hmin hfull hna hm hJ t ht htn hcross hhalf
  by_cases hzero : sourceMovedFixed D = ⊥
  · rw [fixed_layer_eq_bot_of_zero_kernel D hzero ht htn hcross]
    exact bot_le
  obtain ⟨n,hn,e,⟨c⟩⟩ := hm
  let : NeZero n := ⟨by omega⟩
  by_cases ho : Odd n
  · exact fixed_layer_centralizes_half_sylow_of_odd_degree D e c ho
      (GaloisField.card 2 n (by omega)) ht htn hcross
  have he : Even n := Nat.not_odd_iff_even.mp ho
  have hn2 : n ≠ 2 := by
    intro hn2
    subst n
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact hna ⟨(e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2))).trans a⟩
  have hn4 : 4 ≤ n := by obtain ⟨k,hk⟩ := he; omega
  exact heven hmany L D hmin hfull hna n hn4 he e c hzero hJ t ht htn hcross hhalf

omit D in
/-- All rank-one point geometry follows once its remaining even positive
central-kernel input is discharged by this task's assembly. -/
theorem rankOneGeometryAt_of_even_positive (heven : EvenPositiveFixedLayerAt T) :
    RankOneGeometryAt T :=
  rankOneGeometryAt_of_fixed_layer (fixedLayerAt_of_even_positive heven)

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
