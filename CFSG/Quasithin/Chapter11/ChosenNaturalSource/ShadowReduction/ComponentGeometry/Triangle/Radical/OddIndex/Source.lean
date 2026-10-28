module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Intrinsic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Outer

/-!
# The exact odd-extension index on the original chosen flag

The actual point normalizer supplies SQTK to its relative component K.
Thus the source's two-odd SL₂ quotient gives the literal two-Fitting
quotient without a separate nilpotent-kernel or elementary-kernel premise.
The original R₁ is Sylow in O∞(KT). Restriction to K and the index product
formula give the exact identity

  [O∞(KT) : O₂,F(KT)] = 2 [R₁ : R₁ intersect (K O₂(KT))].

Consequently the bound by two is equivalent to R₁ ≤ K O₂(KT). The last
application derives both radical bounds from this containment on the
unchanged flag, with no assumption that X normalizes T.

The containment is an outstanding geometric obligation of
qt-d-1222-shadow-component-triangle. The conditional application is not
a proof of 11.4.1(3); qt-d-1222-shadow-components retains the registered
earlier source inputs and final component assembly.
Source: Aschbacher–Smith A.3.6, pp.43–45; 11.1.2(1), p.761;
11.4.1(3), printed pp.775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The original two-local point normalizer discharges the intrinsic SQTK premise. -/
theorem ofFlag_twoFitting_model_of_twoOdd_sl2 (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K : Subgroup G) (hK : Source.ComponentIn (centralizer (f.Vi 0 : Set G)) K)
    {p : ℕ} (hp : 3 < p) (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    Source.IsSL (K ⧸ twoFittingCore K) 2 p := by
  have hs := S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)
  have hC := Subgroup.centralizer_le_normalizer (f.Vi 0 : Set G)
  have hc : IsSQTK KnownSimple.IsKnownSimple (centralizer (f.Vi 0 : Set G)) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hC)).mp
      (hs.subgroup ((centralizer (f.Vi 0 : Set G)).subgroupOf (normalizer (f.Vi 0 : Set G))))
  exact relative_twoFitting_model_of_twoOdd_sl2 hc hK hp hm

/-- The exact index formula retains the original R₁, K, T and both literal cores. -/
theorem ofFlag_fitting_index_eq_two_mul_outer_index (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hn : S.field.degree = 2) {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) =
      2 * (K ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (ofFlag S f X z H).R₁ := by
  have hp' : p.Prime ∧ 3 < p := by
    rcases hp with rfl | ⟨hp,hl⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨hp,by omega⟩
  have hm' := ofFlag_twoFitting_model_of_twoOdd_sl2 S f K hK.1 hp'.2 hm
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let R := (ofFlag S f X z H).R₁
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans (sup_le_sup_right hAK _)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let e : B ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hF : (twoFittingCore B).map e.toMonoidHom = twoFittingCore K := by
    refine le_antisymm (twoFittingCore_map_equiv_le e) ?_
    intro k hk
    exact ⟨e.symm k, twoFittingCore_map_equiv_le e.symm
      (mem_map_of_mem e.symm.toMonoidHom hk), e.apply_symm_apply k⟩
  have hi : (twoFittingCore B).relIndex (solvableRadical B) = 2 := by
    have he := relIndex_map_map_of_injective (f := e.toMonoidHom)
      (twoFittingCore B) (solvableRadical B) e.injective
    rw [hF,map_solvableRadical_equiv e] at he
    exact he.symm.trans (fitting_index_two_of_sl2 hp'.2
      (hp'.1.odd_of_ne_two (by omega)) hm')
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right), subgroupOf_self])
  have hs : Chapter1.IsSylowIn 2 (R.subgroupOf J) (solvableRadical J) := by
    apply (Chapter1.IsSylowIn.map_iff J.subtype J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRJ]
    exact ofFlag_surviving_sylow_radical S f X z H K hK hAK hTK
      (.sl2Prime rfl hn p hp hm)
  rw [fitting_index_eq_sylow_core_index (R.subgroupOf J) hs
    (radical_fitting_quotient_isTwoGroup B hq hi),
    radical_core_index_factor B (R.subgroupOf J) hs hi]
  congr 1
  have he := relIndex_map_map_of_injective (f := J.subtype)
    (B ⊔ pCore 2 J) (R.subgroupOf J) J.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left),
    map_subgroupOf_eq_of_le hRJ] at he
  exact he.symm

/-- The missing numerical bound is precisely the original radical covering condition. -/
theorem ofFlag_fitting_index_le_two_iff_core_cover (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hn : S.field.degree = 2) {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2 ↔
      (ofFlag S f X z H).R₁ ≤ K ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [ofFlag_fitting_index_eq_two_mul_outer_index S f X z H K hK hAK hTK hn hp hm]
  have hi : 0 < (K ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (ofFlag S f X z H).R₁ :=
    Nat.pos_of_ne_zero ((K ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (ofFlag S f X z H).R₁).index_ne_zero_of_finite
  constructor
  · intro h
    apply relIndex_eq_one.mp
    omega
  · intro h
    rw [relIndex_eq_one.mpr h]

/-- Apply the index calculation to the original Cartan commutator consumer.
The core-cover premise remains with the triangle assembly owner. -/
theorem ofFlag_odd_extension_bounds_of_core_cover (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G)) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hn : S.field.degree = 2) {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p)
    (hcover : (ofFlag S f X z H).R₁ ≤ K ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2) :
    (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z H).R₁, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hs := ofFlag_surviving_sylow_radical S f X z H K hK hAK hTK
    (.sl2Prime rfl hn p hp hm)
  have hR := (Chapter1.isSylowIn_iff.mp hs).2.1
  exact ⟨hR,ofFlag_commutator_of_radical_fitting_index S f X z H K hAK hTK hXK hXR hR
    ((ofFlag_fitting_index_le_two_iff_core_cover S f X z H K hK hAK hTK hn hp hm).mpr hcover)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
