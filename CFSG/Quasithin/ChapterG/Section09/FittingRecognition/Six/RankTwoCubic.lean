module
public import Theory.Representation.NormalNineDegreeSix
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.SupercriticalSmallRank
public import CFSG.Quasithin.ChapterA.Section01.PStructure.RankTwo
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Source

/-!
# A normal cubic in the rank-two three-core branch

Choose a characteristic supercritical subgroup of the actual three-core.
The rank-two source theorem makes it an elementary nine-group or an
extraspecial group of order 27. In the former case the degree-six fixed-space
argument supplies a normal cubic; in the latter its characteristic center
does. The final theorem applies this to the actual G.9 Fitting hypothesis.

Source: Aschbacher--Smith G.9.4, printed p.355, using A.1.24--25.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The degree-six rank-two core has an ambient-normal cubic subgroup. -/
theorem normal_cubic_of_three_rank_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    [Representation.IsIrreducible ρ] (hd : finrank (ZMod 2) V = 6)
    (hr : primeRank 3 (pCore 3 G) = 2) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let B := pCore 3 G
  have hB : IsPGroup 3 B := pCore_isPGroup
  obtain ⟨R,hR⟩ := hB.exists_supercriticalPSubgroup (by decide)
  let : R.Characteristic := hR.characteristic
  have hRrank : primeRank 3 R = 2 :=
    (hR.primeRank_eq_of_le_two hB (by decide) hr.le).trans hr
  have hRexp : Monoid.exponent R = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hR.exponent_dvd_p with he | he
    · let : Subsingleton R := Monoid.exp_eq_one_iff.mp he
      have hz : primeRank 3 R ≤ 0 :=
        (primeRank_le_iff_elementary_card_le R).mpr (fun E _ => by simp)
      omega
    · exact he
  rcases ChapterA.rankTwo_models (by decide : 3 ≠ 2) (hB.to_subgroup R)
      hRexp hRrank hR.derived_le_center with ⟨hc,_⟩ | ⟨_,hex,_⟩
  · let : IsElementaryAbelian 3 R := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
      exponent_dvd_p := hR.exponent_dvd_p }
    let N := R.map B.subtype
    let : N.Normal := ConjAct.normal_of_characteristic_of_normal
    let : IsElementaryAbelian 3 N := IsElementaryAbelian.map B.subtype
    have hN : Nat.card N = 9 := (card_map_of_injective B.subtype_injective).trans hc
    obtain ⟨C,_,hCn,hCc⟩ :=
      Representation.NormalNineDegreeSix.exists_normal_cubic_of_irreducible ρ hf N hN hd
    exact ⟨C,hCn,hCc⟩
  · let : IsExtraspecial 3 R := hex
    let C₀ := (center R).map R.subtype
    let : C₀.Characteristic := inferInstance
    let C := C₀.map B.subtype
    have hCn : C.Normal := ConjAct.normal_of_characteristic_of_normal
    have hCc : Nat.card C = 3 := by
      rw [card_map_of_injective B.subtype_injective,card_map_of_injective R.subtype_injective]
      exact IsExtraspecial.center_order_p 3 R
    exact ⟨C,hCn,hCc⟩

/-- Actual cubic Fitting data discharge the lower rank bound, leaving only
the source exclusion of three-rank greater than two. -/
theorem normal_cubic_of_source_three_rank_le_two
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup G,A⁆ : Subgroup G))
    (hd : finrank (ZMod 2) V = 6) (hr : primeRank 3 (pCore 3 G) ≤ 2) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let := h.irreducible
  have hlow := (threeCoreData_from_source h (by decide) hc).core_rank_ge
  exact normal_cubic_of_three_rank_two ρ h.faithful hd (by omega)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six
