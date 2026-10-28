module
public import Theory.GroupTheory.ComponentPairRankDescent
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitCoordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitModels

/-!
# Rank at three in the original component-pair action quotient

The actual plus components contain a disjoint elementary plane of order nine.
It lies in the image of K joined with T_v, where the quotient map already
has two-group kernel. Lift that plane into the original actor. Ambient
three-rank at most two makes the full plus kernel three-prime by the
normalized-disjoint-plane argument. Rank at three consequently descends to
the plus quotient. No full SQTK assertion about that quotient is used.

Source: Aschbacher--Smith, 13.6.14 and its invocation of 1.2.2(a), printed
pp.929 and504; the elementary kernel argument is A.1.27, p.26.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual plus kernel has order prime to three. Its restricted
component-Sylow join kernel and the source rank bound suffice. -/
theorem plusMk_ker_coprime_three_of_pair
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hd : 3 ∣ Nat.card (plusImage K L T z v hL hz K)) :
    Nat.Coprime 3 (Nat.card (plusMk K L T z v hL hz).ker) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t,ht,htN,hpair,hdis,e,he⟩ := exists_plus_pair_coordinates_source
    K L T z v hlocal hL hz hSylow hK hn
  let A := plusActor K L T v
  let f := plusMk K L T z v hL hz
  let B := plusImage K L T z v hL hz K
  let C := plusImage K L T z v hL hz (K.conjBy t)
  let tA : A := ⟨t,(show Tv T v ≤ A from le_sup_right) ht⟩
  have hC : C = B.conjBy (f tA) :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  have hdc : 3 ∣ Nat.card C := by
    rw [hC]
    change 3 ∣ Nat.card (B.map (MulAut.conj (f tA)).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj (f tA)).injective]
    exact hd
  have hBcomp : IsComponent (Gplus K L T z v hL hz) B :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hCcomp : IsComponent (Gplus K L T z v hL hz) C := hC.symm ▸ hBcomp.map_conj (f tA)
  have hne : B ≠ C := plusImage_pair_ne_source K L T z v hlocal hL hz hK hn t ht htN
  obtain ⟨E,hE,hcard,hEB⟩ := ComponentPairRankDescent.exists_plane_in_pair B C hdis
    (commutator_eq_bot_iff_le_centralizer.mp (hBcomp.commutator_eq_bot_of_ne hCcomp hne)) hd hdc
  let := hE
  let J₀ := K ⊔ Tv T v
  have hJA : J₀ ≤ A := sup_le (K_le_plusActor K L T v) le_sup_right
  let J := J₀.subgroupOf A
  let j : J ≃* J₀ := subgroupOfEquivOfLe hJA
  let r := f.comp J.subtype
  have hr_eq : r = (joinPlusMap K L T z v hL hz).comp j.toMonoidHom := rfl
  have htwo : IsPGroup 2 r.ker := by
    have htwo₀ := joinPlusMap_ker_isTwoGroup_source K L T z v hlocal hL hz hK hn
    let q : r.ker →* (joinPlusMap K L T z v hL hz).ker :=
      (j.toMonoidHom.comp r.ker.subtype).codRestrict _ (fun x => x.property)
    apply htwo₀.of_injective q
    intro x y hh
    apply Subtype.ext
    exact j.injective (congrArg Subtype.val hh)
  have hcop : Nat.Coprime 3 (Nat.card r.ker) := by
    obtain ⟨n,hn⟩ := htwo.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hKmJ : Kminus K T v ≤ J₀ :=
    conjugateSpanBy_le le_sup_left ((show Tv T v ≤ J₀ from le_sup_right).trans J₀.le_normalizer)
  have hpairrange : B ⊔ C ≤ r.range := by
    have hKmA : Kminus K T v ≤ A := le_sup_left.trans le_sup_left
    have hCtA : K.conjBy t ≤ A := (le_sup_right.trans hpair.ge).trans hKmA
    have hBC : B ⊔ C = plusImage K L T z v hL hz (Kminus K T v) := by
      rw [hpair,plusImage,subgroupOf_sup (K_le_plusActor K L T v) hCtA,Subgroup.map_sup]
      rfl
    rw [hBC]
    rintro x ⟨a,ha,rfl⟩
    exact ⟨⟨a,hKmJ ha⟩,rfl⟩
  have hEr : E ≤ r.range := hEB.trans hpairrange
  let P := E.subgroupOf r.range
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.subgroupOf hEr
  have hPc : Nat.card P = 3^2 := (Nat.card_congr (subgroupOfEquivOfLe hEr).toEquiv).trans hcard
  have hAr : primeRank 3 A ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (plusActor_le_Gv K L T v hK.1.1))
      (inclusion_injective _)).trans (hlocal.stronglyQuasithin 3 (by decide) (by decide))
  exact ComponentPairRankDescent.coprime_ker_of_plane_in_restricted_range f J hAr hcop P hPc

/-- Rank at three descends to the actual plus quotient via the proved
three-prime kernel. No full SQTK property of that quotient is assumed. -/
theorem plus_primeRank_three_le_two_of_pair
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hd : 3 ∣ Nat.card (plusImage K L T z v hL hz K)) :
    primeRank 3 (Gplus K L T z v hL hz) ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hker := plusMk_ker_coprime_three_of_pair K L T z v hlocal hL hz hSylow hK hn hd
  have hke : (plusMk K L T z v hL hz).ker = (plusConjugation K L T z v hL hz).ker := by
    ext x
    exact QuotientGroup.eq_one_iff x
  rw [hke] at hker
  have hr := primeRank_quotient_le_of_coprime 3 (plusConjugation K L T z v hL hz).ker hker
  exact hr.trans ((Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (plusActor_le_Gv K L T v hK.1.1))
    (inclusion_injective _)).trans (hlocal.stronglyQuasithin 3 (by decide) (by decide)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
