module

public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.SmallModels
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.FiveDelta
public import CFSG.Quasithin.Chapter2.Section04.Statement
public import CFSG.Quasithin.Chapter1.Defs
public import GorensteinWalter.LinearThreeEquiv
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Stellmacher.MainDefs

/-!
# Small Sylow recognition in the single A₃-block branch

The dihedral and semidihedral alternatives of the earlier source I.4.3
retain their actual group models. Simplicity discharges its no-index-two
hypothesis and QTKE supplies even characteristic. The literal δ and unique
maximal-two-local geometry exclude PSL₂(5), PSL₂(7), and A₆; solvability
excludes PSL₂(3). The remaining models are exactly Theorem 2.4.1's list.

This proves the recognition deduction in the S₄ paragraph of 2.4.26,
Aschbacher–Smith, printed p.543. The earlier universal I.4.3 implication is
explicit. The C.6.1 construction of the Sylow alternatives, the C₂ × S₄
fusion argument, and the A₅-shadow argument of 2.4.25–29 remain separate
source obligations; no assertion of that full family is made here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.SmallBlocks
variable {G : Type*} [Group G] [Finite G]

/-- The two complete earlier I.4.3 implications, including both Sylow
families and the actual model isomorphisms. -/
structure EarlierSmallSylowSource (G : Type*) [Group G] [Finite G] : Prop where
  dihedral : (∀ N : Subgroup G, N.index ≠ 2) → IsEvenCharacteristic G →
    ∀ T : Sylow 2 G, Stellmacher.IsDihedralGroup T →
      Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL G 2 p
  semidihedral : (∀ N : Subgroup G, N.index ≠ 2) → IsEvenCharacteristic G →
    ∀ T : Sylow 2 G, Stellmacher.IsSemidihedralGroup T →
      ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11)

private theorem simple_no_index_two {K : GroupClass} (hG : IsSimpleQTKE K G) :
    ∀ N : Subgroup G, N.index ≠ 2 := by
  let := hG.simple
  intro N hi
  have hn := N.normal_of_index_eq_two hi
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hc : Nat.card G = 2 := by simpa only [hb, index_bot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hG.nonabelian inferInstance
  · simp [ht] at hi

private theorem not_psl2_three {K : GroupClass} (hG : IsSimpleQTKE K G) :
    ¬ ClassicalGroup.IsPSL G 2 3 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let := hG.simple
  let : Fintype F := Fintype.ofFinite F
  let ef : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let ea : G ≃* alternatingGroup (Fin 4) := e.trans
    ((GorensteinWalter.psl2RingEquiv ef).symm.trans
      GorensteinWalter.psl2_three_equiv_alternatingGroup)
  let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
    alternatingGroup_fin_four_isSolvable
  have hs : Group.IsSolvable G :=
    Group.isSolvable_of_isSolvable_injective (f := ea.toMonoidHom) ea.injective
  exact hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))

private theorem fermatMersenne_three_le {p : ℕ} (hp : IsFermatOrMersennePrime p) :
    3 ≤ p := by
  have hne : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
      omega
    · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
      omega
  have := hp.1.two_le
  omega

/-- The exact classification conclusion in the dihedral or semidihedral
case of 2.4.26. The three exceptional exclusions are proved on the actual
models; the sole recognition premise is the complete earlier I.4.3 input. -/
theorem source_small_sylow_recognition {K : GroupClass} (hG : IsSimpleQTKE K G)
    (source : EarlierSmallSylowSource G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hSylow : Stellmacher.IsDihedralGroup T ∨ Stellmacher.IsSemidihedralGroup T) :
    IsTheorem241Model G := by
  have hno := simple_no_index_two hG
  obtain ⟨h7, h6⟩ := source_small_rank_two_exclusions hG T M hM hu
  rcases hSylow with hd | hs
  · rcases source.dihedral hno hG.evenCharacteristic T hd with ha | ⟨p, hp, he⟩
    · exact (h6 ha).elim
    have hlarge : 7 < p := by
      by_contra hn
      have hlo := fermatMersenne_three_le hp
      have hprime := hp.1
      interval_cases p
      · exact not_psl2_three hG he
      · norm_num at hprime
      · exact not_psl2_five_of_delta_nonempty _ M hM hdelta he
      · norm_num at hprime
      · exact h7 he
    exact Or.inl ⟨p, hp, hlarge, he⟩
  · exact Or.inr (source.semidihedral hno hG.evenCharacteristic T hs)

end CFSG.Quasithin.Chapter2.SmallBlocks
