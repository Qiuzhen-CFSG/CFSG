module
public import Theory.GroupTheory.OddRadicalConjugatePair
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
/-!
# The SL₂(5) odd-radical pair

This is the actual finite-field specialization of the quasisimple conjugate
pair construction. It retains the specified SL₂ model and the literal pair
inside the ambient group. The pair has trivial two-core and noncentral
Fitting subgroup, and its solvable-radical quotient is nonabelian simple.
No splitting or classification of that pair is assumed.

Source: Aschbacher--Smith C.5.12, printed p.163, the A.3.12(21) branch.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.OddRadicalConjugatePair
variable {G : Type*} [Group G] [Finite G]


/-- The original SL₂(5) pair, over any field with five elements. -/
theorem exists_sl2_five_pair
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F=5)
    (N B : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hn : Odd (Nat.card N)) (hself : centralizer (N : Set G) ≤ N)
    (hBN : B ⊓ N=⊥) (e : B ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ g∈N,
      let E := B ⊔ B.map (MulAut.conj g).toMonoidHom
      pCore 2 E=⊥ ∧ Group.IsPerfect E ∧ (⊤ : Subgroup E).IsCComponent ∧
        IsSimpleGroup (E ⧸ solvableRadical E) ∧
        ¬ IsMulCommutative (E ⧸ solvableRadical E) ∧
        ¬ fittingSubgroup E ≤ center E := by
  have hlarge : 3 < Nat.card F := by omega
  let : IsQuasisimple B := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  have hc : Nat.card (center B)=2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (GorensteinWalter.sl2ProjectiveProjection_ker F) ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card F (hF ▸ (by decide : Odd 5))
  obtain ⟨g,hg,hcore,hperfect,hcomp,hfit⟩ := exists_pair_of_quasisimple_center_two N B hn hself hBN hc
  let E := B ⊔ B.map (MulAut.conj g).toMonoidHom
  let : Group.IsPerfect E := hperfect
  let : IsSimpleGroup ((⊤ : Subgroup E) ⧸ solvableRadical (⊤ : Subgroup E)) :=
    hcomp.isSimpleGroup_quotient_solvableRadical
  let er : ((⊤ : Subgroup E) ⧸ solvableRadical (⊤ : Subgroup E)) ≃*
      (E ⧸ solvableRadical E) :=
    QuotientGroup.congr _ _ topEquiv (map_solvableRadical_equiv topEquiv)
  let : IsSimpleGroup (E ⧸ solvableRadical E) := er.symm.isSimpleGroup
  exact ⟨g,hg,hcore,hperfect,hcomp,inferInstance,Group.IsPerfect.not_isMulCommutative _,hfit⟩

/-- Odd nilpotence discharges the intersection premise for the actual SL₂(5) pair. -/
theorem exists_sl2_five_pair_of_odd_nilpotent
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F=5)
    (N B : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hn : Odd (Nat.card N)) (hself : centralizer (N : Set G) ≤ N)
    (e : B ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ g∈N,
      let E := B ⊔ B.map (MulAut.conj g).toMonoidHom
      pCore 2 E=⊥ ∧ Group.IsPerfect E ∧ (⊤ : Subgroup E).IsCComponent ∧
        IsSimpleGroup (E ⧸ solvableRadical E) ∧
        ¬ IsMulCommutative (E ⧸ solvableRadical E) ∧
        ¬ fittingSubgroup E ≤ center E := by
  have hlarge : 3 < Nat.card F := by omega
  let : IsQuasisimple B := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  have hc : Nat.card (center B)=2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (GorensteinWalter.sl2ProjectiveProjection_ker F) ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card F (hF ▸ (by decide : Odd 5))
  let K := N.subgroupOf B
  let j : K →* N := B.subtype.subgroupComap N
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun n : N => (n : G)) he))
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hj
  have hKC : K ≤ center B :=
    (le_solvableRadical K inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hBN : B ⊓ N = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hxB,hxN⟩
    let b : B := ⟨x,hxB⟩
    have hbC : b ∈ center B := hKC hxN
    have hd : orderOf b ∣ 2 := hc ▸ orderOf_dvd_natCard (center B) hbC
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    · have hodd := hn.of_dvd_nat (orderOf_dvd_natCard N hxN)
      have hx2 : orderOf x=2 := (Subgroup.orderOf_coe b).trans h2
      rw [hx2] at hodd
      exact (by norm_num at hodd)
  exact exists_sl2_five_pair hF N B hn hself hBN e

end Theory.GroupTheory.OddRadicalConjugatePair
