module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LocalOrbit
public import Theory.SpecificGroups.SL2.EvenBorel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic.ShortOrder
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LinearIntrinsic.BorelOrder

/-!
# Intrinsic facts for binary linear Borels in E.6.8

The characteristic-two central quotient identifies SL₂ with PSL₂, proving
centerlessness. Its upper unipotents are self-centralizing and form the
two-core of their normalizer. Sylow conjugacy and the actual matrix
isomorphism transport characteristic two to the prescribed ambient Borel.

For odd field degree, every subgroup of a finite Borel power is excluded
from being short: the power is solvable and its order is prime to three.
For general degree, a subnormal subgroup's two-core embeds coordinatewise
in the abelian unipotent radicals. The short-group calculation then forces
order twelve. The independent matrix Borel calculation excludes that order
for subnormal subgroups of every finite Borel power when the field has order
at least eight. Excluding PSL₂(4) ensures this field-size bound, completing
the exclusion in every degree. Subnormality in the whole power is essential:
larger even-degree Borels can contain arbitrary A₄ subgroups.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259), with C.1.7–13, printed pp.123–125.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
open Matrix.ProjectiveSpecialLinearGroup
open CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- The prescribed ambient Borel is isomorphic to the actual projective matrix Borel. -/
noncomputable def linearSylowBorelEquiv
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : L ≃* PSL(2,F)) (S : Sylow 2 L) : sylowBorel S ≃* OddBorel.borel F := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn : (normalizer (S : Set L)).map e.toMonoidHom =
      normalizer (R : Set PSL(2,F)) :=
    map_normalizer_eq_of_bijective _ e.bijective
  let eb := ((normalizer (S : Set L)).equivMapOfInjective L.subtype L.subtype_injective).symm
  let ee := ((normalizer (S : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hn)
  exact eb.trans (ee.trans (EvenBorelResidual.sylowNormalizerEquiv F R))

omit [Finite G] in
/-- Binary PSL₂ is centerless, using the injective SL₂ central quotient. -/
theorem linear_center_eq_bot {n : ℕ} (_hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ n)) : center L = ⊥ := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let p : Matrix.SpecialLinearGroup (Fin 2) F ≃* PSL(2,F) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let a := e.trans p.symm
  apply (center L).eq_bot_iff_forall.mpr
  intro x hx
  have hm : a x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := a.surjective y
    exact (map_mul a z x).symm.trans
      ((congrArg a (mem_center_iff.mp hx z)).trans (map_mul a x z))
  have he : a x = 1 := by
    simpa only [BenderSuzuki.Converse.center_SL2_eq_bot, mem_bot] using hm
  exact a.injective (he.trans (map_one a).symm)

private theorem matrix_borel_characteristicTwo
    (F : Type*) [Field F] [Finite F] [CharP F 2] :
    HasCharacteristicTwo (OddBorel.borel F) := by
  have hc : HasCharacteristicTwo (Matrix.SpecialLinearGroup.rankOneBorel F) := by
    apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
    have he : (Matrix.SpecialLinearGroup.rankOneBorel F).pCoreIn 2 =
        Matrix.SpecialLinearGroup.upperUnipotent F :=
      twoCore_sylow_normalizer (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
    rw [he, Theory.SpecificGroups.SL2.EvenBorel.unipotent_centralizer]
    exact inf_le_right
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (EvenBorelResidual.rankOneBorelEquiv F)).mp hc

/-- The actual binary linear Sylow normalizer has characteristic two. -/
theorem linear_sylowBorel_characteristicTwo {n : ℕ} (_hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ n)) (S : Sylow 2 L) :
    HasCharacteristicTwo (sylowBorel S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (linearSylowBorelEquiv F e S)).mpr (matrix_borel_characteristicTwo F)

private theorem not_short_of_solvable_three_free {X : Type*} [Group X] [Finite X]
    [Group.IsSolvable X] (hthree : ¬ 3 ∣ Nat.card X) : ¬ ChapterC.IsShort X := by
  intro hx
  rcases hx.quotient with hq | hq
  · let _ := hq
    let _ : IsSimpleGroup ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) := IsQuasisimple.simple
    let _ : Nontrivial (X ⧸ pCore 2 X) :=
      (QuotientGroup.mk'_surjective (center (X ⧸ pCore 2 X))).nontrivial
    exact Group.IsPerfect.not_isSolvable (X ⧸ pCore 2 X) inferInstance
  · exact hthree (hq ▸ (pCore 2 X).card_quotient_dvd_card)

/-- In odd field degree every subgroup of every finite Borel power is non-short. -/
theorem linear_borel_power_noShort_of_odd {n : ℕ} (hn : 2 ≤ n)
    (iso : ClassicalGroup.IsPSL L 2 (2 ^ n)) (hodd : Odd n)
    (S : Sylow 2 L) (k : ℕ) (X : Subgroup (Fin k → sylowBorel S)) :
    ¬ ChapterC.IsShort X := by
  let _ := ((Model.linear hn iso).sylowFacts S).solvable
  let eb := (normalizer (S : Set L)).equivMapOfInjective L.subtype L.subtype_injective
  let _ : Group.IsSolvable (sylowBorel S) :=
    Group.isSolvable_of_isSolvable_injective (f := eb.symm.toMonoidHom) eb.symm.injective
  let _ := Group.isSolvable_finite_pi (fun _ : Fin k => sylowBorel S)
  have hthreeB : ¬ 3 ∣ Nat.card (sylowBorel S) := by
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    rw [Nat.card_congr (linearSylowBorelEquiv F e S).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (EvenBorelResidual.borel_threePrime_of_odd F hcard hodd)
  apply not_short_of_solvable_three_free
  intro hd
  have hp := hd.trans X.card_subgroup_dvd_card
  rw [Nat.card_fun] at hp
  exact hthreeB (Nat.prime_three.dvd_of_dvd_pow hp)

private theorem subnormal_power_core_commutative
    {B : Type*} [Group B] [Finite B] [IsMulCommutative (pCore 2 B)]
    (k : ℕ) (X : Subgroup (Fin k → B)) (hs : X.IsSubnormal) :
    IsMulCommutative (pCore 2 X) := by
  have hc := pCoreIn_le_of_subnormal 2 hs
  have hp (i : Fin k) : (pCore 2 (Fin k → B)).map
      (Pi.evalMonoidHom (fun _ : Fin k => B) i) ≤ pCore 2 B := by
    exact le_sSup ⟨(inferInstance : (pCore 2 (Fin k → B)).Normal).map _
      (fun b => ⟨fun _ => b, rfl⟩), pCore_isPGroup.map _⟩
  have hm (a : pCore 2 X) (i : Fin k) : a.val.val i ∈ pCore 2 B :=
    hp i (mem_map_of_mem _ (hc (mem_map_of_mem X.subtype a.property)))
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (mul_comm (⟨a.val.val i, hm a i⟩ : pCore 2 B)
    ⟨b.val.val i, hm b i⟩)

/-- Subnormality in the whole Borel power puts the two-core in its abelian radicals. -/
theorem linear_matrix_borel_power_core_commutative
    (F : Type*) [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n)
    (k : ℕ) (X : Subgroup (Fin k → OddBorel.borel F)) (hs : X.IsSubnormal) :
    IsMulCommutative (pCore 2 X) := by
  let _ : IsMulCommutative (pCore 2 (OddBorel.borel F)) := by
    rw [EvenBorelResidual.twoCore_eq_kernel F hcard]
    infer_instance
  exact subnormal_power_core_commutative k X hs

private theorem matrix_borel_solvable
    (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Group.IsSolvable (OddBorel.borel F) := by
  have he : Matrix.SpecialLinearGroup.rankOneBorel F = BenderSuzuki.Converse.Borel F := by
    ext g
    exact (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff g).trans
      (BenderSuzuki.Converse.mem_Borel_iff g).symm
  let _ : Group.IsSolvable (Matrix.SpecialLinearGroup.rankOneBorel F) := by
    rw [he]
    exact Linear.borel_solvable
  exact Group.isSolvable_of_surjective
    (f := (EvenBorelResidual.rankOneBorelEquiv F).toMonoidHom)
    (EvenBorelResidual.rankOneBorelEquiv F).surjective

/-- Conditional final reduction for the linear intrinsic exclusion. The two
numerical inputs are independent proof obligations, not Borel placement or
block-exclusion assumptions. The actual component and Borel equivalences
transport shortness and subnormality to the finite matrix model. -/
theorem linear_borel_power_noShort_of_order_inputs
    (hshortOrder : LinearShortOrderInput) (hborelOrder : LinearBorelOrderInput)
    {n : ℕ} (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (notFour : ¬ ClassicalGroup.IsPSL L 2 4)
    (S : Sylow 2 L) (k : ℕ) (X : Subgroup (Fin k → sylowBorel S))
    (hs : X.IsSubnormal) : ¬ ChapterC.IsShort X := by
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    exact notFour (by simpa only [hn2, show (2 : ℕ) ^ 2 = 4 by decide] using iso)
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let E := MulEquiv.piCongrRight (fun _ : Fin k => linearSylowBorelEquiv F e S)
  let Y := X.map E.toMonoidHom
  have hYs : Y.IsSubnormal := hs.map E.surjective
  let _ := matrix_borel_solvable F
  let _ := Group.isSolvable_finite_pi (fun _ : Fin k => OddBorel.borel F)
  let _ := linear_matrix_borel_power_core_commutative F hcard k Y hYs
  intro hx
  have hY : ChapterC.IsShort Y := hx.of_mulEquiv (E.subgroupMap X)
  exact hborelOrder F n hn3 hcard k Y hYs (hshortOrder Y hY)

/-- Every subnormal subgroup of a finite power of the actual binary linear
Borel is non-short, apart from the excluded PSL₂(4) branch. Both numerical
inputs are discharged by the short-group and matrix Borel calculations. -/
theorem linear_borel_power_noShort
    {n : ℕ} (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (notFour : ¬ ClassicalGroup.IsPSL L 2 4)
    (S : Sylow 2 L) (k : ℕ) (X : Subgroup (Fin k → sylowBorel S))
    (hs : X.IsSubnormal) : ¬ ChapterC.IsShort X :=
  linear_borel_power_noShort_of_order_inputs linearShortOrderInput linearBorelOrderInput
    hn iso notFour S k X hs

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
