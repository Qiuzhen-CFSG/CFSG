module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ComponentRows
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFourLocal
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import Theory.GroupTheory.ResidualCentralQuotientImage
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.Mathieu.OrderFour

/-!
# Excluding the rank-two components in the Mathieu Hall argument

The literal residual maps to the component's central quotient with solvable
kernel and normalizes the nontrivial image of its own two-core. Its Mathieu
simple quotient has elements of order four and order divisible by three and
eleven. The linear parabolic sections have elementary two-subgroups; the
remaining Ree parabolic is three-free; and the PSU₅(4) parabolic orders and
the small derived endpoints are prime to eleven. These facts exclude every
relative-rank-two row without a fixed module order or a center-free cover.

The chosen-module consumer constructs the epimorphism from the original
inclusion-compatible two-core quotient. Its output preserves every component,
module and residual placement clause and identifies the remaining central
quotient as J₄. This is not the J₄ exclusion or residual uniqueness theorem.
Source: Aschbacher--Smith 4.4.11--12, printed pp.621--622, and the parabolics
in F.1.12, printed pp.262--264 (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.NormalizedRankOneOddControl
open ClassificationModels

/-- The actual Mathieu simple quotient has order divisible by three. -/
theorem mathieu_centralQuotient_three_dvd {Q : Type*} [Group Q]
    (hm : HasMathieuCentralQuotient Q) : 3 ∣ Nat.card (Q ⧸ center Q) := by
  rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m22_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order]; norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m24_order]; norm_num

/-- A cyclic subgroup of order four obstructs elementary two-subgroups. -/
theorem mathieu_centralQuotient_not_two_exponent {Q : Type*} [Group Q]
    (hm : HasMathieuCentralQuotient Q) :
    ¬ ∀ P : Subgroup (Q ⧸ center Q), IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  have hx : ∃ x : Q ⧸ center Q, orderOf x = 4 := by
    rcases hm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨x,hx⟩ := Sporadic.Mathieu.m12_exists_order_four
      exact ⟨e.symm x,(e.symm.orderOf_eq x).trans hx⟩
    · obtain ⟨x,hx⟩ := Sporadic.Mathieu.m22_exists_order_four
      exact ⟨e.symm x,(e.symm.orderOf_eq x).trans hx⟩
    · obtain ⟨x,hx⟩ := Sporadic.Mathieu.m23_exists_order_four
      exact ⟨e.symm x,(e.symm.orderOf_eq x).trans hx⟩
    · obtain ⟨x,hx⟩ := Sporadic.Mathieu.m24_exists_order_four
      exact ⟨e.symm x,(e.symm.orderOf_eq x).trans hx⟩
  obtain ⟨x,hx⟩ := hx
  intro h
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers,hx]; rfl)
  have hy : x ^ 2 = 1 := congrArg Subtype.val (h (zpowers x) hp ⟨x,mem_zpowers x⟩)
  have hd := orderOf_dvd_of_pow_eq_one hy
  rw [hx] at hd
  norm_num at hd

open BenderSuzuki.MatrixGroups
private theorem no_eleven_unitary_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    (h11 : 11 ∣ Nat.card S)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J hcard hconj hJ W hn hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
      else Theory.SpecificGroups.UnitaryFive.lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹ * r x *
      ((Theory.SpecificGroups.UnitaryFive.project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).injective
        (he.trans (map_one _).symm))) (inclusion_injective _)
  have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
  have hd11 := h11.trans hd
  cases b
  · rw [if_neg Bool.false_ne_true,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] at hd11
    norm_num at hd11
  · rw [if_pos rfl,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] at hd11
    norm_num at hd11

private theorem no_rankTwo_of_residual_module
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (h3 : 3 ∣ Nat.card S) (h11 : 11 ∣ Nat.card S)
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) :
    False := by
  let r0 := residualQuotientMap hFK (MulEquiv.refl (K ⧸ center K))
  let := residualQuotientMap_kernel_solvable hFK (MulEquiv.refl (K ⧸ center K))
  have hd : 11 ∣ Nat.card (K ⧸ center K) := h11.trans
    (SimpleSection.card_dvd_of_solvable_representation hS π hπ r0)
  cases hm with
  | linear hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcard,he] at hd
      norm_num at hd
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_linear_three_local hS hexp π hπ hn2 hcard _ hp hpne r hnorm
  | unitary_four hn hm =>
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two
      n (by omega) hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
      J n (by omega) hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_unitary_four_local hS hexp π hπ J.conj J.conj_involutive
      n (by omega) hcard hconj _ hp hpne r hnorm
  | unitary_five hn hm =>
    have hu : ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
      simpa only [hn,show 2 ^ 2 = 4 from rfl] using hm
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
    let : CharP E 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_eleven_unitary_five_local hS π hπ h11
      (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl _ hp hpne r hnorm
  | symplectic hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := E)).symm
    let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm a
    exact no_symplectic_four_local hS hexp π hπ _ hp hpne r hnorm
  | g2 hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hbig : 2 < Nat.card E := by
      rw [hcard]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_g2_local hS hexp π hπ hbig _ hp hpne r hnorm
  | triality hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_triality_local hS hexp π hπ n (show 0 < n from hn) _ hp hpne r hnorm
  | ree_f4 m hm _ he =>
    obtain ⟨e⟩ := he
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_ree_local_of_three_dvd hS hexp h3 π hπ hm _ hp hpne r hnorm
  | symplectic_derived _ he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (ClassicalGroup.PSp 2 (ZMod 2))).card_subgroup_dvd_card
    rw [← Nat.card_congr
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hd'
    norm_num at hd'
  | g2_derived _ he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | tits _ he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd


/-- A perfect residual with its original nonzero two-core commutator module
and Mathieu central quotient cannot lie in a rank-two component cover. -/
theorem no_rankTwo_of_mathieu_residual
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] [IsQuasisimple Q]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hm : HasMathieuCentralQuotient Q)
    (π : F →* (Q ⧸ center Q)) (hπ : Function.Surjective π)
    {n : ℕ} (hmodel : IsRankTwoModel (K ⧸ center K) n) : False := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Group.IsPerfect (Q ⧸ center Q) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  exact no_rankTwo_of_residual_module F K W hFK hWF hne hcomm
    (Group.IsPerfect.not_isSolvable _) (mathieu_centralQuotient_not_two_exponent hm)
    π hπ (mathieu_centralQuotient_three_dvd hm) (mathieu_centralQuotient_eleven_dvd hm) hmodel

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl

/-- The surviving moved-component configuration retains the original full
component, residual and module, now with its actual J₄ central quotient. -/
@[expose] def MathieuJankoComponentCase {G : Type*} [Group G]
    (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧
    ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal residual and its inclusion-induced quotient remove every
relative-rank-two component row, leaving the full J₄-cover configuration. -/
theorem sourceOrbit_mathieu_janko_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hc : MathieuComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent)) :
    MathieuJankoComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent) := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hmodel,hv,hf,hcent,hr,hsection⟩ := hc
  refine ⟨K,hK,hn,hKV,hout,hcore,?_,hv,hf,hcent,hr,hsection⟩
  rcases hmodel with ⟨n,hmK⟩ | hj
  · exfalso
    let : Finite D.orbitComponent :=
      Finite.of_surjective D.orbitComponentHom D.orbitComponentHom_surjective
    let := D.orbitComponent_quasisimple h
    let N := normalizer (A : Set G)
    let F := oddActorResidual L A
    let J := K.map N.subtype
    let : Group.IsPerfect F := oddActorResidual_isPerfect L A
    obtain ⟨hcover,he,hWF,_⟩ := chosen_oddActorResidual_cover h D A hAN hcomm ho hAV
    obtain ⟨q,_⟩ := exists_pCoreQuotientEquiv_of_cover
      (p := 2) (A := F) (L := L)
      ((oddActorResidual_le L A).trans inf_le_left) hcover.subset
    have hz : (center _).map q.toMonoidHom = center _ := by
      apply le_antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact (centerCongr q ⟨z,hz⟩).property
      · intro z hz
        exact ⟨q.symm z,(centerCongr q.symm ⟨z,hz⟩).property,q.apply_symm_apply z⟩
    let e := (QuotientGroup.congr _ _ q hz).trans (D.orbitCentralQuotientEquiv h)
    let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) := e.toMonoidHom.comp
      ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp (QuotientGroup.mk' (pCore 2 F)))
    have hπ : Function.Surjective π := e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    let a : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
    let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ a (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr a ⟨x,hx⟩).property
      · intro y hy
        exact ⟨a.symm y,(centerCongr a.symm ⟨y,hy⟩).property,a.apply_symm_apply y⟩)
    exact no_rankTwo_of_mathieu_residual F J V hf hWF D.ne_bot he hm π hπ
      (hmK.of_mulEquiv z)
  · exact hj

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
