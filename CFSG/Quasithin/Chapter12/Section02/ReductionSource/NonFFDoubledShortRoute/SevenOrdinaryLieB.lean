module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryLie
-- Internal continuation: reuse the private A7 order-four obstruction.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryLie
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal
public import Theory.SpecificGroups.SymplecticSix.LocalOrder
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.SpecificGroups.SymplecticSix.FieldTransport

/-!
# The remaining Theorem B Lie rows for the actual alternating-seven residual

The extra unitary-four row has binary SL₂ Levi factors, already excluded by
the order-four element of A₇. Both full PSU₅(4) parabolics have order prime
to seven. Every actual binary Sp₆ two-local has order not divisible by 35.
The actual residual map into the component central quotient has solvable
kernel, so its A₇ quotient survives in the indicated local section in every
case. No rank bound or auxiliary local-placement premise is supplied.
Source: Aschbacher–Smith A.2.2, F.1.12 and 4.4.12, printed pp.33,262–264,622,
applied to the doubled A₇ source in 12.2.7, printed p.797.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterA.Section02 ClassificationModels
open Chapter4.Section04.NormalizedRankOneOddControl

private theorem no_seven_unitary_five_local
    {A : Type*} [Group A]
    (hS : ¬ Group.IsSolvable (alternatingGroup (Fin 7)))
    (π : A →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 5 E)
    (hcard : Nat.card E = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
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
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ,
      nat_card_alternatingGroup, Nat.card_fin] at hd
    norm_num at hd
  · simp only [↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ,
      nat_card_alternatingGroup, Nat.card_fin] at hd
    norm_num at hd

/-- All relative-rank-two Theorem B rows are incompatible with the actual
perfect residual, its moved two-subgroup and its alternating-seven quotient. -/
theorem no_BrankTwo_of_seven_residual_module
    {G : Type*} [Group G] [Finite G]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (π : F →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π)
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective hπ
  have hS := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7))
  have hc := no_CrankTwo_of_seven_residual_module F K U hFK hUF hne hcomm π hπ (n := n)
  cases hm with
  | linear hn he => exact hc (.linear hn he)
  | symplectic hn he => exact hc (.symplectic hn he)
  | g2 hn he => exact hc (.g2 hn he)
  | triality hn he => exact hc (.triality hn he)
  | ree_f4 m hm hn he => exact hc (.ree_f4 m hm hn he)
  | symplectic_derived hn he => exact hc (.symplectic_derived hn he)
  | g2_derived hn he => exact hc (.g2_derived hn he)
  | tits hn he => exact hc (.tits hn he)
  | unitary_four hn hm =>
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two
      n (by omega) hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
      J n (by omega) hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm t
    exact no_unitary_four_local hS seven_not_two_exponent π hπ J.conj J.conj_involutive
      n (by omega) hcard hconj _ hp hpne r hnorm
  | unitary_five hn hm =>
    subst n
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    have hcard' : Nat.card E = 16 := by simpa using hcard
    have hconj' : ∀ x, J.conj x = x ^ 4 := by simpa using hconj
    let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard'
    obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard' hconj'
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm t
    exact no_seven_unitary_five_local hS π hπ
      (HermitianForm.IdentityGram.identityGram J) hcard' hconj' rfl _ hp hpne r hnorm

/-- The binary symplectic six-space is excluded by the order of the same
residual inside the actual two-local normalizer of its core image. -/
theorem no_binary_symplectic_six_of_seven_residual_module
    {G : Type*} [Group G] [Finite G]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (π : F →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π)
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective hπ
  have hS := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7))
  obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
  let t := (e.trans (Theory.SpecificGroups.SymplecticSix.pspFieldEquivZModTwo E hcard)).trans
    Theory.SpecificGroups.SymplecticSix.EvenProjective.equiv.symm
  let r := residualQuotientMap hFK t
  let := residualQuotientMap_kernel_solvable hFK t
  obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm t
  let P := (pCore 2 F).map r
  let N := normalizer (P : Set (Theory.SpecificGroups.SymplecticSix.Sp (ZMod 2)))
  let k := r.codRestrict N (fun x => hnorm ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun _ hx => congrArg Subtype.val hx))
    (inclusion_injective _)
  have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
  apply Theory.SpecificGroups.SymplecticSix.twoLocal_not_dvd_thirtyFive N ⟨P,hpne,hp,rfl⟩
  have h35 : 35 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  exact h35.trans hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
