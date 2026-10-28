module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel.LocalAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional.ModelCentralizers
public import Theory.SpecificGroups.SU3.FourOuterAction
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.PPerfectHom

/-!
# The marked A₃ action on PSU₃(4)

The actual A₃ block is two-perfect and its quotient by O₂ has order three.
Consequently it has no nontrivial image in a group of order prime to three.
If Out(X) is a two-group, two-perfection first makes the entire block action
inner. Fixing the marked involution then places this image in the conjugation
image of its inner centralizer, whose order is prime to three for PSU₃(4).

The proved arbitrary-automorphism coverage theorem, specialized to fixed-field
order four and matrix-field order sixteen, supplies the semilinear formulas.
The matrix calculation in `FourOuterAction` then gives the outer two-group.
A genuine Hermitian basis change handles the arbitrary form in
`ClassicalGroup.IsPSU`. The final theorem discharges coverage and all transports.

Source: Aschbacher–Smith, E.6.8 and E.6.23, printed pp.247–248 and 254–255;
C.1.7 and C.1.12, printed pp.123–124; GLS3, Theorem 2.5.12 and §2.7.
-/

public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel

private theorem three_block_hom_eq_one
    {D Y : Type*} [Group D] [Finite D] [Group Y] [Finite Y]
    (hD : ChapterC.IsAlternatingBlock D 3) (hY : ¬ 3 ∣ Nat.card Y)
    (f : D →* Y) : f = 1 := by
  have hq : Nat.card (D ⧸ pCore 2 D) = 3 := by
    obtain ⟨e⟩ := hD.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hc : Nat.card D = 2 ^ n * 3 := by
    rw [← (pCore 2 D).card_mul_index, hn]
    exact congrArg (2 ^ n * ·) hq
  have hr : Nat.card f.range ∣ 2 ^ n * 3 := hc ▸ card_range_dvd f
  have h3 : Nat.Coprime (Nat.card f.range) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun h => hY (h.trans f.range.card_subgroup_dvd_card))).symm
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (h3.dvd_mul_right.mp hr)
  have he := hD.2.1.twoPerfect.hom_eq_one_of_isPGroup hp f.rangeRestrict
  ext d
  exact congrArg (fun a : D →* f.range => (a d : Y)) he

private theorem action_eq_one_of_outer_isTwoGroup
    {D X : Type*} [Group D] [Finite D] [Group X] [Finite X]
    (hD : ChapterC.IsAlternatingBlock D 3)
    (ho : IsPGroup 2 (MulAut.Outer X))
    (ρ : D →* MulAut X) (t : X)
    (hc : ¬ 3 ∣ Nat.card (centralizer ({t} : Set X)))
    (hfix : ∀ d : D, ρ d t = t) : ρ = 1 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup X)
  have he := hD.2.1.twoPerfect.hom_eq_one_of_isPGroup ho (q.comp ρ)
  let C := (centralizer ({t} : Set X)).map (MulAut.conj : X →* MulAut X)
  have hρ (d : D) : ρ d ∈ C := by
    have hi : ρ d ∈ MulAut.innerSubgroup X :=
      (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun he d)
    obtain ⟨x, hx⟩ := hi
    refine ⟨x, ?_, hx⟩
    apply mem_centralizer_singleton_iff.mpr
    have ht := hfix d
    rw [← hx] at ht
    exact mul_inv_eq_iff_eq_mul.mp ht
  have hC : ¬ 3 ∣ Nat.card C := fun h =>
    hc (h.trans (card_map_dvd _ (MulAut.conj : X →* MulAut X)))
  have htr := three_block_hom_eq_one hD hC (ρ.codRestrict C hρ)
  apply MonoidHom.ext
  intro d
  exact congrArg (fun a : D →* C => (a d : MulAut X)) htr

/-- The inner centralizer calculation finishes the marked action once the
actual outer group is known to be a two-group. Subnormality and the Sylow
marking are unnecessary for this stronger local deduction. -/
theorem unitaryThree_fixedSylowActionTrivial_of_outer_isTwoGroup
    {X : Type*} [Group X] [Finite X] (hm : ClassicalGroup.IsPSU X 3 4)
    (ho : IsPGroup 2 (MulAut.Outer X)) : FixedSylowActionTrivial X := by
  intro H D _ _ _ _ hD ι _ _ ρ S _ t ht ht2 hfix
  have ht1 : t ≠ 1 := fun h => ht (h ▸ (center X).one_mem)
  exact action_eq_one_of_outer_isTwoGroup hD ho (ρ.comp ι) t
    (ComponentCase.ThreeDimensional.unitary_four_centralizer_three_free hm t ht1 ht2)
    (fun d => hfix (ι d))

open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

/-- The full marked action follows from arbitrary-automorphism coverage of
the standard matrix model over the field of order sixteen. All model and
Hermitian-form transports are discharged here; coverage remains explicit. -/
theorem unitaryThree_fixedSylowActionTrivial_of_standard_coverage
    {X : Type*} [Group X] [Finite X] (hm : ClassicalGroup.IsPSU X 3 4)
    (hcoverage : ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      Nat.card F = 4 ^ 2 → Nat.card {x : F // J.conj x = x} = 4 →
      ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
        ∃ σ : F ≃+* F, J.HasUnitarySemilinearForm a σ) :
    FixedSylowActionTrivial X := by
  apply unitaryThree_fixedSylowActionTrivial_of_outer_isTwoGroup hm
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
  have hfixed : Nat.card {x : F // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hconj
  obtain ⟨eJ⟩ := exists_projectiveEquiv J 4 hF hfixed
  have hp := (standardForm J).outer_isTwoGroup_of_four_semilinear_coverage
    rfl hF hconj (hcoverage F (standardForm J) rfl hF hfixed)
  exact hp.of_equiv (MulAut.outerCongr (e.trans eJ)).symm

/-- Every marked A₃ action on PSU₃(4) is trivial. Arbitrary-automorphism
coverage is supplied at binary exponent two; no additional coverage or
quasisimplicity premise is needed. -/
theorem unitaryThree_fixedSylowActionTrivial
    {X : Type*} [Group X] [Finite X] (hm : ClassicalGroup.IsPSU X 3 4) :
    FixedSylowActionTrivial X := by
  apply unitaryThree_fixedSylowActionTrivial_of_standard_coverage hm
  intro F _ _ J hJ hF hfixed a
  exact J.semilinear_coverage 2 (by decide) hJ hF hfixed a

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
