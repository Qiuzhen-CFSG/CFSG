module
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Mathlib.GroupTheory.IsPerfect
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity

/-!
# Perfect subgroups of the PSU₅(4) two-locals

The line parabolic is the proved product of a binary radical with SU₃(4)
and a cubic scalar group. Perfectness kills that scalar, and the SU₃ order
has only one factor three. The plane parabolic's entire order has only one
factor five. The fixed isotropic subspace and its special-unitary transport
therefore exclude a perfect subgroup with both odd ranks at least two from
every actual two-local.

Source: Aschbacher--Smith 4.4.12, printed p.622, using the literal full
parabolics of F.1.12(7), printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.PerfectLocals
open LineCore.Parabolic.Blocks
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

theorem perfect_line_threeRank_le_one
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* lineParabolic J) (hf : Function.Injective f) : primeRank 3 H ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let e := MulEquiv.ofBijective (fullMap J hconj c hc hJ)
    ⟨fullMap_injective J hconj c hc hJ,
      Exhaustion.fullMap_surjective J hconj hcard c hc hJ⟩
  let j := e.symm.toMonoidHom.comp f
  have hj : Function.Injective j := e.symm.injective.comp hf
  let k := (productProjection J hconj).comp j
  let d := (productCharacter J hconj).comp j
  have hd (x : H) : d x = 1 :=
    Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
  have hk : k.ker = ((SemidirectProduct.inl : LineCore.Coord J →* FullProduct J hconj).range).comap j := by
    ext x
    rw [← product_common_kernel]
    change k x = 1 ↔ k x = 1 ∧ d x = 1
    exact ⟨fun h => ⟨h,hd x⟩, And.left⟩
  have ht : IsPGroup 2 k.ker := by
    rw [hk]
    exact ((LineCore.Coord.isPGroup (J := J)).of_surjective
      (SemidirectProduct.inl : LineCore.Coord J →* FullProduct J hconj).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)).comap_of_injective j hj
  have hz : primeRank 3 k.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n,hn⟩ := ht.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h)
  have hs : primeRank 3 (LineCore.Parabolic.middleForm J).specialSubgroup ≤ 1 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rw [card_identity_su3_four (LineCore.Parabolic.middleForm J) hcard hconj rfl]
    decide
  have h := primeRank_le_ker_add (p := 3) k
  omega

theorem plane_fiveRank_le_one
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    primeRank 5 (planeParabolic J) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  apply primeRank_le_of_prime_pow_not_dvd
  rw [card_planeParabolic_four J hcard hconj hJ]
  decide

/-- A perfect subgroup in an actual two-local cannot have both marked odd ranks. -/
theorem no_perfect_three_five_rank_two_in_twoLocal
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Injective f)
    (h3 : 2 ≤ primeRank 3 H) (h5 : 2 ≤ primeRank 5 H)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hM : IsTwoLocal M) (hle : f.range ≤ M) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨W,hn,hi,_,hMW⟩ := IsotropicGeometry.projective_twoLocal_stabilizes_isotropic J hJ M hM
  obtain ⟨b,g,hg⟩ := IsotropicTransitivity.transitive J hcard hconj hJ W hn hi
  have he : parabolic J W = (if b then planeParabolic J else lineParabolic J).map
      (MulAut.conj (project J g)).toMonoidHom := by
    rw [hg, IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hMW
  let j := (MulAut.conj (project J g)⁻¹).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj (project J g)⁻¹).injective.comp hf
  have hc : j.range ≤ (if b then planeParabolic J else lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hMW (hle ⟨x,rfl⟩)
    change (project J g)⁻¹ * f x * ((project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply, mul_assoc] using hy
  cases b
  · let k := j.codRestrict _ (fun x => hc ⟨x,rfl⟩)
    have hk : Function.Injective k := fun _ _ h => hj (congrArg Subtype.val h)
    have hh := perfect_line_threeRank_le_one J hcard hconj hJ k hk
    omega
  · let k := j.codRestrict _ (fun x => hc ⟨x,rfl⟩)
    have hk : Function.Injective k := fun _ _ h => hj (congrArg Subtype.val h)
    have hh := (primeRank_le_of_injective 5 k hk).trans
      (plane_fiveRank_le_one J hcard hconj hJ)
    omega
end Theory.SpecificGroups.UnitaryFive.PerfectLocals
