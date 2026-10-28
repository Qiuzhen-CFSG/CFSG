module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.MatrixWitnesses
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# An inner elementary nine-group fixed by a cubic field automorphism

A coefficient automorphism whose cube is one fixes every cube root of unity:
its permutation of the two primitive cubic roots cannot have order three.
In even binary degree, choose a nontrivial such root. The projective images
of diag(1,u,u²) and a coordinate three-cycle are independent commuting
cubics, and both are fixed. The existing matrix witness bounds the rank of
the actual fixed subgroup below by two. Extracting an elementary subgroup
of order nine and applying faithful inner conjugation gives the required
subgroup of Aut(PSL₃). Transport by any actual automorphism preserves all
four assertions, including pointwise centralization of the conjugate actor.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of A.3.18,
printed pp.51–53, and the last paragraph of 15.3.37, printed p.1135.
The projective semilinear descent needed for arbitrary standard actors is
separate; none is assumed in the pure-field theorem.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
open Theory.SpecificGroups Theory.SpecificGroups.SignedThreeCubicRank

namespace Matrix.PSL3.StandardCubicFixedNine

private theorem fixes_cubic_scalar {F : Type*} [Field F] (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1) : σ u = u := by
  have hp : IsPrimitiveRoot u 3 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime hu hne)
  obtain ⟨k, hk, he⟩ := hp.eq_pow_of_pow_eq_one (show σ u ^ 3 = 1 by rw [← map_pow, hu, map_one])
  have hne' : σ u ≠ 1 := by simpa using hne
  have hs' : σ (σ (σ u)) = u := DFunLike.congr_fun hs u
  interval_cases k
  · exact (hne' (by simpa using he.symm)).elim
  · simpa using he.symm
  · have h2 : σ u = u ^ 2 := he.symm
    rw [h2, map_pow, h2, map_pow, map_pow, h2] at hs'
    have h8 : ((u ^ 2) ^ 2) ^ 2 = u ^ 2 := by
      calc ((u ^ 2) ^ 2) ^ 2 = u ^ 3 * u ^ 3 * u ^ 2 := by ring
           _ = u ^ 2 := by rw [hu]; simp
    rw [h8] at hs'
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu
    have h1 : u = 1 := by
      apply mul_right_cancel₀ hu0
      simpa only [pow_two, one_mul] using hs'
    exact (hne h1).elim

/-- The actual projective fixed subgroup has three-rank at least two. -/
theorem field_fixed_primeRank_ge_two {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n)
    (σ : F ≃+* F) (hs : σ ^ 3 = 1) :
    2 ≤ primeRank 3 (fieldAction F σ).fixedSubgroup := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by
    rw [Nat.card_units, hcard]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn)
  have hu3 : (u : F) ^ 3 = 1 := congrArg Units.val (orderOf_eq_prime_iff.mp hu).1
  have hu1 : (u : F) ≠ 1 := fun h => (orderOf_eq_prime_iff.mp hu).2 (Units.ext h)
  have hfix : σ (u : F) = u := fixes_cubic_scalar σ hs u hu3 hu1
  have hd : fieldAction F σ (QuotientGroup.mk (SignedThreeCubicRank.diagonal (u : F) hu3)) =
      QuotientGroup.mk (SignedThreeCubicRank.diagonal (u : F) hu3) := by
    rw [fieldAction_mk]
    congr 1
    apply Subtype.ext
    ext i j
    change σ ((SignedThreeCubicRank.diagonal (u : F) hu3).val i j) = (SignedThreeCubicRank.diagonal (u : F) hu3).val i j
    fin_cases i <;> fin_cases j <;> simp [SignedThreeCubicRank.diagonal, hfix]
  have hc : fieldAction F σ (QuotientGroup.mk (SignedThreeCubicRank.cycle (F := F))) =
      QuotientGroup.mk (SignedThreeCubicRank.cycle (F := F)) := by
    rw [fieldAction_mk]
    congr 1
    apply Subtype.ext
    ext i j
    change σ ((SignedThreeCubicRank.cycle (F := F)).val i j) = (SignedThreeCubicRank.cycle (F := F)).val i j
    fin_cases i <;> fin_cases j <;> simp [SignedThreeCubicRank.cycle]
  exact projective_rank (u : F) hu3 hu1
    (Matrix.ProjectiveSpecialLinearGroup.toPGL.comp (fieldAction F σ).fixedSubgroup.subtype)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp Subtype.val_injective)
    ⟨QuotientGroup.mk (SignedThreeCubicRank.diagonal (u : F) hu3), (MulAut.mem_fixedSubgroup _ _).mpr hd⟩
    ⟨QuotientGroup.mk (SignedThreeCubicRank.cycle (F := F)), (MulAut.mem_fixedSubgroup _ _).mpr hc⟩ rfl rfl

private theorem nine_of_rank {G : Type*} [Group G] [Finite G]
    (hr : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨A, hA, hc⟩ := exists_elementaryAbelian_card_primeRank (G := G) (p := 3)
  let := hA
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 3
    (n := 2) (by rw [hc]; exact pow_dvd_pow 3 hr)
  let : IsElementaryAbelian 3 B :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun b => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 A) b.val }
  refine ⟨B.map A.subtype, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hB]
  norm_num

private theorem inner_nine_of_rank {G : Type*} [Group G] [Finite G]
    (hcenter : center G = ⊥) (a : MulAut G) (hr : 2 ≤ primeRank 3 a.fixedSubgroup) :
    ∃ E : Subgroup (MulAut G), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup G ∧ Nat.card E = 9 ∧
      E ≤ centralizer ({a} : Set (MulAut G)) := by
  obtain ⟨A, hA, hc⟩ := nine_of_rank hr
  let := hA
  let f : a.fixedSubgroup →* MulAut G := MulAut.conj.comp a.fixedSubgroup.subtype
  have hf : Function.Injective f :=
    (MulAut.conj_injective_of_center_eq_bot hcenter).comp Subtype.val_injective
  refine ⟨A.map f, IsElementaryAbelian.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.val, rfl⟩
  · rw [Subgroup.card_map_of_injective hf, hc]
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro y
    change x.val * a y * x.val⁻¹ = a (x.val * y * x.val⁻¹)
    rw [map_mul, map_mul, map_inv, (MulAut.mem_fixedSubgroup a x.val).mp x.property]

private theorem centerless {G : Type*} [Group G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hns (Group.isSolvable_of_comm (center_eq_top_iff.mp h).is_comm.comm)).elim

/-- A cubic coefficient actor fixes an elementary inner subgroup of order nine. -/
theorem exists_fixed_inner_nine_of_field {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n)
    (σ : F ≃+* F) (hs : σ ^ 3 = 1) :
    ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
      E ≤ centralizer ({fieldAction F σ} : Set (MulAut PSL(3,F))) :=
  inner_nine_of_rank (centerless hns) _ (field_fixed_primeRank_ge_two hcard hn σ hs)

/-- The fixed inner nine-group transports along an actual conjugation of actors. -/
theorem exists_fixed_inner_nine_of_conjugate_field {F : Type*} [Field F] [Finite F]
    [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n)
    (a d : MulAut PSL(3,F)) (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (hd : MulAut.congr d a = fieldAction F σ) :
    ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
      E ≤ centralizer ({a} : Set (MulAut PSL(3,F))) := by
  obtain ⟨E, hE, hinner, hc, hfix⟩ := exists_fixed_inner_nine_of_field hns hcard hn σ hs
  let := hE
  let f := (MulAut.congr d.symm).toMonoidHom
  have hfa : f (fieldAction F σ) = a := by
    rw [← hd]
    exact (MulAut.congr d).symm_apply_apply a
  refine ⟨E.map f, IsElementaryAbelian.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := hinner hx
    exact ⟨d.symm y, (MulAut.congr_conj d.symm y).symm⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr d.symm).injective, hc]
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg f (mem_centralizer_singleton_iff.mp (hfix hx))
    simpa only [map_mul, hfa] using h

end Matrix.PSL3.StandardCubicFixedNine
