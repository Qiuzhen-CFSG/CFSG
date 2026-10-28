module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Residual
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.CentralCoprimeLiftUnique

/-!
# The involution-centralizer residual in the actual PSL₃ quotient

The SL₃ scalar kernel is a central three-group. Coprime torsion lifting gives
an involution above each projective involution, and uniqueness of that lift
identifies its centralizer with the full preimage of the projective
centralizer. Surjectivity therefore transports solvable residuals.

The SL₃ residual is SL₂(q). Its intersection with the projection kernel
lies in its center, whose order is two, while the scalar kernel has order
dividing three. Thus projection is injective on the residual and gives the
actual SL₂(q) isomorphism in PSL₃(q), including when the scalar kernel is
nontrivial. No identification of SL₃ with PSL₃ is assumed.

Source: Aschbacher–Smith, A.3.21(a), printed p.55, and the canonical choice
in the proof of 1.3.4, printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

private theorem projection_ker_three (F : Type*) [Field F] [Finite F] :
    IsPGroup 3 (Matrix.PSL3.projection F).ker := by
  rw [Matrix.PSL3.projection_ker]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    (Matrix.SL3.card_center_dvd_three F) with h | h
  · exact IsPGroup.of_card (n := 0) (by simpa using h)
  · exact IsPGroup.of_card (n := 1) (by simpa using h)

/-- Every projective involution has an involutory lift under the actual projection. -/
theorem psl3_involution_lift (F : Type*) [Field F] [Finite F]
    (z : PSL(3, F)) (hz : orderOf z = 2) :
    ∃ w : SL(3, F), Matrix.PSL3.projection F w = z ∧ orderOf w = 2 := by
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨w, hw, hw2⟩ := (Matrix.PSL3.projection F).exists_pow_eq_one_lift_of_central_pgroup_ker
    (Matrix.PSL3.projection_surjective F)
    (by rw [Matrix.PSL3.projection_ker]) (projection_ker_three F)
    (by decide : Nat.Coprime 3 2) z hz2
  refine ⟨w, hw, orderOf_eq_prime hw2 ?_⟩
  intro he
  have hz1 : z = 1 := hw.symm.trans (by rw [he, map_one])
  simp [hz1] at hz

/-- The full preimage of a projective involution centralizer is its lift centralizer. -/
theorem sl3_comap_projective_involution_centralizer (F : Type*) [Field F] [Finite F]
    (z : SL(3, F)) (hz : orderOf z = 2) :
    (centralizer ({Matrix.PSL3.projection F z} : Set PSL(3, F))).comap
      (Matrix.PSL3.projection F) = centralizer ({z} : Set SL(3, F)) := by
  ext x
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have he : x * z * x⁻¹ = z :=
      (Matrix.PSL3.projection F).eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
        (by rw [Matrix.PSL3.projection_ker]) (projection_ker_three F)
        (by decide : Nat.Coprime 3 2)
        (by simp only [map_mul, map_inv, hx, mul_inv_cancel_right])
        (by change (MulAut.conj x z) ^ 2 = 1
            rw [← map_pow, show z ^ 2 = 1 from hz ▸ pow_orderOf_eq_one z, map_one])
        (hz ▸ pow_orderOf_eq_one z)
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · intro hx
    simpa only [map_mul] using congrArg (Matrix.PSL3.projection F) hx

private theorem residual_projection_injective (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (z : SL(3, ZMod q)) (hz : orderOf z = 2) :
    Function.Injective ((Matrix.PSL3.projection (ZMod q)).comp
      ((centralizer ({z} : Set SL(3, ZMod q))).subtype.comp
        (solvableResidual (centralizer ({z} : Set SL(3, ZMod q)))).subtype)) := by
  let C := centralizer ({z} : Set SL(3, ZMod q))
  let R := solvableResidual C
  let i : R →* SL(3, ZMod q) := C.subtype.comp R.subtype
  let f := (Matrix.PSL3.projection (ZMod q)).comp i
  change Function.Injective f
  apply f.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hcentral : i x ∈ center SL(3, ZMod q) := by
    rw [← Matrix.PSL3.projection_ker]
    exact hx
  have hxcenter : x ∈ center R := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_center_iff.mp hcentral (i y)
  have hcard : Nat.card (center R) = 2 := by
    rw [Nat.card_congr (centerCongr (sl3_involution_solvableResidual_equiv q hq hlarge z hz)).toEquiv]
    rw [← GorensteinWalter.sl2ProjectiveProjection_ker]
    exact GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by simpa using hq)
  have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (hcard ▸ (center R).orderOf_dvd_natCard hxcenter)
  have hi2 : i x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hi3 : i x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (((center SL(3, ZMod q)).orderOf_dvd_natCard hcentral).trans
      (Matrix.SL3.card_center_dvd_three (ZMod q)))
  have hi1 : i x = 1 := by simpa only [pow_succ, hi2, one_mul] using hi3
  exact Subtype.ext (Subtype.ext hi1)

/-- The solvable residual of a PSL₃(q) involution centralizer is SL₂(q), for q > 3. -/
noncomputable def psl3_involution_solvableResidual_equiv (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (z : PSL(3, ZMod q)) (hz : orderOf z = 2) :
    solvableResidual (centralizer ({z} : Set PSL(3, ZMod q))) ≃* SL(2, ZMod q) := by
  let w := Classical.choose (psl3_involution_lift (ZMod q) z hz)
  have hw := (Classical.choose_spec (psl3_involution_lift (ZMod q) z hz)).1
  have hw2 := (Classical.choose_spec (psl3_involution_lift (ZMod q) z hz)).2
  let C := centralizer ({w} : Set SL(3, ZMod q))
  let D := centralizer ({z} : Set PSL(3, ZMod q))
  let f := Matrix.PSL3.projection (ZMod q)
  have hCD : D.comap f = C := by
    dsimp only [D]
    rw [← hw]
    exact sl3_comap_projective_involution_centralizer (ZMod q) w hw2
  let c : C →* D := f.restrict (by rw [← hCD]; exact fun _ h => h)
  have hc : Function.Surjective c := by
    intro x
    obtain ⟨y, hy⟩ := Matrix.PSL3.projection_surjective (ZMod q) x
    have hyC : y ∈ C := by rw [← hCD]; change f y ∈ D; rw [hy]; exact x.property
    exact ⟨⟨y, hyC⟩, Subtype.ext hy⟩
  let r : solvableResidual C →* solvableResidual D :=
    c.restrict (fun x hx => map_solvableResidual_le c (mem_map_of_mem c hx))
  have hr : Function.Bijective r := by
    constructor
    · intro x y h
      apply residual_projection_injective q hq hlarge w hw2
      exact congrArg (fun v : solvableResidual D => ((v : D) : PSL(3, ZMod q))) h
    · intro x
      have hx : (x : D) ∈ (solvableResidual C).map c := by
        rw [map_solvableResidual_eq c hc]
        exact x.property
      obtain ⟨y, hy, he⟩ := hx
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact (MulEquiv.ofBijective r hr).symm.trans
    (sl3_involution_solvableResidual_equiv q hq hlarge w hw2)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
