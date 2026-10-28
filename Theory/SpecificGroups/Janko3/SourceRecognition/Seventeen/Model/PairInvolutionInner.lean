module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Pair
public import Theory.SpecificGroups.Janko3.SourceRecognition.PairAutomorphisms

/-!
# Involutory automorphisms of the full pair are inner

The pair is D₃ × D₅. Its noninner automorphism coset consists of inner
conjugations followed by coordinate doubling. The square of each such
map moves the standard quintic rotation, as checked on the sixty possible
conjugators. An automorphism whose square is identity is therefore inner.
The pair has trivial center, so its conjugating element also squares to one.
No automorphism group is enumerated.
-/

noncomputable section
open Subgroup
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

private def pairDihedral : pair ≃* PairAutomorphisms.H :=
  pairEquiv.trans (MulEquiv.prodCongr CyclicCoordinates.trianglePermEquiv.symm
    (MulEquiv.refl (DihedralGroup 5)))

private theorem outer_square_moves : ∀ h : PairAutomorphisms.H,
    (MulAut.conj h * PairAutomorphisms.delta)
      ((MulAut.conj h * PairAutomorphisms.delta) (1,DihedralGroup.r 1)) ≠
        (1,DihedralGroup.r 1) := by decide +kernel

private theorem center_coordinates : center PairAutomorphisms.H = ⊥ := by
  rw [Subgroup.center_prod,
    DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide),
    DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide)]
  simp

/-- The full pair has trivial center. -/
public theorem pair_center_eq_bot : center pair = ⊥ := by
  apply bot_unique
  intro z hz
  have he : pairDihedral z ∈ center PairAutomorphisms.H := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := pairDihedral.surjective x
    rw [←map_mul,←map_mul,(mem_center_iff.mp hz) y]
  rw [center_coordinates] at he
  exact pairDihedral.injective (show pairDihedral z = pairDihedral 1 by simpa using he)

/-- A pair automorphism squaring to identity is conjugation by an element squaring to one. -/
public theorem pair_involution_inner (φ : MulAut pair) (hφ : φ * φ = 1) :
    ∃ b : pair, b ^ 2 = 1 ∧ φ = MulAut.conj b := by
  let a : MulAut PairAutomorphisms.H := MulAut.congr pairDihedral φ
  have ha : a * a = 1 := by
    change (MulAut.congr pairDihedral) φ * (MulAut.congr pairDihedral) φ = 1
    rw [←map_mul,hφ,map_one]
  obtain ⟨h,ε,he⟩ := PairAutomorphisms.exists_inner_mul_delta a
  have hai : a = MulAut.conj h := by
    cases ε
    · simpa using he
    · have hx := congrArg (fun f : MulAut PairAutomorphisms.H => f (1,DihedralGroup.r 1)) ha
      have he' : a = MulAut.conj h * PairAutomorphisms.delta := by simpa using he
      rw [he'] at hx
      exact False.elim (outer_square_moves h hx)
  let b : pair := pairDihedral.symm h
  have hbi : φ = MulAut.conj b := by
    apply MulEquiv.ext
    intro x
    apply pairDihedral.injective
    have hx := congrArg (fun f : MulAut PairAutomorphisms.H => f (pairDihedral x)) hai
    simpa [a,b,MulAut.congr,MulAut.conj_apply] using hx
  refine ⟨b,?_,hbi⟩
  have hbcenter : b ^ 2 ∈ center pair := by
    have hh : MulAut.conj (b ^ 2) = 1 := by
      rw [pow_two,map_mul,←hbi]
      exact hφ
    apply mem_center_iff.mpr
    intro x
    have hx := congrArg (fun f : MulAut pair => f x) hh
    change b ^ 2 * x * (b ^ 2)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  simpa only [pair_center_eq_bot,mem_bot] using hbcenter

/-- Pointwise involutivity gives the same literal inner-action formula. -/
public theorem pair_involutive_inner (φ : MulAut pair) (hφ : ∀ x, φ (φ x) = x) :
    ∃ b : pair, b ^ 2 = 1 ∧ ∀ x : pair, φ x = b * x * b⁻¹ := by
  have hs : φ * φ = 1 := MulEquiv.ext hφ
  obtain ⟨b,hb,hbe⟩ := pair_involution_inner φ hs
  exact ⟨b,hb,fun x => by rw [hbe]; rfl⟩

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
