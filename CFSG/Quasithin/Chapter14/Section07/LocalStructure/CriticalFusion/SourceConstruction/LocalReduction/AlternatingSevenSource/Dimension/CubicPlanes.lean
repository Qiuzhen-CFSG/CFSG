module
public import Theory.Representation.BinaryPermutation.SevenSourceCubics
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
/-!
# Two incompatible cubic orbits in a binary seed plane

The first cubic commutes with the marked transposition, which inverts the
second cubic. If both cubic orbits of a nonzero Sylow-fixed vector lie in a
common plane, the first orbit makes that transposition trivial on the plane.
The second orbit then contains a fixed vector for its cubic. Thus an action
with fixed-point-free three-cycles cannot satisfy the original source orbit
bound. This applies to the four-plus-dual alternative in 14.7.50.
-/

open Subgroup Representation
open BinaryPermutation.SevenSourceCubics
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension
local instance (t : Equiv.Perm (Fin 7)) : Decidable t.IsThreeCycle :=
  inferInstanceAs (Decidable (t.cycleType = {3}))
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
omit [FiniteDimensional (ZMod 2) W] in
private theorem binary_pair_independent (s v : W) (hs : s ≠ 0)
    (hv : v ≠ 0) (hvs : v ≠ s) : LinearIndependent (ZMod 2) ![s,v] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hb : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
  rcases hb a with rfl | rfl <;> rcases hb b with rfl | rfl <;>
    simp only [zero_smul,one_smul,zero_add,add_zero] at hab ⊢
  · trivial
  · exact (hv hab).elim
  · exact (hs hab).elim
  · exact (hvs (by simpa only [ZModModule.neg_eq_self] using
      (eq_neg_of_add_eq_zero_right hab))).elim

/-- The two actual cubic source orbits cannot both lie in a binary seed plane
when three-cycles have no nonzero fixed vectors. -/
theorem no_common_seed_plane (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) W)
    (hfree : ∀ g : Equiv.Perm (Fin 7), g.IsThreeCycle →
      ∀ w : W, ρ g w = w → w = 0)
    (s : W) (hs : s ≠ 0)
    (hfix : ∀ t ∈ standardTwo, ρ t s = s)
    (S : Submodule (ZMod 2) W) (hdim : Module.finrank (ZMod 2) S = 2)
    (hsS : s ∈ S) (hfirst : ρ first s ∈ S) (hsecond : ρ second s ∈ S) : False := by
  have hf0 : ρ first s ≠ 0 := by
    intro he
    have hh := congrArg (ρ first⁻¹) he
    simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply,map_zero] at hh
    exact hs hh
  have hfs : ρ first s ≠ s := fun he => hs (hfree first (by decide) s he)
  let P := Submodule.span (ZMod 2) ({s,ρ first s} : Set W)
  have hP : Module.finrank (ZMod 2) P = 2 := by
    have hh := finrank_span_eq_card (binary_pair_independent s (ρ first s) hs hf0 hfs)
    have he : Set.range ![s,ρ first s] = ({s,ρ first s} : Set W) := by
      ext w
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![s,ρ first s])) = 2 at hh
    rw [he] at hh
    exact hh
  have hPS : P ≤ S := by
    apply Submodule.span_le.mpr
    rintro w (rfl | rfl) <;> assumption
  have hPeq : P = S := Submodule.eq_of_le_of_finrank_eq hPS (hP.trans hdim.symm)
  let t : Equiv.Perm (Fin 7) := Equiv.swap 2 3
  have ht : ρ t s = s := hfix t (by decide)
  have htf : ρ t (ρ first s) = ρ first s := by
    rw [←Module.End.mul_apply,←map_mul,show t * first = first * t by decide,
      map_mul,Module.End.mul_apply,ht]
  have hPfix : ∀ w ∈ P, ρ t w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rcases hw with rfl | rfl <;> assumption
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add,hx,hy]
    | smul a x _ hx => rw [map_smul,hx]
  have hts : ρ t (ρ second s) = ρ second s := hPfix _ (hPeq.symm ▸ hsecond)
  have hi : ρ second⁻¹ s = ρ second s := by
    calc
      ρ second⁻¹ s = ρ second⁻¹ (ρ t s) := by rw [ht]
      _ = ρ t (ρ second s) := by
        rw [←Module.End.mul_apply,←map_mul,show second⁻¹ * t = t * second by decide,
          map_mul,Module.End.mul_apply]
      _ = ρ second s := hts
  have hf : ρ second s = s := by
    have hh := congrArg (ρ second) hi
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
      Module.End.one_apply] at hh
    have hpow : second * second = second⁻¹ := by decide
    rw [hpow,hi] at hh
    exact hh.symm
  exact hs (hfree second (by decide) s hf)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension
