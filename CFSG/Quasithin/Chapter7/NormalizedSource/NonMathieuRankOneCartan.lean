module
public import Theory.SpecificGroups.Suzuki.OddCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Suzuki Cartan bounds and central covers

The order bound for a cyclic actor permuting with a Sylow gives n' <= n
for every inner-containing automorphism group of Sz(2^n). Faithful descent
to the central quotient transfers the complete witness from every perfect
central cover, preserving its Sylow and permutation clauses.

Source: Aschbacher--Smith E.3.37 and 7.3.4, printed pp.239,699.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds

/-- The Cartan exponent of every inner-containing Suzuki automorphism subgroup. -/
theorem suzuki_automorphism_cartan_bound {m : ℕ} (hm : 0 < m)
    (A : Subgroup (MulAut (SuzukiMatrixGroup m)))
    (hA : MulAut.innerSubgroup (SuzukiMatrixGroup m) ≤ A) : nPrime A ≤ 2*m+1 := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.cyclic
  have hc := SuzukiCartan.automorphism_odd_cyclic_cartan_card m hm A hA
    w.sylow w.abelianGroup w.cyclicGroup w.cyclic_le w.odd w.permutes
  rw [w.card] at hc
  have hp : 0 < 2^c := by positivity
  have hq : 0 < 2^(2*m+1) := by positivity
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp (by omega)

/-- Faithful central-quotient descent retains the entire Cartan witness. -/
theorem suzuki_centralCover_cartan_bound
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {m : ℕ} (hm : 0 < m) (e : (X ⧸ center X) ≃* SuzukiMatrixGroup m)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2*m+1 := by
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  have hinner : MulAut.innerSubgroup (SuzukiMatrixGroup m) ≤ A.map f := by
    rintro b ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := e.surjective y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center X) z
    exact ⟨MulAut.conj x,hA ⟨x,rfl⟩,MulAut.centralQuotientAction_conj e x⟩
  have hmap : Function.Injective (f.subgroupMap A) := by
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  obtain ⟨w⟩ := nPrime_spec (X := A)
  exact (w.map (f.subgroupMap A) (f.subgroupMap_surjective A)
    (hmap.comp w.cyclicGroup.subtype_injective)).le_nPrime.trans
      (suzuki_automorphism_cartan_bound hm _ hinner)
end CFSG.Quasithin.Chapter7.NormalizedSource
