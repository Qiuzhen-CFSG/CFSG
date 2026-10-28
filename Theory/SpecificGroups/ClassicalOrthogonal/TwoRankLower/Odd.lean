module
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.BlockMaps
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Comparison
public import Theory.SpecificGroups.Symplectic.TwoRankLower

/-!
# Two-rank in the actual odd-dimensional orthogonal carriers

In odd characteristic the elementary five-space is the centerless PSp₄.
Its literal block embedding remains injective after any ambient scalar
quotient: an element collapsing to a scalar would be central in PSp₄.
In characteristic two the actual odd-orthogonal/symplectic comparison gives
the same bound in every rank. Rank one is retained as the genuine PSL₂ alias.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace ClassicalOrthogonal.TwoRank
open Theory.AlgebraicGroup Fundamental.SplitOddBlocks Theory.GroupTheory
universe u
variable {F V H : Type u} [Field F] [AddCommGroup V] [Module F V] [Group H]

/-- A faithful centerless subgroup survives the literal orthogonal scalar quotient. -/
theorem projective_injective_of_centerless (Q : QuadraticForm F V)
    (f : H →* elementarySubgroup Q) (hf : Function.Injective f)
    (hc : Subgroup.center H = ⊥) :
    Function.Injective ((projectiveElementaryMap Q).comp f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro h hh
  have hs : f h ∈ elementaryScalarSubgroup Q := by
    change projectiveElementaryMap Q (f h) = 1 at hh
    exact (projectiveElementaryMap_kernel Q) ▸ (show f h ∈ (projectiveElementaryMap Q).ker from hh)
  have hz := elementaryScalarSubgroup_le_center Q hs
  have hh : h ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hf
    simpa only [map_mul] using (Subgroup.mem_center_iff.mp hz) (f g)
  simpa only [hc,Subgroup.mem_bot] using hh

variable (F : Type) [Field F] [Finite F]

/-- The five-space elementary subgroup is centerless in odd characteristic. -/
theorem odd_five_center (h2 : (2:F) ≠ 0) : Subgroup.center (OmegaOdd 2 F) = ⊥ := by
  have hcard : 2 < Nat.card F := by
    let := Fintype.ofFinite F
    have hcard : 1 < Nat.card F := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
    have hne : Nat.card F ≠ 2 := by
      intro hc
      have hc' : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hc
      let : CharP F 2 := charP_of_card_eq_prime hc'
      exact h2 CharTwo.two_eq_zero
    omega
  let := Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.perfect hcard
  let e := OddFiveComparison.pspEquivElementary (F:=F) h2
  apply bot_unique
  intro x hx
  have he : e.symm x ∈ Subgroup.center (Matrix.PSp4Three.PSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using (Subgroup.mem_center_iff.mp hx) (e y)
  rw [Group.IsPerfect.center_quotient_center_eq_bot,Subgroup.mem_bot] at he
  rw [Subgroup.mem_bot]
  apply e.symm.injective
  simpa only [map_one] using he

/-- An actual PSp₄ sits in each odd-dimensional projective orthogonal group of rank at least two. -/
def oddFiveEmbedding (h2 : (2:F) ≠ 0) (r : ℕ) :
    Matrix.PSp4Three.PSp 2 F →* POmegaOdd (r+2) F :=
  (projectiveElementaryMap (formB (r+2) F)).comp
    (((oddBlocks r 2).comp (MonoidHom.inr _ _)).comp
      (OddFiveComparison.pspEquivElementary h2).toMonoidHom)

theorem oddFiveEmbedding_injective (h2 : (2:F) ≠ 0) (r : ℕ) :
    Function.Injective (oddFiveEmbedding F h2 r) := by
  have hi : Function.Injective ((oddBlocks (F:=F) r 2).comp (MonoidHom.inr _ _)) :=
    (oddBlocks_injective r 2).comp (fun _ _ h => congrArg Prod.snd h)
  exact (projective_injective_of_centerless _ _ hi (odd_five_center F h2)).comp
    (OddFiveComparison.pspEquivElementary h2).injective

/-- Every rank at least two in the actual odd orthogonal family has two-rank at least three. -/
theorem odd_three_le {r : ℕ} (hr : 2 ≤ r) : 3 ≤ primeRank 2 (POmegaOdd r F) := by
  by_cases h2 : (2:F)=0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
    let : PerfectRing F 2 := inferInstance
    rw [primeRank_equiv 2 (TheoremDRootNormalizer.oddProjectiveEquivPSp (F:=F) (by omega : 0<r))]
    exact Theory.SpecificGroups.Symplectic.TwoRank.three_le F hr
  · obtain ⟨n,rfl⟩ : ∃ n, r=n+2 := ⟨r-2,by omega⟩
    exact (Theory.SpecificGroups.Symplectic.TwoRank.three_le F (by decide : 2≤2)).trans
      (primeRank_le_of_injective 2 (oddFiveEmbedding F h2 n) (oddFiveEmbedding_injective F h2 n))
end ClassicalOrthogonal.TwoRank
