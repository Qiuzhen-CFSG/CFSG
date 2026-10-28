module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.HigherRank
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Scalars
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualContainment

/-!
# Assembly of the minus block residual calculation

The projective centralizer lifting theorem reduces coverage to the full
orthogonal centralizer and restriction of ambient commutator membership to
the complementary block. Once these two independent calculations are supplied,
the projective block image is the entire marked centralizer. Siegel generation
of the actual complementary commutator then identifies it with the literal
prime-to-characteristic residual through the published subtype inclusion.

The structural premises remain explicit here: full orthogonal centralizer
splitting, reflection of commutator membership by extension, and equality of
the complementary elementary and commutator groups. Their source-theorem
assembly must discharge all three. Scalar specialization is exported separately
and also retains its missing commutator/spinor input. The higher-rank residual
nine-subgroup needs none of these additional premises.

Source: Aschbacher–Smith A.2.17, printed p.39; GLS3 §2.7. The ambient group is
exactly `ClassicalGroup.POmegaMinus (r + 3) F`, with the original marked left
SL₂ and complementary commutator Omega of rank `r + 1`.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- Full orthogonal centralizer splitting and commutator restriction identify the projective centralizer. -/
theorem projectiveBlockHom_range_eq_centralizer_of_structure [Finite F]
    (p : ℕ) [CharP F p] (ho : Odd p) (r : ℕ) (hq : 2 < Nat.card F)
    (hsplit : (fullBlockHom (F := F) r).range =
      Subgroup.centralizer ((fullFundamentalHom (F := F) r).range : Set _))
    (hrestrict : ∀ u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)),
      fullBlockHom r (1, u) ∈
        Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) →
      u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    (projectiveBlockHom r hq).range = fundamentalCentralizer r hq := by
  apply le_antisymm (projectiveBlockHom_le_centralizer r hq)
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Minus.scalarSubgroup F _ _) x
  have hy : y.val ∈ (fullBlockHom r).range := by
    rw [hsplit, Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (projective_centralizer_lifts p ho r hq y hx A).map (commutator _).subtype
  obtain ⟨⟨A, u⟩, hAu⟩ := hy
  have hu : u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
    apply hrestrict
    have hA : fullBlockHom r (A, 1) ∈
        Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) :=
      (coverBlockHom r hq (A, 1)).property
    have he : (A, 1)⁻¹ * (A, u) = (1, u) := by simp
    rw [← he, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) (hAu ▸ y.property)
  refine ⟨(A, ⟨u, hu⟩), ?_⟩
  change QuotientGroup.mk' (Minus.scalarSubgroup F _ _) (coverBlockHom r hq _) = _
  exact congrArg (QuotientGroup.mk' (Minus.scalarSubgroup F _ _)) (Subtype.ext hAu)

/-- Elementary generation of the actual complement puts the entire block image in the residual. -/
theorem projectiveBlockHom_range_le_residual_of_elementary [Finite F]
    (p : ℕ) [CharP F p] (r : ℕ) (hq : 2 < Nat.card F)
    (hgen : elementarySubgroup (Minus.quadraticForm F (r + 1)) =
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    (projectiveBlockHom r hq).range ≤ centralizerResidualImage p r hq := by
  let f := blockToCentralizer r hq
  let e := MulEquiv.subgroupCongr hgen
  rintro _ ⟨g, rfl⟩
  have h1 := Matrix.SL2.map_mem_primeToResidual p (f.comp (MonoidHom.inl _ _)) g.1
  have h2 := SplitOddBlocks.elementary_map_mem_primeToResidual p
    (Minus.quadraticForm F (r + 1))
    ((f.comp (MonoidHom.inr _ _)).comp e.toMonoidHom) (e.symm g.2)
  have hg : f g ∈ centralizerResidual p r hq := by
    have he : g = (g.1, 1) * (1, g.2) := by simp
    rw [he, map_mul]
    apply Subgroup.mul_mem _ h1
    change f (1, e (e.symm g.2)) ∈ _ at h2
    simpa only [MulEquiv.apply_symm_apply] using h2
  exact ⟨f g, hg, rfl⟩

/-- Assemble the literal residual equality from the independent isometry and commutator calculations. -/
theorem projectiveBlockHom_range_eq_residual_of_structure [Finite F]
    (p : ℕ) [CharP F p] (ho : Odd p) (r : ℕ) (hq : 2 < Nat.card F)
    (hsplit : (fullBlockHom (F := F) r).range =
      Subgroup.centralizer ((fullFundamentalHom (F := F) r).range : Set _))
    (hrestrict : ∀ u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)),
      fullBlockHom r (1, u) ∈
        Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) →
      u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hgen : elementarySubgroup (Minus.quadraticForm F (r + 1)) =
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    (projectiveBlockHom r hq).range = centralizerResidualImage p r hq := by
  apply le_antisymm (projectiveBlockHom_range_le_residual_of_elementary p r hq hgen)
  rw [projectiveBlockHom_range_eq_centralizer_of_structure p ho r hq hsplit hrestrict]
  exact Subgroup.map_subtype_le _


end ClassicalOrthogonal.Fundamental.MinusCentralizer
