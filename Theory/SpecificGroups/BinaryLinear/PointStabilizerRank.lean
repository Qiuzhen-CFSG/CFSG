module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Representation.SpecialLinearNatural

/-!
# Three-rank of binary natural point stabilizers

A binary point stabilizer is the parabolic of its one-dimensional span.
The quotient by its two-core has the two diagonal linear factors. If the
ambient dimension is at least five, the quotient factor on the complementary
space has dimension at least four and three-rank at least two. Odd prime
rank is unchanged by the two-core, and the actual binary SL–GL equivalence
transports the result to determinant-one matrices.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 13.7.6(1–2), printed pp.938–939.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.PointStabilizerRank
open SmallParabolicLevi OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private instance [Finite V] : Finite (BinaryLinear.GL V) :=
  Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective

/-- A parabolic of codimension at least four has three-rank at least two. -/
theorem two_le_parabolic [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (hW : 4 ≤ Module.finrank (ZMod 2) (V ⧸ W)) :
    2 ≤ primeRank 3 (parabolic W) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ⧸ W) := Module.finite_of_finite (ZMod 2)
  let e := (Module.finBasis (ZMod 2) (V ⧸ W)).equivFun
  have hquot : 2 ≤ primeRank 3 (BinaryLinear.GL (V ⧸ W)) := by
    rw [primeRank_equiv 3 (linearGroupCongr e), ← primeRank_equiv 3
      (slEquivLinear (Module.finrank (ZMod 2) (V ⧸ W)))]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hW
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (parabolic W)) pCore_isPGroup,
    primeRank_equiv 3 (quotientTwoCoreEquiv W), primeRank_prod_eq_add]
  omega

private theorem mem_binary_span (v w : V) :
    w ∈ Submodule.span (ZMod 2) {v} ↔ w = 0 ∨ w = v := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem stabilizer_eq_parabolic (v : V) :
    MulAction.stabilizer (BinaryLinear.GL V) v = parabolic (Submodule.span (ZMod 2) {v}) := by
  ext g
  change g v = v ↔ ∀ w, g w ∈ Submodule.span (ZMod 2) {v} ↔
    w ∈ Submodule.span (ZMod 2) {v}
  simp only [mem_binary_span]
  constructor
  · intro h w
    constructor
    · rintro (hz | he)
      · exact Or.inl (g.injective (hz.trans (map_zero g).symm))
      · exact Or.inr (g.injective (he.trans h.symm))
    · rintro (rfl | rfl)
      · exact Or.inl (map_zero g)
      · exact Or.inr h
  · intro h
    rcases (h v).mpr (Or.inr rfl) with hz | he
    · have hv : v = 0 := g.injective (hz.trans (map_zero g).symm)
      simp [hv]
    · exact he

/-- Every nonzero point in a binary vector space of dimension at least five
has a stabilizer of three-rank at least two. -/
theorem two_le_linear_stabilizer [FiniteDimensional (ZMod 2) V]
    (hV : 5 ≤ Module.finrank (ZMod 2) V) (v : V) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (MulAction.stabilizer (BinaryLinear.GL V) v) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  rw [stabilizer_eq_parabolic]
  apply two_le_parabolic
  have h := (Submodule.span (ZMod 2) {v}).finrank_quotient_add_finrank
  rw [finrank_span_singleton hv] at h
  omega

/-- The actual natural matrix stabilizer and the corresponding linear-map
stabilizer agree through the binary SL–GL equivalence. -/
noncomputable def naturalStabilizerEquiv (n : ℕ) (v : Fin n → ZMod 2) :
    MulAction.stabilizer SL(n, ZMod 2) v ≃*
      MulAction.stabilizer (BinaryLinear.GL (Fin n → ZMod 2)) v :=
  ((MulAction.stabilizer SL(n, ZMod 2) v).equivMapOfInjective
    (slEquivLinear n).toMonoidHom (slEquivLinear n).injective).trans
      (MulEquiv.subgroupCongr (by
        ext g
        constructor
        · rintro ⟨s,hs,rfl⟩
          exact hs
        · intro hg
          refine ⟨(slEquivLinear n).symm g, ?_, (slEquivLinear n).apply_symm_apply g⟩
          change slEquivLinear n ((slEquivLinear n).symm g) v = v
          rw [MulEquiv.apply_symm_apply]
          exact hg))

/-- In the natural module of SLₙ(2), n ≥ 5, every nonzero point stabilizer
has three-rank at least two. -/
theorem two_le_natural_stabilizer {n : ℕ} (hn : 5 ≤ n)
    (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    2 ≤ primeRank 3 (MulAction.stabilizer SL(n, ZMod 2) v) := by
  rw [primeRank_equiv 3 (naturalStabilizerEquiv n v)]
  exact two_le_linear_stabilizer (by simpa using hn) v hv
end BinaryLinear.PointStabilizerRank
