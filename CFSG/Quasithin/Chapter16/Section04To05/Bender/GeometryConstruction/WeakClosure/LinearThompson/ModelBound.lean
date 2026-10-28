module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.Action
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.Kernel
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.ModelBound.Transport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import Theory.SpecificGroups.PSL2.RootSemilinearFixedBound
public import Theory.ElementaryAbelian.CyclicImageComparison

/-!
# Strict action bound for the center-free PSL₂ branch

The pointwise omega kernel and the inner-action kernel agree on each
involution. Comparing these restricted kernels with the cyclic field outer
quotient bounds every elementary action image by two. A nontrivial element
of that image is an outer involution; marked root coordinates identify its
fixed points with solutions of a scalar-semilinear field equation. Above
field order four, twice this fixed-point order is strictly smaller than the
root-group order. The relative centralizer of the whole elementary subgroup
embeds in that fixed set.

This proves the quantitative helper in Aschbacher–Smith 16.5.1, printed
p.1194, for every n ≥ 3, including even n. The action image is the range of
the original Sylow conjugation homomorphism. No LocalAction or offender
premise is used. The existing Thompson and weak-closure deductions consume
this bound in the parent module.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G} {n : ℕ}

/-- On involutions, the actual omega projection detects innerness in any
specified PSL₂ model of the component. -/
theorem omegaProjection_eq_one_iff_model_inner {F : Type*} [Field F]
    (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (e : L ≃* PSL(2,F)) (t : T) (ht2 : t ^ 2 = 1) :
    omegaProjection h t = 1 ↔ ∃ g : PSL(2,F), modelAction h e t = MulAut.conj g := by
  have hq : omegaProjection h t = 1 ↔ omegaAction h t = 1 := by
    constructor
    · exact fun he => congrArg Subtype.val he
    · exact fun he => Subtype.ext he
  rw [hq, omegaAction_eq_one_iff_inner_psl2 h hZ hmodel t ht2]
  exact (MulAut.congr_inner_iff e
    (L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩)).symm

/-- The image of an elementary subgroup in the actual omega action has
order at most two, by comparison with the cyclic outer quotient. -/
theorem omega_image_card_le_two_psl2 {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (e : L ≃* PSL(2,F)) (A : Subgroup T) [IsElementaryAbelian 2 A] :
    Nat.card (A.map (omegaProjection h)) ≤ 2 := by
  have coverage (a : MulAut PSL(2,F)) :
      ∃ (g : PSL(2,F)) (σ : F ≃+* F), a = MulAut.conj g * Theory.PSL2.fieldAut σ := by
    exact BenderSuzuki.ZD.Linear.semilinear_coverage a
  let : IsCyclic (MulAut.Outer PSL(2,F)) :=
    Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage coverage
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(2,F))
  apply IsElementaryAbelian.card_map_le_of_cyclic_kernel_comparison A (omegaProjection h)
    (q.comp (modelAction h e))
  intro t ht
  rw [omegaProjection_eq_one_iff_model_inner h hZ hmodel e t
    (elemPow_eq_one_of_isElementaryAbelian t ht)]
  change (∃ g, modelAction h e t = MulAut.conj g) ↔ q (modelAction h e t) = 1
  constructor
  · rintro ⟨g, hg⟩
    exact (QuotientGroup.eq_one_iff _).mpr ⟨g, hg.symm⟩
  · intro hg
    obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp hg
    exact ⟨g, hg.symm⟩

/-- The strict numerical bound for the linear branch of Proposition 16.5.1.
Every nontrivial elementary restriction image loses more fixed points than
it gains in order. -/
theorem strictActionBound_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hn : 3 ≤ n) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n)) :
    StrictActionBound h := by
  classical
  have hsource := hmodel
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eL : L ≃* PSL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀
  let := componentSylow_elementary_psl2 h hZ hsource
  obtain ⟨e, b, hb⟩ := exists_root_coordinates h eL
  have hlarge : 4 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  intro A hA hne
  let := hA
  have hcard := omega_image_card_le_two_psl2 h hZ hsource e A
  have hex : ∃ t ∈ A, omegaProjection h t ≠ 1 := by
    by_contra! htriv
    apply hne
    apply eq_bot_iff.mpr
    rintro x ⟨t, ht, rfl⟩
    exact htriv t ht
  obtain ⟨t, ht, htn⟩ := hex
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have houter : ¬ ∃ g : PSL(2,F), modelAction h e t = MulAut.conj g := by
    rwa [← omegaProjection_eq_one_iff_model_inner h hZ hsource e t ht2]
  have hfixed := Theory.PSL2.RootSemilinear.fixed_card_lt hlarge (modelAction h e t)
    (modelAction_normalizes_root h e b hb t)
    (by rw [← map_pow, ht2, map_one]) houter
    (BenderSuzuki.ZD.Linear.semilinear_coverage (modelAction h e t))
  have hle := centralizer_card_le_root_fixed h e b hb A t ht
  have hcU := Nat.card_congr b.toEquiv
  calc
    Nat.card (componentOmegaInSylow T L ⊓ centralizer (A : Set T) : Subgroup T) *
        Nat.card (A.map (omegaProjection h)) ≤
      Nat.card {u : Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F //
        modelAction h e t u = u} * 2 := Nat.mul_le_mul hle hcard
    _ < Nat.card (componentOmegaInSylow T L) := by
      rw [hcU, Nat.mul_comm]
      exact hfixed

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
