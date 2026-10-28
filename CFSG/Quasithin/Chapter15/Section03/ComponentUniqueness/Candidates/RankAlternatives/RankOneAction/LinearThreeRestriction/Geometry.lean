module

public import Theory.GroupTheory.SolvableCyclicThreeCore
public import Theory.SpecificGroups.PSL3.QuadraticThreeSylow
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry

/-!
# Solvable Sylow overgroups in opposite-sign PSL₃

For |F| = 2ⁿ ≡ -1 modulo three, Sylow three-subgroups of PSL₃(F)
are cyclic. A solvable {2,3}-subgroup containing the full upper Sylow
therefore has nontrivial two-core: otherwise that nonabelian Sylow would
be abelian by the cyclic-core lemma. The common fixed space of the two-core
places its normalizer in a conjugate point or line parabolic. For n ≥ 2,
the actual SL₂ Levi quotient then puts the solvable overgroup in the Borel.

The imported geometry constructs the invariant subspace and the local
quotient; no parabolic placement or automorphism coverage is assumed.
Source: Aschbacher--Smith, 15.3.37, printed p.1135; the elementary matrix
geometry also supplies the placement in 1.3.4, printed p.511.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.LinearThreeGeometry

open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry

private theorem unipotent_nonabelian (F : Type*) [Field F] [Finite F] :
    ¬ IsMulCommutative (unipotent F) := by
  intro hc
  let _ := hc
  have h := mul_comm (unipotentEquiv F ⟨1, 0, 0⟩) (unipotentEquiv F ⟨0, 1, 0⟩)
  have h' : (⟨1, 0, 0⟩ : U F) * ⟨0, 1, 0⟩ = ⟨0, 1, 0⟩ * ⟨1, 0, 0⟩ :=
    (unipotentEquiv F).injective (by simpa only [map_mul] using h)
  have he : (1 : F) = 0 := by simpa using congrArg U.c h'
  exact one_ne_zero he

/-- Solvable {2,3}-overgroups of the full Sylow lie in its Borel for the
opposite-sign parameters larger than two. -/
theorem solvable_le_borel (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hmod : 2 ^ n % 3 = 2)
    (H : Subgroup PSL(3,F)) [Group.IsSolvable H]
    (hUH : unipotent F ≤ H)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    H ≤ borel F := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let N := (pCore 3 H).map H.subtype
  obtain ⟨T, hT⟩ := (pCore_isPGroup (p := 3) (G := H)).map H.subtype |>.exists_le_sylow
  let _ : IsCyclic T := Matrix.PSL3.QuadraticThreeSylow.sylow_three_isCyclic F 2
    (hF ▸ hmod) T
  let _ : IsCyclic N := Subgroup.isCyclic_of_le hT
  let e := (pCore 3 H).equivMapOfInjective H.subtype H.subtype_injective
  let _ : IsCyclic (pCore 3 H) := isCyclic_of_injective e.toMonoidHom e.injective
  have htwo : pCore 2 H ≠ ⊥ := by
    apply twoCore_ne_bot_of_solvable_cyclic_threeCore inferInstance hprime ((unipotent F).subgroupOf H)
      ((unipotent_isTwoGroup F hF).comap_of_injective H.subtype H.subtype_injective)
    intro hc
    let _ := hc
    apply unipotent_nonabelian F
    apply isMulCommutative_iff.mpr
    intro a b
    apply (subgroupOfEquivOfLe hUH).symm.injective
    simp only [map_mul, mul_comm]
  let Q := (pCore 2 H).map H.subtype
  have hQ : Q ≠ ⊥ := by
    intro he
    exact htwo (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp he)
  have hHQ : H ≤ normalizer (Q : Set PSL(3,F)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 H).le_normalizer_map H.subtype
  obtain ⟨g, point, hg⟩ :=
    CFSG.Quasithin.MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
      (by omega : 0 < n) hF (normalizer (Q : Set PSL(3,F)))
      ⟨Q, hQ, pCore_isPGroup.map H.subtype, rfl⟩
  exact CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.solvable_le_borel_of_conjugate_parabolic F hn hF H hUH
      ⟨g, point, (map_mono hHQ).trans hg⟩

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.LinearThreeGeometry
