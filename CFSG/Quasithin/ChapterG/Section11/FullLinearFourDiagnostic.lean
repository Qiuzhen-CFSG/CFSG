module
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import Theory.Representation.BinaryNaturalDual.FourActors.Parameters
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# The exceptional degree-four exchanged model

The actual automorphism group of GL₄(2), identified with S₈ by the existing
exceptional comparison, acts on its natural module plus its dual. Its
four-pair elementary actor A₁ has order sixteen and a one-dimensional fixed
space. The distinguished inner transvection has rank two on the sum, and
the same fixed point lies in its moved space. The binary-tree Sylow normalizes
A₁ and fixes that point. Thus both additional G.11.1 predicates hold literally
on this eight-dimensional model. Its odd-prime ranks are at most two, while
the extra small-actor bound used in the terminal G.10 repair fails.

The proofs use the published eight-point comparison, the explicit A₁ matrices,
and the binary-tree Sylow, with finite checks of at most seven by sixteen
actor conjugates. These are diagnostics for the exceptional GL₄(2) row in
`ExchangedModels`, not an exhaustive G.11 classifier or a Lean counterexample
to the full theorem: the original G.10 hypothesis, the K-group property, and
the exclusion of all thirteen outputs are not asserted here.

Source: Aschbacher--Smith G.10.15(3), G.11.1--2 and H.9.3(5), printed
pp.363--364,391. The small-actor repair is developed separately in
Chapter14's `ComponentCatalogueExchangedCentralKernelFullLinearFour`.
-/

@[expose] public noncomputable section

open Subgroup Module Representation
open BinaryNaturalDual BinaryNaturalDual.FourActors
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.FullLinearFourDiagnostic
noncomputable abbrev coordinates : CoordinateAction 4 :=
  BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl rfl)
noncomputable abbrev rho := coordinates.representation
local instance : Finite M := Finite.of_injective permutationEquiv permutationEquiv.injective
noncomputable def point : V :=
  ((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0) +
    rho transposition ((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0)

theorem dimension : finrank (ZMod 2) V = 8 := by
  simp [V,CoordinateSpace,BinaryNaturalDual.Space,BinaryLinear.OuterCyclic.Space]

theorem point_ne_zero : point ≠ 0 := by
  have hz := outer_natural coordinates transposition transposition_outer
    (((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0) : V)
    ((mem_naturalSummand _).mpr rfl)
  have he := (mem_dualSummand _).mp hz
  intro hp
  have hh := congrArg (fun w : V => w.1 0) hp
  change (1 : ZMod 2) + (rho transposition ((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0)).1 0 = 0 at hh
  change (rho transposition ((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0)).1 = 0 at he
  rw [he] at hh
  norm_num at hh

theorem fixed_line : actorFixed coordinates A1 = Submodule.span (ZMod 2) {point} :=
  Parameters.A1_fixed_line coordinates

theorem rank_r : finrank (ZMod 2) (RankTwo.movedSpace rho r) = 2 := by
  have hk := (Parameters.A1_parameters coordinates).2.2
  have hd := (rho r - LinearMap.id).finrank_range_add_finrank_ker
  have hker : (rho r - LinearMap.id).ker = BinaryNaturalDual.fixedSpace (action coordinates r) := rfl
  rw [hker,hk,dimension] at hd
  change finrank (ZMod 2) (LinearMap.range (rho r - LinearMap.id)) = 2
  exact Nat.add_right_cancel (show finrank (ZMod 2) (LinearMap.range (rho r - LinearMap.id)) + 6 = 2 + 6 from hd)

theorem point_mem_moved : point ∈ RankTwo.movedSpace rho r := by
  let u : V := ((![1,1,0,0] : BinaryNaturalDual.FourActors.X),0)
  let w : V := ((![0,0,1,0] : BinaryNaturalDual.FourActors.X),0)
  have hru : rho r w - w = u := by
    rw [A1Module.r_eq,coordinates.on_inner,naturalDualRepresentation_apply]
    apply Prod.ext
    · change (A1Module.matrix 7).mulVec (![0,0,1,0] : BinaryNaturalDual.FourActors.X) -
        ![0,0,1,0] = ![1,1,0,0]
      decide +kernel
    · simp [w,u]
  have hu : u ∈ RankTwo.movedSpace rho r := ⟨w,hru⟩
  have hrA : r ∈ A1 := by
    rw [A1Module.r_eq]
    exact (A1Module.conj_linear_mem 7).1
  have hc : r * transposition = transposition * r :=
    congrArg Subtype.val (mul_comm (⟨r,hrA⟩ : A1) ⟨transposition,transposition_mem_A1⟩)
  have hxu : rho transposition u ∈ RankTwo.movedSpace rho r := by
    refine ⟨rho transposition w,?_⟩
    change rho r (rho transposition w) - rho transposition w = rho transposition u
    rw [← Module.End.mul_apply,← map_mul,hc,map_mul,Module.End.mul_apply,← map_sub,hru]
  exact (RankTwo.movedSpace rho r).add_mem hu hxu

theorem low_rank_witness : LowRankWitness rho point A1 := by
  refine ⟨r,?_,rank_r.le,point_mem_moved⟩
  rw [A1Module.r_eq]
  exact (A1Module.conj_linear_mem 7).1

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem pairs_le_tree : permutationA1 ≤ treeGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact treeGenerator_mem 0
  · exact treeGenerator_mem 1
  · exact treeGenerator_mem 2
  · exact treeGenerator_mem 3

private theorem tree_normalizes_pairs : treeGroup ≤ normalizer (permutationA1 : Set S) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  have hc : ∀ (j : Fin 7) (t : A1Module.Bits), ∃ u : A1Module.Bits,
      treeGenerator j * A1Module.pairPerm t * (treeGenerator j)⁻¹ = A1Module.pairPerm u := by
    decide +kernel
  have hi : ∀ j : Fin 7, (treeGenerator j)⁻¹ = treeGenerator j := by decide +kernel
  have hmap (g : S) (hg : g ∈ permutationA1) :
      treeGenerator j * g * (treeGenerator j)⁻¹ ∈ permutationA1 := by
    rw [A1Module.pairs_range] at hg ⊢
    obtain ⟨t,rfl⟩ := hg
    obtain ⟨u,hu⟩ := hc j t.toAdd
    exact ⟨Multiplicative.ofAdd u,hu.symm⟩
  change treeGenerator j ∈ normalizer (permutationA1 : Set S)
  rw [mem_normalizer_iff]
  intro g
  refine ⟨hmap g,fun hg => ?_⟩
  have hh := hmap _ hg
  rw [hi] at hh
  have hsq : treeGenerator j * treeGenerator j = 1 := inv_eq_iff_mul_eq_one.mp (hi j)
  have he : treeGenerator j * (treeGenerator j * g * treeGenerator j) * treeGenerator j = g := by
    calc
      _ = (treeGenerator j * treeGenerator j) * g * (treeGenerator j * treeGenerator j) := by group
      _ = g := by rw [hsq,one_mul,mul_one]
  exact he ▸ hh

noncomputable def pointSylow : Sylow 2 M :=
  treeSylow.mapSurjective (f := permutationEquiv.symm.toMonoidHom) permutationEquiv.symm.surjective

private theorem sylow_mem (g : M) : g ∈ (pointSylow : Subgroup M) ↔
    permutationEquiv g ∈ treeGroup := by
  change g ∈ treeGroup.map permutationEquiv.symm.toMonoidHom ↔ _
  simpa only [MulEquiv.symm_symm] using (mem_map_equiv (f := permutationEquiv.symm) (K := treeGroup) (x := g))

private theorem actor_le_sylow : A1 ≤ (pointSylow : Subgroup M) := by
  intro g hg
  exact (sylow_mem g).mpr (pairs_le_tree hg)

private theorem sylow_normalizes : (pointSylow : Subgroup M) ≤ normalizer (A1 : Set M) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro a
  change permutationEquiv a ∈ permutationA1 ↔
    permutationEquiv (g * a * g⁻¹) ∈ permutationA1
  rw [map_mul,map_mul,map_inv]
  exact (mem_normalizer_iff.mp (tree_normalizes_pairs ((sylow_mem g).mp hg))) _

private theorem point_fixed (a : M) (ha : a ∈ A1) : rho a point = point := by
  have hv : point ∈ actorFixed coordinates A1 := by
    rw [fixed_line]
    exact Submodule.mem_span_singleton_self _
  exact hv ⟨a,ha⟩

private theorem sylow_fixes_point : (pointSylow : Subgroup M) ≤ Section10.pointCentralizer rho point := by
  intro g hg
  have hmem : rho g point ∈ actorFixed coordinates A1 := by
    intro a
    have ha := a.property
    have hh : g⁻¹ * a * g ∈ A1 := by
      have hn := (normalizer (A1 : Set M)).inv_mem (sylow_normalizes hg)
      simpa only [inv_inv] using (mem_normalizer_iff.mp hn a).mp ha
    have he : a * g = g * (g⁻¹ * a * g) := by group
    change rho a (rho g point) = rho g point
    rw [← Module.End.mul_apply,← map_mul,he,map_mul,Module.End.mul_apply,point_fixed _ hh]
  rw [fixed_line,Submodule.mem_span_singleton] at hmem
  obtain ⟨c,hc⟩ := hmem
  have hcases : c = 0 ∨ c = 1 := by exact (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hcases with rfl | rfl
  · have hh : rho g point = 0 := by simpa only [zero_smul] using hc.symm
    exact (point_ne_zero ((rho.apply_bijective g).injective (hh.trans (map_zero _).symm))).elim
  · change rho g point = point
    simpa only [one_smul] using hc.symm

/-- Relative normality holds for the actual actor and a Sylow of the full
model group, and that Sylow fixes the same marked point. -/
theorem normal_sylow : NormalSylow rho point A1 :=
  ⟨pointSylow,sylow_fixes_point,actor_le_sylow,
    (normal_subgroupOf_iff_le_normalizer actor_le_sylow).mpr sylow_normalizes⟩

/-- The concrete model is S8, and its actor has order sixteen. -/
theorem group_and_actor_orders : Nat.card M = 40320 ∧ Nat.card A1 = 16 := by
  refine ⟨?_,PermutationCatalogue.A1_card⟩
  rw [Nat.card_congr permutationEquiv.toEquiv,Nat.card_perm,Nat.card_fin]
  decide

/-- The extra small-actor premise used in the terminal G.10 repair fails
on this actual eight-dimensional low-rank model. -/
theorem not_small_actor : ¬ finrank (ZMod 2) (Additive A1) ≤ finrank (ZMod 2) V / 2 - 1 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A1)
  rw [Nat.card_zmod,show Nat.card (Additive A1) = 16 from PermutationCatalogue.A1_card] at hc
  have hr : finrank (ZMod 2) (Additive A1) = 4 :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  rw [hr,dimension]
  decide

/-- The full group satisfies the odd-prime-rank part of SQTK. The K-group
assertion is not included in this diagnostic. -/
theorem strongly_quasithin : IsStronglyQuasithin M := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply Theory.GroupTheory.primeRank_le_of_prime_pow_not_dvd (n := 2)
  rw [group_and_actor_orders.1]
  intro hd
  have hb : p ^ 3 ≤ 40320 := Nat.le_of_dvd (by decide) hd
  have hlt : p < 35 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_left (show 35 ≤ p from by omega) 3
    norm_num at hpow
    omega
  exact (by decide +kernel : ∀ p : Fin 35, p.val.Prime → Odd p.val →
    ¬ p.val ^ 3 ∣ 40320) ⟨p,hlt⟩ hp ho hd

/-- Both extra G.11 inputs are realized on the same marked S8 action.
This applies the original source predicates, rather than a weakened substitute. -/
theorem extra_source_inputs : point ≠ 0 ∧ LowRankWitness rho point A1 ∧
    NormalSylow rho point A1 ∧
    actorFixed coordinates A1 = Submodule.span (ZMod 2) {point} :=
  ⟨point_ne_zero,low_rank_witness,normal_sylow,fixed_line⟩

end CFSG.Quasithin.ChapterG.Section11.FullLinearFourDiagnostic
