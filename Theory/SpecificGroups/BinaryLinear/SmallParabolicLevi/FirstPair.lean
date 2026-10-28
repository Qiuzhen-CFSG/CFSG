module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Adjacent

/-!
# The first adjacent pair in a binary flag

The Sylow-overgroup lattice identifies the join of two minimal parabolics
with deletion of their two cuts. At the first pair, in dimensions four
and five, the quotient by the two-core is the actual SL₃(2). In dimension
four restriction to the hyperplane gives GL₃(2) times the trivial GL₁(2);
in dimension five the existing marked block-diagonal quotient applies.

The full flag is self-normalizing, since its invariant cuts are uniquely
determined. Together these results retain the original basis and quotient
maps for the rank-two construction in Aschbacher--Smith, 15.1.29,
printed pp.1103--1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.SmallParabolicLevi

namespace BinaryLinear.SylowFlagOvergroups
theorem pair_eq_cutStabilizer {m : ℕ} (S : Sylow 2 (LinearGroup (m + 1)))
    (b : Basis m) (hb : (S : Subgroup _) = cutStabilizer b Set.univ) (i j : Fin m) :
    minimalParabolic b i ⊔ minimalParabolic b j = cutStabilizer b {i,j}ᶜ := by
  obtain ⟨cuts,hcuts⟩ := overgroup_eq_cutStabilizer S b hb
    (minimalParabolic b i ⊔ minimalParabolic b j)
    ((fullFlag_covBy_minimalParabolic S b hb i).le.trans le_sup_left)
  have hi : cuts ⊆ {i}ᶜ := (cutStabilizer_le_iff b _ _).mp
    (show minimalParabolic b i ≤ cutStabilizer b cuts from le_sup_left.trans_eq hcuts)
  have hj : cuts ⊆ {j}ᶜ := (cutStabilizer_le_iff b _ _).mp
    (show minimalParabolic b j ≤ cutStabilizer b cuts from le_sup_right.trans_eq hcuts)
  apply le_antisymm
  · exact sup_le ((cutStabilizer_le_iff b _ _).mpr (by simp))
      ((cutStabilizer_le_iff b _ _).mpr (by simp))
  · rw [hcuts]
    exact (cutStabilizer_le_iff b _ _).mpr (by intro k hk; simpa using ⟨hi hk,hj hk⟩)
end BinaryLinear.SylowFlagOvergroups

namespace BinaryLinear.OrderedResidualConjugators
private theorem linear_one_subsingleton : Subsingleton (LinearGroup 1) := by
  let : Finite (LinearGroup 1) := Finite.of_equiv _ (matrixEquivLinear 1).toEquiv
  apply Finite.card_le_one_iff_subsingleton.mp
  have hc : Nat.card (LinearGroup 1) = 1 := by
    rw [← Nat.card_congr (matrixEquivLinear 1).toEquiv, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  omega

noncomputable def four_head_quotient (b : Basis 3) :
    (cutStabilizer b ({0,1} : Set (Fin 3))ᶜ ⧸
      pCore 2 (cutStabilizer b ({0,1} : Set (Fin 3))ᶜ)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  have he : cutStabilizer b ({0,1} : Set (Fin 3))ᶜ = parabolic (cutSpace b 2) := by
    ext g
    rw [mem_cutStabilizer]
    constructor
    · exact fun h => h 2 (by decide)
    · intro h i hi
      have hi2 : i = 2 := by fin_cases i <;> simp_all
      subst i
      exact h
  let W := cutSpace b 2
  have hW : Module.finrank (ZMod 2) W = 3 := cutSpace_finrank b 2
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 1 := by
    have hh := W.finrank_quotient_add_finrank
    have hh' : Module.finrank (ZMod 2) (Space 4 ⧸ W) + 3 = 4 := by
      simpa only [hW,Module.finrank_fin_fun] using hh
    omega
  let c : W ≃ₗ[ZMod 2] Space 3 := LinearEquiv.ofFinrankEq W (Space 3) (by simpa using hW)
  let q : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 1 := LinearEquiv.ofFinrankEq (Space 4 ⧸ W) (Space 1) (by simpa using hQ)
  let e := quotientTwoCoreEquivOfCoordinates W c q
  let f : LinearGroup 3 × LinearGroup 1 →* LinearGroup 3 := MonoidHom.fst _ _
  have hf : Function.Bijective f := by
    let := linear_one_subsingleton
    exact ⟨fun x y h => Prod.ext h (Subsingleton.elim _ _),fun x => ⟨(x,1),rfl⟩⟩
  exact (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr he)
    (pCore_map_iso 2 _)).trans (e.trans ((MulEquiv.ofBijective f hf).trans (slEquivLinear 3).symm))

theorem head_quotient {m : ℕ} (hm : m = 3 ∨ m = 4) (b : Basis m) :
    Nonempty ((cutStabilizer b ({⟨0,by omega⟩,⟨1,by omega⟩} : Set (Fin m))ᶜ ⧸
      pCore 2 (cutStabilizer b ({⟨0,by omega⟩,⟨1,by omega⟩} : Set (Fin m))ᶜ)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rcases hm with rfl | rfl
  · exact ⟨four_head_quotient b⟩
  · exact ⟨TwoNodes.adjacentQuotientEquiv b 0⟩
end BinaryLinear.OrderedResidualConjugators

namespace BinaryLinear.SylowFlagOvergroups

theorem normalizer_fullFlag_eq {m : ℕ} (b : Basis m) :
    normalizer (cutStabilizer b Set.univ : Set (LinearGroup (m + 1))) =
      cutStabilizer b Set.univ := by
  apply le_antisymm _ (cutStabilizer b Set.univ).le_normalizer
  intro g hg
  have he := mem_normalizer_iff_map_conj_eq.mp hg
  change (cutStabilizer b Set.univ).map (MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ at he
  rw [cutStabilizer_map_conj] at he
  rw [mem_cutStabilizer]
  intro i _ v
  have hspace : cutSpace b i = cutSpace (b.map g) i :=
    (cutSpace_eq_of_fullFlag_le b (b.map g) Set.univ he.symm.le i (Set.mem_univ i)).symm
  rw [cutSpace_map] at hspace
  constructor
  · intro hv
    rw [hspace] at hv
    obtain ⟨w,hw,he⟩ := hv
    exact g.injective he ▸ hw
  · intro hv
    rw [hspace]
    exact ⟨v,hv,rfl⟩
end BinaryLinear.SylowFlagOvergroups
