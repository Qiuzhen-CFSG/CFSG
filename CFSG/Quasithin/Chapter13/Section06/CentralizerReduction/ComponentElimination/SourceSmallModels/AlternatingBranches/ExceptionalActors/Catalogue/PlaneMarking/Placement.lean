module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.Coordinates
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Literal permutation placement of the order-72 stabilizer

An order-72 subgroup of A₇ cannot fix a point, since that would give an
index-five subgroup of A₆. Its orbits therefore have size at most four.
A Sylow two-subgroup supplies a four-cycle, hence a four-point orbit.
Relabelling that orbit gives containment in the four-plus-three stabilizer;
equality follows from the common order 72.

The orbit argument is adapted from Chapter1's Seven/PermutationAction,
with narrow lower-layer imports. No chapter classification result is used.
Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Equiv MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking
private theorem no_fixed_point (H : Subgroup A7) (hc : Nat.card H = 72) (a : Fin 7)
    (ha : ∀ g ∈ H, (g : Perm (Fin 7)) a = a) : False := by
  classical
  let s : Finset (Fin 7) := Finset.univ.erase a
  have hs : Nat.card s = 6 := by simp [s]
  have hs' : Nontrivial s := by
    apply (Fintype.one_lt_card_iff_nontrivial).mp
    simpa only [Nat.card_eq_fintype_card] using (show 1 < Nat.card s by omega)
  let f := alternatingGroup.ofSubtype s
  have hf : Function.Injective f := alternatingGroup.ofSubtype_injective
  have hH : H ≤ f.range := by
    intro g hg
    apply (alternatingGroup.mem_range_ofSubtype_iff s g).mpr
    intro b hb
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst b
    exact (Perm.mem_support.mp hb) (ha g hg)
  let K := H.comap f
  have hK : Nat.card K = 72 := by
    rw [← card_map_of_injective hf, map_comap_eq_self hH, hc]
  have hA : Nat.card (alternatingGroup s) = 360 := by
    rw [nat_card_alternatingGroup, hs]
    norm_num
  have hi : K.index = 5 := by
    have h := K.card_mul_index
    rw [hK, hA] at h
    omega
  let _ : IsSimpleGroup (alternatingGroup s) := alternatingGroup.isSimpleGroup (by simpa only [← Nat.card_eq_fintype_card, hs] using (by decide : 5 ≤ 6))
  have ht : K = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt K (by
    rw [hi, hA]
    decide)
  rw [ht, card_top, hA] at hK
  omega

private theorem orbit_card_le_four (H : Subgroup A7) (hc : Nat.card H = 72) (a : Fin 7) :
    Nat.card (orbit H a) ≤ 4 := by
  classical
  have hle : Nat.card (orbit H a) ≤ 7 := (Set.ncard_le_card _).trans_eq (by simp)
  have hd : Nat.card (orbit H a) ∣ 72 := by
    rw [Nat.card_congr (orbitEquivQuotientStabilizer H a)]
    exact hc ▸ (stabilizer H a).index_dvd_card
  have hn : Nat.card (orbit H a) ≠ 6 := by
    intro hn
    have hcomp : (orbit H a)ᶜ.ncard = 1 := by
      rw [Set.ncard_compl]
      change Nat.card (Fin 7) - Nat.card (orbit H a) = 1
      rw [hn]
      norm_num
    obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp hcomp
    have hb' : b ∉ orbit H a := by
      change b ∈ (orbit H a)ᶜ
      simp [hb]
    apply no_fixed_point H hc b
    intro g hg
    have hgb : (⟨g, hg⟩ : H) • b ∉ orbit H a := by
      intro h
      have h' := mapsTo_smul_orbit (⟨g, hg⟩ : H)⁻¹ a h
      apply hb'
      change (⟨g, hg⟩ : H)⁻¹ • ((⟨g, hg⟩ : H) • b) ∈ orbit H a at h'
      simpa only [inv_smul_smul] using h'
    have : (g : Perm (Fin 7)) b ∈ (orbit H a)ᶜ := hgb
    simpa [hb] using this
  interval_cases hc' : Nat.card (orbit H a) <;> norm_num at *

private def fourCycle : A7 :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by
    simp only [Perm.mem_alternatingGroup, map_mul]
    decide⟩

private theorem fourCycle_order : orderOf fourCycle = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

private theorem large_orbit (P : Sylow 2 A7) (H : Subgroup A7) (hPH : (P : Subgroup A7) ≤ H) :
    ∃ a : Fin 7, 4 ≤ Nat.card (orbit H a) := by
  have hp : IsPGroup 2 (zpowers fourCycle) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, fourCycle_order]
    rfl : Nat.card (zpowers fourCycle) = 2 ^ 2)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_smul_eq A7 Q P
  have hq : MulAut.conj g fourCycle ∈ P := by
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul fourCycle (MulAut.conj g) (Q : Subgroup A7)
      (hQ (mem_zpowers fourCycle))
  let p : H := ⟨MulAut.conj g fourCycle, hPH hq⟩
  have ht : ∀ i : Fin 4, ((fourCycle ^ i.val : A7) : Perm (Fin 7)) 0 = i.castLE (by decide) := by
    decide
  let f : Fin 4 → orbit H ((g : Perm (Fin 7)) 0) := fun i =>
    ⟨(g : Perm (Fin 7)) (i.castLE (by decide)), by
      refine ⟨p ^ i.val, ?_⟩
      change ((MulAut.conj g fourCycle) ^ i.val : A7).val ((g : Perm (Fin 7)) 0) = _
      rw [← map_pow]
      change (g.val * (fourCycle ^ i.val).val * g.val⁻¹) (g.val 0) = _
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, ht]⟩
  refine ⟨g.val 0, ?_⟩
  have hf : Function.Injective f := by
    intro i j he
    have hij := g.val.injective (congrArg Subtype.val he)
    exact Fin.ext (congrArg (fun x : Fin 7 => x.val) hij)
  simpa using Nat.card_le_card_of_injective f hf


/-- The literal even four-plus-three stabilizer has order 72. -/
theorem blockStabilizer_card : Nat.card blockStabilizer = 72 := by
  rw [← Subgroup.card_map_of_injective (K := blockStabilizer) (f := (alternatingGroup (Fin 7)).subtype)
    (alternatingGroup (Fin 7)).subtype_injective]
  have he : blockStabilizer.map (alternatingGroup (Fin 7)).subtype =
      alternatingGroup (Fin 7) ⊓ normalizer
        (AlternatingSeven.ThreeResidualLocals.naturalFour : Set (Perm (Fin 7))) := by
    rw [AlternatingSeven.ThreeResidualLocals.naturalFour_normalizer_eq_fourPointSetwiseStabilizer,
      blockStabilizer, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  rw [he]
  exact AlternatingSeven.ThreeResidualLocals.alternating_normalizer_naturalFour_card

private theorem exists_orbit_relabelling (H : Subgroup A7) (a : Fin 7)
    (ha : Nat.card (orbit H a) = 4) :
    ∃ g : Perm (Fin 7), ∀ x, g x ∈ orbit H a ↔ x.val < 4 := by
  classical
  let b : Set.powersetCard (Fin 7) 4 := ⟨{0,1,2,3}, by change ({0,1,2,3} : Finset (Fin 7)).card = 4; decide⟩
  let t : Set.powersetCard (Fin 7) 4 := ⟨(orbit H a).toFinset, by
    change (orbit H a).toFinset.card = 4
    rw [← Set.ncard_eq_toFinset_card']; exact ha⟩
  let : IsPretransitive (Perm (Fin 7)) (Set.powersetCard (Fin 7) 4) :=
    Set.powersetCard.isPretransitive
  obtain ⟨g, hg⟩ := exists_smul_eq (Perm (Fin 7)) b t
  refine ⟨g, fun x => ?_⟩
  have hm : g x ∈ t.val ↔ x ∈ b.val := by
    rw [← hg, Set.powersetCard.coe_smul]
    change g • x ∈ g • b.val ↔ x ∈ b.val
    simp only [Finset.smul_mem_smul_finset_iff]
  have hb : x ∈ b.val ↔ x.val < 4 := by
    change x ∈ ({0,1,2,3} : Finset (Fin 7)) ↔ x.val < 4
    fin_cases x <;> decide
  simpa only [t, Set.mem_toFinset, hb] using hm

/-- Order and the actual Sylow inclusion identify the subgroup by a
permutation-induced automorphism, including the marking on all seven letters. -/
theorem exists_block_marking_of_card (H : Subgroup A7) (hH : Nat.card H = 72)
    (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ H) :
    ∃ g : Perm (Fin 7), H = blockStabilizer.map (relabelling g).toMonoidHom := by
  obtain ⟨a, ha⟩ := large_orbit S H hS
  have hc : Nat.card (orbit H a) = 4 := le_antisymm (orbit_card_le_four H hH a) ha
  obtain ⟨g, hg⟩ := exists_orbit_relabelling H a hc
  refine ⟨g, ?_⟩
  have hle : H ≤ blockStabilizer.map (relabelling g).toMonoidHom := by
    intro h hh
    refine ⟨(relabelling g).symm h, ?_, (relabelling g).apply_symm_apply h⟩
    change ∀ x : Fin 7, x.val < 4 ↔ (g.symm (h.val (g x))).val < 4
    intro x
    have ho (y : Fin 7) : h.val y ∈ orbit H a ↔ y ∈ orbit H a := by
      change (⟨h, hh⟩ : H) • y ∈ orbit H a ↔ y ∈ orbit H a
      constructor
      · intro hy
        have hi := mapsTo_smul_orbit (⟨h, hh⟩ : H)⁻¹ a hy
        simpa only [inv_smul_smul] using hi
      · exact fun hy => mapsTo_smul_orbit (⟨h, hh⟩ : H) a hy
    rw [← hg, ← hg, g.apply_symm_apply, ho]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (relabelling g).injective, blockStabilizer_card, hH]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking
