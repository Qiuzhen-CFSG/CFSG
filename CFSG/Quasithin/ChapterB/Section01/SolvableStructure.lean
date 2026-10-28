module

public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.StableSaturation
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import Theory.Representation.BinaryPermutation
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.FieldTheory.Finiteness

/-!
# Solvable FF structure, cyclic-three conjugates and the stable-family correction

The imported `source_lemma_B_1_8_corrected` proves B.1.8(1)–(4) and the
generated-factor assertion of (5), with saturation giving the corrected
family formulation. `source_lemma_B_1_12` constructs the two internal products
and the transitive quotient-factor action from the original hypotheses.
Both assemble the proved factorization and offender theory without extra
structural premises. The independent obstruction below explains why the
last printed family equality must be corrected.

The last equality in printed B.1.8(5) is false for the definition of stability
in B.1.6. Here `G = S₃ × S₃` acts faithfully on the direct sum of its two
three-dimensional binary permutation modules. It is solvable and its actual
two-core is trivial. The coordinate transposition groups `B` and `C` are
minimal best offenders of weight six. Their product `A` is a best offender
of weight six, but is not minimal. Thus the stable family of all minimal best
offenders generates a subgroup containing `A` without containing `A` as a
member. In particular it is not the family of all best offenders contained
in the group it generates.

Finite enumeration checks the fixed-space cardinalities and faithfulness;
the finite vector-space cardinality formula yields their dimensions. The
best-offender test uses the possible subgroup orders 1, 2 and 4, and the
fact that a nontrivial subgroup of a faithful action has a proper fixed space.
Solvability and the trivial two-core use the actual symmetric group models.

The imported `IsStable.saturation_spec` supplies the corrected family
statement: all best offenders contained in the generated subgroup form a stable
saturation with the same generated subgroup. The original family need not equal
that saturation. Downward equal-weight closure is not strengthened to closure
under products.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed p. 70 (PDF p. 81), B.1.6–B.1.8.
-/

@[expose] public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableStableFamilyCounterexample
abbrev S := Equiv.Perm (Fin 3)
abbrev G := S × S
abbrev V := (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)
def representation : Representation (ZMod 2) G V where
  toFun g := (BinaryPermutation.representation (Fin 3) g.1).prodMap
    (BinaryPermutation.representation (Fin 3) g.2)
  map_one' := by ext v <;> rfl
  map_mul' g h := by ext v <;> rfl
private abbrev A : Subgroup G := SymmetricThreeProduct.borel
private def B : Subgroup G := SymmetricThreeProduct.pointStabilizer.prod ⊥
private def C : Subgroup G := (⊥ : Subgroup S).prod SymmetricThreeProduct.pointStabilizer
private instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.1 0 = 0 ∧ g.2 = 1))
private instance : DecidablePred (· ∈ C) := fun g => inferInstanceAs (Decidable (g.1 = 1 ∧ g.2 0 = 0))

private theorem card_B : Nat.card B = 2 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem card_C : Nat.card C = 2 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem card_A : Nat.card A = 4 := SymmetricThreeProduct.card_borel
private theorem faithful : Function.Injective representation := by
  have htest : ∀ g h : G, (∀ v : V, representation g v = representation h v) → g = h := by decide +kernel
  exact fun g h he => htest g h (fun v => congrArg (fun f : Module.End (ZMod 2) V => f v) he)

private theorem solvable : Group.IsSolvable G := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  infer_instance

private theorem twoCore : pCore 2 G = ⊥ := SymmetricThreeProduct.twoCore_eq_bot

private theorem B_le_A : B ≤ A := by
  intro g hg
  have he : g.2 = 1 := hg.2
  exact ⟨hg.1, he ▸ Subgroup.one_mem _⟩
private theorem C_le_A : C ≤ A := by
  intro g hg
  have he : g.1 = 1 := hg.1
  exact ⟨he ▸ Subgroup.one_mem _, hg.2⟩
private theorem A_le_sup : A ≤ B ⊔ C := by
  intro g hg
  have hB : (g.1, (1 : S)) ∈ B := ⟨hg.1, rfl⟩
  have hC : ((1 : S), g.2) ∈ C := ⟨rfl, hg.2⟩
  simpa using (B ⊔ C).mul_mem (Subgroup.mem_sup_left hB) (Subgroup.mem_sup_right hC)

private theorem elementary_A : IsElementaryTwo A := by
  refine ⟨fun h => ?_, ?_⟩
  · have := card_A; rw [h] at this; simp at this
  · exact { toIsMulCommutative := ⟨⟨by decide +kernel⟩⟩
            exponent_dvd_p := (Monoid.exponent_dvd_iff_forall_pow_eq_one).mpr (by decide +kernel) }

private def fixedTest (D : Subgroup G) (v : V) : Prop := ∀ g : G, g ∈ D → representation g v = v
private instance (D : Subgroup G) [DecidablePred (· ∈ D)] (v : V) : Decidable (fixedTest D v) :=
  inferInstanceAs (Decidable (∀ g : G, g ∈ D → representation g v = v))

private theorem fixed_dimension (D : Subgroup G) [DecidablePred (· ∈ D)] (d : ℕ)
    (h : Fintype.card {v : V // fixedTest D v} = 2 ^ d) :
    Module.finrank (ZMod 2) (fixedSpace representation D) = d := by
  let e : {v : V // fixedTest D v} ≃ fixedSpace representation D :=
    Equiv.subtypeEquivRight (fun v => by
      change (∀ g : G, g ∈ D → representation g v = v) ↔ ∀ g : D, representation g v = v
      exact ⟨fun h g => h g g.property, fun h g hg => h ⟨g, hg⟩⟩)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace representation D)
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, h] at he
  rw [hc] at he
  norm_num at he
  exact he.symm

private theorem dimension_A : Module.finrank (ZMod 2) (fixedSpace representation A) = 4 :=
  fixed_dimension A 4 (by decide +kernel)
private theorem dimension_B : Module.finrank (ZMod 2) (fixedSpace representation B) = 5 :=
  fixed_dimension B 5 (by decide +kernel)
private theorem dimension_C : Module.finrank (ZMod 2) (fixedSpace representation C) = 5 :=
  fixed_dimension C 5 (by decide +kernel)
private theorem dimension_V : Module.finrank (ZMod 2) V = 6 := by simp [V, Module.finrank_prod]
private theorem weight_A : weight representation A = 6 := by rw [weight, rank, card_A, dimension_A]; rfl
private theorem weight_B : weight representation B = 6 := by rw [weight, rank, card_B, dimension_B]; rfl
private theorem weight_C : weight representation C = 6 := by rw [weight, rank, card_C, dimension_C]; rfl

private theorem fixed_dimension_lt {D : Subgroup G} (hD : D ≠ ⊥) :
    Module.finrank (ZMod 2) (fixedSpace representation D) < 6 := by
  rw [← dimension_V]
  apply Submodule.finrank_lt
  intro htop
  apply hD
  apply le_bot_iff.mp
  intro g hg
  apply faithful
  apply LinearMap.ext
  intro v
  have hv : v ∈ fixedSpace representation D := by rw [htop]; trivial
  exact (hv ⟨g, hg⟩).trans (by simp)

private theorem best_A : IsBestOffender representation A := by
  refine ⟨elementary_A, fun D hD => ?_⟩
  have hd := Subgroup.card_dvd_of_le hD
  rw [card_A] at hd
  have cases : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 := by
    have := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show Nat.card D ∣ 2 ^ 2 from hd)
    obtain ⟨i, hi, he⟩ := this
    interval_cases i <;> simp_all
  rcases cases with h | h | h
  · have hb := Subgroup.card_eq_one.mp h
    rw [hb, weight_bot, weight_A, dimension_V]
  · have hn : D ≠ ⊥ := by intro he; rw [he] at h; simp at h
    have hf := fixed_dimension_lt hn
    rw [weight, rank, h, weight_A]
    norm_num
    omega
  · have he := Subgroup.eq_of_le_of_card_ge hD (by rw [card_A, h] : Nat.card A ≤ Nat.card D)
    rw [he]

private theorem elementary_B : IsElementaryTwo B :=
  elementary_A.of_le B_le_A (by intro h; have := card_B; rw [h] at this; simp at this)
private theorem elementary_C : IsElementaryTwo C :=
  elementary_A.of_le C_le_A (by intro h; have := card_C; rw [h] at this; simp at this)
private theorem best_B : IsBestOffender representation B :=
  best_A.of_equalWeightLE representation elementary_B ⟨B_le_A, by rw [weight_A, weight_B]⟩
private theorem best_C : IsBestOffender representation C :=
  best_A.of_equalWeightLE representation elementary_C ⟨C_le_A, by rw [weight_A, weight_C]⟩

private theorem minimal_of_card_two {D : Subgroup G} (hD : IsBestOffender representation D)
    (hc : Nat.card D = 2) : IsMinimalBestOffender representation D := by
  refine ⟨hD, fun E hE hED => ?_⟩
  apply Subgroup.eq_of_le_of_card_ge hED.1
  rw [hc]
  have hne : Nat.card E ≠ 1 := fun h => hE.1.1 (Subgroup.card_eq_one.mp h)
  have hp := Nat.card_pos (α := E)
  omega

private theorem minimal_B : IsMinimalBestOffender representation B := minimal_of_card_two best_B card_B
private theorem minimal_C : IsMinimalBestOffender representation C := minimal_of_card_two best_C card_C

private theorem not_minimal_A : ¬ IsMinimalBestOffender representation A := by
  intro h
  have he := h.2 B best_B ⟨B_le_A, by rw [weight_A, weight_B]⟩
  have hc := card_B
  rw [he, card_A] at hc
  contradiction

/-- A finite solvable group with trivial two-core and a faithful binary FF-module
for which the second assertion of source B.1.8(5) fails. All group, module and
family witnesses are constructed in the proof. -/
theorem source_obstruction_B_1_8_5 :
    Group.IsSolvable G ∧ pCore 2 G = ⊥ ∧ Function.Injective representation ∧ IsFFModule representation ∧
      ∃ P : Set (Subgroup G), IsStable representation P ∧
        P ≠ {D | IsBestOffender representation D ∧ D ≤ generatedBy P ⊤} := by
  have hff : IsFFModule representation := ⟨A, best_A.isOffender representation⟩
  refine ⟨solvable, twoCore, faithful, hff, {D | IsMinimalBestOffender representation D},
    isStable_minimalBestOffenders representation hff, ?_⟩
  intro he
  apply not_minimal_A
  rw [Set.ext_iff] at he
  apply (he A).mpr
  refine ⟨best_A, A_le_sup.trans (sup_le ?_ ?_)⟩
  · exact le_iSup_of_le B (le_iSup_of_le ⟨minimal_B, le_top⟩ le_rfl)
  · exact le_iSup_of_le C (le_iSup_of_le ⟨minimal_C, le_top⟩ le_rfl)

/-- Even under the solvable FF hypotheses, saturation can strictly enlarge a
stable family while preserving its generated subgroup. -/
theorem source_obstruction_saturation :
    Group.IsSolvable G ∧ pCore 2 G = ⊥ ∧ Function.Injective representation ∧
      IsFFModule representation ∧ ∃ P : Set (Subgroup G),
        IsStable representation P ∧ P ⊂ saturation representation P ∧
          IsStable representation (saturation representation P) ∧
          generatedBy (saturation representation P) ⊤ = generatedBy P ⊤ := by
  obtain ⟨hs, hc, hf, hff, P, hP, hne⟩ := source_obstruction_B_1_8_5
  obtain ⟨hle, hstable, hgen⟩ := hP.saturation_spec representation
  exact ⟨hs, hc, hf, hff, P, hP, Set.ssubset_iff_subset_ne.mpr ⟨hle, hne⟩,
    hstable, hgen⟩
end CFSG.Quasithin.ChapterB.SolvableStableFamilyCounterexample
