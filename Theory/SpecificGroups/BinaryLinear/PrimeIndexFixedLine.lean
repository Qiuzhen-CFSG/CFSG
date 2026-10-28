module
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
/-!
# Prime-index Sylow overgroups and a fixed line in binary linear groups

The flag-overgroup theorem puts every prime-index overgroup of a full Sylow
2-subgroup above a minimal parabolic of index three, forcing that prime to
be three. In dimensions three through five, an order-three subgroup having
only a fixed line forces dimension three. Orbit congruences exclude dimension
four. In dimension five a minimal parabolic preserves either the cuts of
dimensions 1 and 2 or those of dimensions 3 and 4. The fixed-space counts
modulo three cannot increase along either such pair when the total fixed
space has order two.

Source application: Aschbacher–Smith, 12.2.23, printed p.803. This supplies
the rank-one numerical step on the actual natural action.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
open OuterCyclic InvariantNodeActions
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

theorem prime_sylow_overgroup_index {m p : ℕ} (hp : p.Prime)
    (S : Sylow 2 (LinearGroup (m+1))) (B : Subgroup (LinearGroup (m+1)))
    (hSB : (S : Subgroup _) ≤ B) (hi : (S : Subgroup _).relIndex B = p) : p = 3 := by
  obtain ⟨b, cuts, hb, hB⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S B hSB
  have hn : cuts ≠ Set.univ := by
    intro he
    have hBS : B = S := by rw [hB, he, hb]
    rw [hBS, relIndex_self] at hi
    exact hp.ne_one hi.symm
  have hnsub : ¬ Set.univ ⊆ cuts := fun hh => hn (Set.Subset.antisymm (Set.subset_univ _) hh)
  obtain ⟨i, _, hiC⟩ := Set.not_subset.mp hnsub
  have hnode : minimalParabolic b i ≤ B := by
    rw [hB]
    exact (cutStabilizer_le_iff b _ _).mpr (fun j hj hji => hiC (hji ▸ hj))
  have hSnode : (S : Subgroup _) ≤ minimalParabolic b i := by
    rw [hb]
    exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
  have hdiv := dvd_of_mul_right_eq _ (relIndex_mul_relIndex (S : Subgroup _)
    (minimalParabolic b i) B hSnode hnode)
  rw [hi, hb, CubicSylowGeneration.minimalParabolic_index] at hdiv
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdiv).symm


private theorem prime_index_node {m p : ℕ} (hp : p.Prime)
    (S : Sylow 2 (LinearGroup (m+1))) (B : Subgroup (LinearGroup (m+1)))
    (hSB : (S : Subgroup _) ≤ B) (hi : (S : Subgroup _).relIndex B = p) :
    ∃ (b : Basis m) (i : Fin m), (S : Subgroup _) = cutStabilizer b Set.univ ∧
      B = minimalParabolic b i := by
  have hp3 := prime_sylow_overgroup_index hp S B hSB hi
  obtain ⟨b, cuts, hb, hB⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S B hSB
  have hnsub : ¬ Set.univ ⊆ cuts := by
    intro hh
    have he : cuts = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hh
    have hBS : B = S := by rw [hB, he, hb]
    rw [hBS, relIndex_self] at hi
    exact hp.ne_one hi.symm
  obtain ⟨i, _, hiC⟩ := Set.not_subset.mp hnsub
  have hn : minimalParabolic b i ≤ B := by
    rw [hB]
    exact (cutStabilizer_le_iff b _ _).mpr (fun j hj hji => hiC (hji ▸ hj))
  have hSn : (S : Subgroup _) ≤ minimalParabolic b i := by
    rw [hb]
    exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
  have hmul := relIndex_mul_relIndex (S : Subgroup _) (minimalParabolic b i) B hSn hn
  rw [hi, hp3, hb, CubicSylowGeneration.minimalParabolic_index] at hmul
  have hnB : (minimalParabolic b i).relIndex B = 1 := by omega
  exact ⟨b, i, hb, le_antisymm (relIndex_eq_one.mp hnB) hn⟩

private theorem fixedSpace_congruence {n : ℕ}
    (C : Subgroup (LinearGroup n)) (hp : IsPGroup 3 C)
    (E : Submodule (ZMod 2) (Space n)) (hCE : C ≤ parabolic E) :
    Nat.card E % 3 = Nat.card (E ⊓ fixedSpace C : Submodule (ZMod 2) (Space n)) % 3 := by
  let : MulAction C E := {
    smul := fun c x => ⟨c.val x.val, (hCE c.property x.val).mpr x.property⟩
    one_smul := fun x => Subtype.ext (by rfl)
    mul_smul := fun c d x => Subtype.ext (by rfl) }
  let e : MulAction.fixedPoints C E ≃ (E ⊓ fixedSpace C : Submodule (ZMod 2) (Space n)) := {
    toFun := fun x => ⟨x.val.val, x.val.property, fun c hc =>
      congrArg Subtype.val (x.property ⟨c,hc⟩)⟩
    invFun := fun x => ⟨⟨x.val,x.property.1⟩, fun c => Subtype.ext (x.property.2 c c.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hh := hp.card_modEq_card_fixedPoints E
  rw [Nat.card_congr e] at hh
  exact hh

private theorem no_odd_even_flag {n : ℕ} (C : Subgroup (LinearGroup n))
    (hp : IsPGroup 3 C) (hc : Nat.card (fixedSpace C) = 2)
    (E F : Submodule (ZMod 2) (Space n)) (hEF : E ≤ F)
    (hCE : C ≤ parabolic E) (hCF : C ≤ parabolic F)
    (hE : Nat.card E % 3 = 2) (hF : Nat.card F % 3 = 1) : False := by
  let E' := E ⊓ fixedSpace C
  let F' := F ⊓ fixedSpace C
  have hcard (X : Submodule (ZMod 2) (Space n)) :
      Nat.card (X ⊓ fixedSpace C : Submodule (ZMod 2) (Space n)) ≤ 2 := by
    exact (Nat.card_le_card_of_injective (Submodule.inclusion (show X ⊓ fixedSpace C ≤ fixedSpace C from inf_le_right))
      (Submodule.inclusion_injective inf_le_right)).trans_eq hc
  have he := fixedSpace_congruence C hp E hCE
  have hf := fixedSpace_congruence C hp F hCF
  rw [hE] at he
  rw [hF] at hf
  have he2 : Nat.card E' = 2 := by
    have hh : Nat.card E' ≤ 2 := hcard E
    change 2 = Nat.card E' % 3 at he
    omega
  have hf1 : Nat.card F' = 1 := by
    have hh : Nat.card F' ≤ 2 := hcard F
    change 1 = Nat.card F' % 3 at hf
    omega
  have hle : Nat.card E' ≤ Nat.card F' := Nat.card_le_card_of_injective
    (Submodule.inclusion (inf_le_inf_right _ hEF)) (Submodule.inclusion_injective _)
  omega

/-- A cubic subgroup in an index-three Sylow overgroup in binary dimension five
cannot have just a fixed line on the original natural space. -/
theorem five_prime_index_fixedSpace_ne_two
    (S : Sylow 2 (LinearGroup 5)) (B C : Subgroup (LinearGroup 5))
    (hSB : (S : Subgroup _) ≤ B) (hi : (S : Subgroup _).relIndex B = 3)
    (hCB : C ≤ B) (hc : Nat.card C = 3) : Nat.card (fixedSpace C) ≠ 2 := by
  intro hfix
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hc)
  obtain ⟨b,i,hS,rfl⟩ := prime_index_node Nat.prime_three S B hSB hi
  have hpar (j : Fin 4) (hj : j ≠ i) : C ≤ parabolic (cutSpace b j) := by
    intro c hcc
    exact (mem_cutStabilizer b {i}ᶜ c).mp (hCB hcc) j hj
  have hcard (j : Fin 4) : Nat.card (cutSpace b j) = 2 ^ (j.val+1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, cutSpace_finrank]
  have hfirst (h0 : (0 : Fin 4) ≠ i) (h1 : (1 : Fin 4) ≠ i) : False := by
    exact no_odd_even_flag C hp hfix (cutSpace b 0) (cutSpace b 1)
      (cutSpace_mono b (by decide)) (hpar 0 h0) (hpar 1 h1)
      (by rw [hcard]; decide) (by rw [hcard]; decide)
  have hlast (h2 : (2 : Fin 4) ≠ i) (h3 : (3 : Fin 4) ≠ i) : False := by
    exact no_odd_even_flag C hp hfix (cutSpace b 2) (cutSpace b 3)
      (cutSpace_mono b (by decide)) (hpar 2 h2) (hpar 3 h3)
      (by rw [hcard]; decide) (by rw [hcard]; decide)
  fin_cases i
  · exact hlast (by decide) (by decide)
  · exact hlast (by decide) (by decide)
  · exact hfirst (by decide) (by decide)
  · exact hfirst (by decide) (by decide)
/-- In binary dimensions three through five, a prime-index Sylow overgroup
and a prime subgroup with just a fixed line force prime and dimension three. -/
theorem small_prime_index_fixed_line {n p : ℕ} (hp : p.Prime)
    (hn : 3 ≤ n ∧ n ≤ 5) (S : Sylow 2 (LinearGroup n))
    (B C : Subgroup (LinearGroup n)) (hSB : (S : Subgroup _) ≤ B)
    (hi : (S : Subgroup _).relIndex B = p) (hCB : C ≤ B)
    (hc : Nat.card C = p) (hfix : Nat.card (fixedSpace C) = 2) : p = 3 ∧ n = 3 := by
  have hp3 : p = 3 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact prime_sylow_overgroup_index hp S B hSB hi
  refine ⟨hp3, ?_⟩
  rw [hp3] at hi hc
  obtain ⟨hlo,hhi⟩ := hn
  interval_cases n
  · rfl
  · have hpC : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hc)
    have hh := fixedSpace_congruence C hpC ⊤ (by intro c hcc x; simp)
    rw [top_inf_eq, hfix, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, finrank_top, Module.finrank_fin_fun] at hh
    norm_num at hh
  · exact (five_prime_index_fixedSpace_ne_two S B C hSB hi hCB hc hfix).elim

end BinaryLinear
