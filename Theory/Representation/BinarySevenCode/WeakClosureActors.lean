module
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Hyperplane fixed vectors in the binary seven-point core

Every nonidentity involution has a weight-two displacement. Every elementary
four-group has a hyperplane with more fixed vectors, and every elementary
eight-group has a hyperplane fixing a vector with a weight-two displacement.

Sylow conjugacy reduces the proof to the three disjoint swaps and the regular
four-group times a disjoint swap. Six two-point words suffice for the finite
checks; the four-group check uses two independent generators, and never
enumerates subgroups of S₇. Relative indices, fixed vectors and displacement
weights are then transported through the literal conjugation maps.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 12.3.9--10, printed pp.810--811. These are finite
inputs to the corrected weak-closure proof, independent of any rank-four bound.
-/

@[expose] public section

open Equiv Subgroup
open Representation.BinaryOffender
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace BinarySevenCode.WeakClosureActors
abbrev E := BinaryPermutation.core (Fin 7)
abbrev ρ := BinaryPermutation.coreRepresentation (Fin 7)
private def seed (i : Fin 6) : E :=
  ⟨![![1,0,0,0,0,0,1], ![0,0,1,0,0,0,1], ![0,0,0,0,1,0,1],
      ![1,1,0,0,0,0,0], ![1,0,1,0,0,0,0], ![1,0,0,1,0,0,0]] i,
    (by intro j; rw [BinaryPermutation.mem_core]; fin_cases j <;> decide :
      ∀ i : Fin 6, _ ∈ BinaryPermutation.core (Fin 7)) i⟩
private def actor (b : Bool) (u : Triple) : S7 := if b then secondWord u else firstWord u
set_option maxRecDepth 4096 in
private theorem representative_displacement : ∀ b u, actor b u ≠ 1 → ∃ i : Fin 6,
    weight (ρ (actor b u) (seed i) - seed i).val = 2 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem representative_four : ∀ b u w, actor b u ≠ 1 → actor b w ≠ 1 → actor b u ≠ actor b w →
    ∃ t : Triple, (t = u ∨ t = w ∨ t = addBits u w) ∧ actor b t ≠ 1 ∧
      ∃ i : Fin 6, ρ (actor b t) (seed i) = seed i ∧
        (ρ (actor b u) (seed i) ≠ seed i ∨ ρ (actor b w) (seed i) ≠ seed i) := by
  intro b u w
  cases b <;> fin_cases u <;> fin_cases w <;>
    simp only [ne_eq, Subtype.ext_iff, funext_iff] <;> decide +kernel

private theorem weight_action (g : S7) (v : E) : weight (ρ g v).val = weight v.val :=
  weight_evenRepresentation g (evenWordsEquivCore.symm v)

private theorem pull_action (g a : S7) (v : E) :
    ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ ((MulAut.conj g) a) v) := by
  change ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ (g * a * g⁻¹) v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

private theorem pull_weight (g a : S7) (v : E) :
    weight (ρ a (ρ g⁻¹ v) - ρ g⁻¹ v).val =
      weight (ρ ((MulAut.conj g) a) v - v).val := by
  rw [pull_action, ← map_sub, weight_action]

private theorem pull_fixed (g : S7) (J : Subgroup S7) {v : E}
    (hv : v ∈ fixedSpace ρ J) :
    ρ g⁻¹ v ∈ fixedSpace ρ (J.comap (MulAut.conj g).toMonoidHom) := by
  intro a
  change ρ a.val (ρ g⁻¹ v) = ρ g⁻¹ v
  rw [pull_action]
  exact congrArg (ρ g⁻¹) (hv ⟨(MulAut.conj g) a.val, a.property⟩)

/-- Every nonidentity involution moves some even word by a word of weight two. -/
theorem involution_displacement (p : S7) (hp : p ^ 2 = 1) (hp1 : p ≠ 1) :
    ∃ v : E, weight (ρ p v - v).val = 2 := by
  obtain ⟨g, hg⟩ := elementary_conjugate_le
    (IsElementaryAbelian.zpowers_of_pow_eq_one hp)
  have hmem : (MulAut.conj g) p ∈ (zpowers p).map (MulAut.conj g).toMonoidHom :=
    mem_map_of_mem _ (mem_zpowers p)
  have hne : (MulAut.conj g) p ≠ 1 := by simpa using hp1
  have hex : ∃ b u, actor b u = (MulAut.conj g) p := by
    rcases hg with hg | hg
    · obtain ⟨u, hu⟩ := hg hmem
      exact ⟨false, u, hu⟩
    · obtain ⟨u, hu⟩ := hg hmem
      exact ⟨true, u, hu⟩
  obtain ⟨b,u,hu⟩ := hex
  obtain ⟨i,hi⟩ := representative_displacement b u (hu ▸ hne)
  refine ⟨ρ g⁻¹ (seed i), ?_⟩
  rw [pull_weight, ← hu]
  exact hi

private theorem four_in_representative (A : Subgroup S7) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 4) (b : Bool)
    (hrep : ∀ a ∈ A, ∃ u, actor b u = a) :
    ∃ J ≤ A, J.relIndex A = 2 ∧ ∃ v : E,
      v ∈ fixedSpace ρ J ∧ v ∉ fixedSpace ρ A := by
  classical
  let _ := hA
  have hne : A ≠ ⊥ := by intro h; rw [h, card_bot] at hc; omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hnle : ¬ A ≤ zpowers a := by
    intro h
    have hcard := card_le_of_le h
    rw [hc, Nat.card_zpowers, hao] at hcard
    omega
  obtain ⟨c,hcA,hca⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc1 : c ≠ 1 := fun h => hca (h ▸ (zpowers a).one_mem)
  have hac : a ≠ c := fun h => hca (h ▸ mem_zpowers a)
  obtain ⟨u,rfl⟩ := hrep a ha
  obtain ⟨w,rfl⟩ := hrep c hcA
  obtain ⟨t,ht,ht1,i,hfix,hmove⟩ := representative_four b u w ha1 hc1 hac
  have htA : actor b t ∈ A := by
    rcases ht with rfl | rfl | rfl
    · exact ha
    · exact hcA
    · have he : actor b (addBits u w) = actor b u * actor b w := by
        cases b
        · exact firstWord_mul u w
        · exact secondWord_mul u w
      rw [he]
      exact A.mul_mem ha hcA
  have hJA : zpowers (actor b t) ≤ A := zpowers_le.mpr htA
  have hcard : Nat.card (zpowers (actor b t)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ htA) ht1
  refine ⟨zpowers (actor b t), hJA, ?_, seed i, ?_, ?_⟩
  · have hh := relIndex_mul_card_of_le hJA
    rw [hcard, hc] at hh
    omega
  · exact (mem_fixedSpace_zpowers_iff ρ _ _).mpr hfix
  · intro hf
    rcases hmove with h | h
    · exact h (hf ⟨_,ha⟩)
    · exact h (hf ⟨_,hcA⟩)

/-- A four-group has a hyperplane whose fixed space strictly contains its own. -/
theorem four_hyperplane (A : Subgroup S7) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 4) :
    ∃ J ≤ A, J.relIndex A = 2 ∧ ∃ v : E,
      v ∈ fixedSpace ρ J ∧ v ∉ fixedSpace ρ A := by
  obtain ⟨g,hg⟩ := elementary_conjugate_le hA
  let A' := A.map (MulAut.conj g).toMonoidHom
  have he : IsElementaryAbelian 2 A' := by
    let _ := hA
    exact IsElementaryAbelian.map _
  have hc' : Nat.card A' = 4 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hc]
  have hex : ∃ J ≤ A', J.relIndex A' = 2 ∧ ∃ v : E,
      v ∈ fixedSpace ρ J ∧ v ∉ fixedSpace ρ A' := by
    rcases hg with hg | hg
    · exact four_in_representative A' he hc' false (fun a ha => hg ha)
    · exact four_in_representative A' he hc' true (fun a ha => hg ha)
  obtain ⟨J,hJA,hi,v,hv,hn⟩ := hex
  refine ⟨J.comap (MulAut.conj g).toMonoidHom, ?_, ?_, ρ g⁻¹ v,
    pull_fixed g J hv, ?_⟩
  · exact (comap_mono hJA).trans_eq (comap_map_eq_self_of_injective
      (MulAut.conj g).injective _)
  · rwa [relIndex_comap]
  · intro hf
    apply hn
    rintro ⟨a,ha⟩
    obtain ⟨c,hc,rfl⟩ := ha
    have h := hf ⟨c,hc⟩
    change ρ c (ρ g⁻¹ v) = ρ g⁻¹ v at h
    rw [pull_action] at h
    change ρ ((MulAut.conj g) c) v = v
    have hh := congrArg (ρ g) h
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, mul_inv_cancel_left, map_one,
      Module.End.one_apply] using hh

private def halfWord (b : Bool) (x : Fin 2 × Fin 2) : S7 :=
  if b then secondWord (x.1,x.2,0) else firstWord (0,x.1,x.2)
private def halfGroup (b : Bool) : Subgroup S7 := rangeSubgroup (halfWord b)
  (by cases b <;> decide +kernel)
  (fun x y => ⟨(x.1+y.1,x.2+y.2),
    (by decide +kernel : ∀ b x y, halfWord b (x.1+y.1,x.2+y.2) =
      halfWord b x * halfWord b y) b x y⟩)
  (fun x => ⟨x, (by decide +kernel : ∀ b x, halfWord b x = (halfWord b x)⁻¹) b x⟩)

private theorem halfGroup_card (b : Bool) : Nat.card (halfGroup b) = 4 := by
  have hinj : Function.Injective (halfWord b) :=
    (by decide +kernel : ∀ b, Function.Injective (halfWord b)) b
  change Nat.card (Set.range (halfWord b)) = 4
  rw [Nat.card_congr (Equiv.ofInjective _ hinj).symm]
  simp

private def bigGroup (b : Bool) : Subgroup S7 := if b then fourTwoElementary else pairElementary

private theorem eight_representative (b : Bool) :
    ∃ J ≤ bigGroup b, J.relIndex (bigGroup b) = 2 ∧ ∃ a ∈ bigGroup b, ∃ v : E,
      v ∈ fixedSpace ρ J ∧ weight (ρ a v - v).val = 2 := by
  have hle : halfGroup b ≤ bigGroup b := by
    rintro _ ⟨x,rfl⟩
    cases b
    · exact ⟨(0,x.1,x.2),rfl⟩
    · exact ⟨(x.1,x.2,0),rfl⟩
  have hc : Nat.card (bigGroup b) = 8 := by
    cases b
    · exact pairElementary_card
    · exact fourTwoElementary_card
  let a := if b then swap45 else swap01
  let v := seed (if b then 2 else 0)
  refine ⟨halfGroup b,hle,?_,a,?_,v,?_,?_⟩
  · have h := relIndex_mul_card_of_le hle
    rw [halfGroup_card,hc] at h
    omega
  · cases b
    · exact pairElementary_generators.1
    · exact fourTwoElementary_generators.2.2
  · rintro ⟨_,x,rfl⟩
    exact (by simp only [Subtype.ext_iff]; decide +kernel : ∀ b x,
      ρ (halfWord b x) (seed (if b then 2 else 0)) = seed (if b then 2 else 0)) b x
  · exact (by decide +kernel : ∀ b : Bool,
      weight (ρ (if b then swap45 else swap01) (seed (if b then 2 else 0)) -
        seed (if b then 2 else 0)).val = 2) b

/-- An eight-group has a hyperplane-fixed vector with a weight-two displacement. -/
theorem eight_hyperplane (A : Subgroup S7) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 8) :
    ∃ J ≤ A, J.relIndex A = 2 ∧ ∃ a ∈ A, ∃ v : E,
      v ∈ fixedSpace ρ J ∧ weight (ρ a v - v).val = 2 := by
  have hne : A ≠ ⊥ := by intro h; rw [h,card_bot] at hc; omega
  have hr : rank A = 3 := by rw [rank,hc]; decide
  obtain ⟨g,hg⟩ := elementary_rank_three_conjugacy A ⟨hne,hA⟩ hr
  have hex : ∃ b, A.map (MulAut.conj g).toMonoidHom = bigGroup b := by
    rcases hg with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hex
  obtain ⟨J,hJ,hi,a,ha,v,hv,hw⟩ := eight_representative b
  rw [← hb] at hJ hi ha
  obtain ⟨a,ha,rfl⟩ := ha
  refine ⟨J.comap (MulAut.conj g).toMonoidHom, ?_, ?_, a,ha,ρ g⁻¹ v,
    pull_fixed g J hv, ?_⟩
  · exact (comap_mono hJ).trans_eq (comap_map_eq_self_of_injective
      (MulAut.conj g).injective _)
  · rwa [relIndex_comap]
  · rwa [pull_weight]
end BinarySevenCode.WeakClosureActors
