module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondRecognition
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCore
import Mathlib.Tactic.Tauto

/-!
# The second Tits core inside the marked Sylow subgroup

An index-two subgroup has a binary membership character. The collection
relations force this character to vanish on s1, s2, s4 and s6, and to agree
on s3, s5 and s7. If s3 lies outside the subgroup, six common words and one
of s8 or s3*s8 restrict its center to two normal forms. The point tests used
for this upper bound are checked by the kernel, without an automorphism census.

Consequently a center of order at least four forces the first seven positive
generators into the subgroup. Their first 1024 normal forms are distinct, so
they determine it uniquely. The existing matrix-root inclusion places s3 in
the literal second two-core; its index is two. This identifies the subgroup
with the comap along the specified Sylow inclusion.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, especially
F.1.12(I)(9); Parrott (1972), §5, p.683, for the positive generators and
collection equations. The source application is in QuinticSecondParabolic.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.SecondCoreCensus
open Subgroup SecondRecognition AmalgamRigidity.SecondExtension

private theorem relations : SylowRelations positive := by
  have h := generators_sylowRelations (MonoidHom.id S) (1 : S)
  have hg : generators (MonoidHom.id S) (1 : S) = positive := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [generators, positive]
    · simp [generators, hi]
  rwa [hg] at h

private theorem membership {P : Type*} [Group P] (g : Fin 9 → P)
    (relations : SylowRelations g) (K : Subgroup P) (hi : K.index = 2) :
    g 1 ∈ K ∧ g 2 ∈ K ∧ g 4 ∈ K ∧ g 6 ∈ K ∧
    (g 3 ∈ K ↔ g 5 ∈ K) ∧ (g 3 ∈ K ↔ g 7 ∈ K) := by
  have sq (x : P) : x ^ 2 ∈ K := sq_mem_of_index_two hi x
  have cube (x : P) : x ^ 3 ∈ K ↔ x ∈ K := by
    rw [pow_succ, mul_mem_iff_of_index_two hi]
    simp [sq]
  have conj (x y : P) : x * y * x⁻¹ ∈ K ↔ y ∈ K := by
    simp only [mul_mem_iff_of_index_two hi, inv_mem_iff]
    tauto
  have h52 := congrArg (fun x : P => x ∈ K) relations.conjugate_5_2
  have h71 := congrArg (fun x : P => x ∈ K) relations.conjugate_7_1
  have h53 := congrArg (fun x : P => x ∈ K) relations.conjugate_5_3
  have h82 := congrArg (fun x : P => x ∈ K) relations.conjugate_8_2
  have h73 := congrArg (fun x : P => x ∈ K) relations.conjugate_7_3
  have h85 := congrArg (fun x : P => x ∈ K) relations.conjugate_8_5
  simp only [eq_iff_iff, conj, mul_mem_iff_of_index_two hi, sq, cube, iff_true]
    at h52 h71 h53 h82 h73 h85
  have h4 : g 4 ∈ K := by
    by_cases h1 : g 1 ∈ K
    · exact (h71.mp h1).mp (h52.mpr h1)
    · have h2 : g 2 ∉ K := fun h => h1 (h52.mp h)
      by_contra h4
      exact h1 (h71.mpr (iff_of_false h2 h4))
  have h1 : g 1 ∈ K := by
    by_cases h3 : g 3 ∈ K
    · exact ((h53.mp h3).mpr h4).mpr h3
    · by_contra h1
      exact h3 (h53.mpr (iff_of_true (iff_of_false h1 h3) h4))
  have h2 : g 2 ∈ K := h52.mpr h1
  have h6 : g 6 ∈ K := (h82.mp h2).mp (iff_of_true h2 h4)
  have h57 : g 5 ∈ K ↔ g 7 ∈ K := by
    simpa only [h2, h4, iff_self, true_iff] using h85
  exact ⟨h1,h2,h4,h6,h73,h73.trans h57⟩

private theorem word_positive (n : Fin 2048) :
    word positive n = atlas1600SylowTwoEquiv n := by
  apply inclusion_injective sylow_le_second
  rw [map_word]
  have he : word ((inclusion sylow_le_second) ∘ positive) n = word gen n := by
    simp [word, inclusion_positive]
  rw [he]
  apply Subtype.ext
  exact (word_gen_val n).trans (atlas1600SylowTwoEquiv_apply n).symm

private def lower : Subgroup S :=
  closure {positive 1, positive 2, positive 3, positive 4,
    positive 5, positive 6, positive 7}

private theorem lower_card : 1024 ≤ Nat.card lower := by
  let f : Fin 1024 → lower := fun n =>
    ⟨word positive ⟨n.val, by omega⟩, by
      have he : n.val / 1024 % 2 = 0 := by omega
      simp only [word, he, pow_zero, mul_one]
      repeat first
        | apply Subgroup.mul_mem
        | apply Subgroup.pow_mem
        | exact Subgroup.subset_closure (by simp)⟩
  have hf : Function.Injective f := by
    intro x y h
    have he := congrArg Subtype.val h
    change word positive _ = word positive _ at he
    simp only [word_positive] at he
    have hn := atlas1600SylowTwoEquiv.injective he
    exact Fin.ext (congrArg (fun n : Fin 2048 => n.val) hn)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf


private theorem core_index : coreInSylow.index = 2 := by
  have hle : pCore 2 second ≤ S.subgroupOf second := by
    rw [← secondSylowTwo_coe]
    exact pCore_isPGroup.le_sylow_of_normal secondSylowTwo
  have hc := (pCore 2 second).card_mul_index
  rw [second_core_card, second_card] at hc
  have hr := relIndex_mul_index hle
  rw [second_sylow_index] at hr
  rw [coreInSylow, index_comap, inclusion_range]
  omega

private theorem three_mem_core : positive 3 ∈ coreInSylow := by
  have h := FullRee.LongRootPaths.generator_mem_secondCore .s3
    (by decide) (by decide) (by decide)
  obtain ⟨x,hx,he⟩ := h
  have hmem : secondEmbedding (gen 3) ∈ pCore 2 FullRee.second := by
    have heq : x = secondEmbedding (gen 3) := by
      apply Subtype.ext
      exact he
    exact heq ▸ hx
  change inclusion sylow_le_second (positive 3) ∈ pCore 2 second
  rw [inclusion_positive _ (by decide), ← secondProjection_ker]
  change FullRee.secondProjection (secondEmbedding (gen 3)) = 1
  rw [← FullRee.secondProjection_ker] at hmem
  exact hmem


private def commutesAtZero (x y : Equiv.Perm (Fin 1600)) : Bool :=
  x (y 0) == y (x 0)
private def baseTest (x : Equiv.Perm (Fin 1600)) : Bool :=
  commutesAtZero x (packedGen 1) && commutesAtZero x (packedGen 2) &&
  commutesAtZero x (packedGen 4) && commutesAtZero x (packedGen 6) &&
  commutesAtZero x (packedGen 3 * packedGen 5) &&
  commutesAtZero x (packedGen 3 * packedGen 7)
set_option maxRecDepth 20000 in
private theorem center_candidates (n : Fin 2048) :
    baseTest (word packedGen n) = true →
      (commutesAtZero (word packedGen n) (packedGen 8) = true ∨
       commutesAtZero (word packedGen n) (packedGen 3 * packedGen 8) = true) →
      n = 0 ∨ n = 65 := by
  revert n
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private def sylowPerm : S →* Equiv.Perm (Fin 1600) :=
  perm.comp (inclusion sylow_le_second)

private theorem perm_positive (i : Fin 9) (hi : i ≠ 0) :
    sylowPerm (positive i) = packedGen i := by
  change perm (inclusion sylow_le_second (positive i)) = _
  rw [inclusion_positive i hi, perm_gen]

private theorem perm_normalForm (n : Fin 2048) :
    sylowPerm (atlas1600SylowTwoEquiv n) = word packedGen n := by
  change (atlas1600SylowTwoEquiv n).val.val = _
  rw [atlas1600SylowTwoEquiv_apply, atlas1600SylowTwoNormalForm_val]
  simp only [word, packedGen, OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
    OuterOddSubgroups.OverlapCentralizers.Packed.generator]
  rfl

private theorem center_bound (K : Subgroup S) (hi : K.index = 2)
    (h1 : positive 1 ∈ K) (h2 : positive 2 ∈ K)
    (h4 : positive 4 ∈ K) (h6 : positive 6 ∈ K)
    (h35 : positive 3 * positive 5 ∈ K) (h37 : positive 3 * positive 7 ∈ K)
    (h3 : positive 3 ∉ K) : Nat.card (center K) ≤ 2 := by
  classical
  have hc (z : center K) :
      atlas1600SylowTwoEquiv.symm z.val.val = 0 ∨
      atlas1600SylowTwoEquiv.symm z.val.val = 65 := by
    let n := atlas1600SylowTwoEquiv.symm z.val.val
    have hn : atlas1600SylowTwoEquiv n = z.val.val :=
      atlas1600SylowTwoEquiv.apply_symm_apply _
    have he : word packedGen n = sylowPerm z.val.val := by
      rw [← perm_normalForm, hn]
    have comm (g : S) (hg : g ∈ K) :
        commutesAtZero (sylowPerm z.val.val) (sylowPerm g) = true := by
      apply beq_iff_eq.mpr
      have hz := congrArg Subtype.val (mem_center_iff.mp z.property ⟨g,hg⟩)
      exact (congrArg (fun x : S => sylowPerm x 0) hz).symm
    apply center_candidates n
    · rw [he]
      simp only [baseTest, Bool.and_eq_true]
      repeat' apply And.intro
      · simpa [perm_positive] using comm _ h1
      · simpa [perm_positive] using comm _ h2
      · simpa [perm_positive] using comm _ h4
      · simpa [perm_positive] using comm _ h6
      · simpa [perm_positive] using comm _ h35
      · simpa [perm_positive] using comm _ h37
    · rw [he]
      by_cases h8 : positive 8 ∈ K
      · exact Or.inl (by simpa [perm_positive] using comm _ h8)
      · have h38 : positive 3 * positive 8 ∈ K :=
          (mul_mem_iff_of_index_two hi).mpr (by simp [h3,h8])
        exact Or.inr (by simpa [perm_positive] using comm _ h38)
  let f : center K → Bool := fun z => decide (atlas1600SylowTwoEquiv.symm z.val.val = 0)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply atlas1600SylowTwoEquiv.symm.injective
    have hab' : (atlas1600SylowTwoEquiv.symm a.val.val = 0) ↔
        (atlas1600SylowTwoEquiv.symm b.val.val = 0) := decide_eq_decide.mp hab
    rcases hc a with ha | ha
    · exact ha.trans (hab'.mp ha).symm
    · rcases hc b with hb | hb
      · exact (hab'.mpr hb).trans hb.symm
      · exact ha.trans hb.symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_injective f hf

private theorem lower_eq (K : Subgroup S) (hi : K.index = 2)
    (h3 : positive 3 ∈ K) : lower = K := by
  obtain ⟨h1,h2,h4,h6,h35,h37⟩ := membership positive relations K hi
  have h5 := h35.mp h3
  have h7 := h37.mp h3
  have hle : lower ≤ K := by
    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  apply eq_of_le_of_card_ge hle
  have hc := K.card_mul_index
  rw [hi, sylow_card] at hc
  have hk : Nat.card K = 1024 := by omega
  rw [hk]
  exact lower_card

/-- The literal second core is the unique index-two subgroup of the Tits
Sylow whose center has order at least four. -/
theorem eq_coreInSylow_of_index_two_of_center_card (K : Subgroup S)
    (hi : K.index = 2) (hz : 4 ≤ Nat.card (center K)) :
    K = coreInSylow := by
  have h3 : positive 3 ∈ K := by
    by_contra hn
    obtain ⟨h1,h2,h4,h6,h35,h37⟩ := membership positive relations K hi
    have hb := center_bound K hi h1 h2 h4 h6
      ((mul_mem_iff_of_index_two hi).mpr h35)
      ((mul_mem_iff_of_index_two hi).mpr h37) hn
    omega
  exact (lower_eq K hi h3).symm.trans (lower_eq coreInSylow core_index three_mem_core)

end Tits.ExceptionalParabolics.SecondCoreCensus
