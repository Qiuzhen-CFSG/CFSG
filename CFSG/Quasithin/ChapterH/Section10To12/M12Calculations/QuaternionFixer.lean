module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.FixedPoints

/-!
# The quaternion obstruction for common fixed spaces on the M₁₂ heart

A permutation fixing the heart fixed space of the marked central involution
pointwise fixes each of its four fixed letters. Even words supported on pairs
of these letters detect this: equality modulo constants is actual equality
for pair words, since there is a coordinate outside the two supports.

The right quaternion embedding fixes these four letters and is transitive on
the other eight. Sharp five-transitivity therefore identifies its image with
the full four-letter pointwise stabilizer. Its only square-one elements are
`1` and the marked involution, so any elementary two-subgroup with the same
heart fixed space has rank at most one. Conjugation transports this obstruction
using the actual representation operators.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, H.11.1, final paragraph, printed p.393 (PDF p.404).
This proves the native quaternion obstruction; the offender reduction and
ambient transport are assembled by the surrounding H.11 development.
-/

@[expose] public section

open BinaryPermutation Representation.BinaryOffender Sporadic.Mathieu
open Sporadic.Mathieu.M12SmallPair Sporadic.Mathieu.M12SmallPair.FirstCore

namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.QuaternionFixer

private def pairWord (a b : Fin 12) : Full (Fin 12) := Pi.single a 1 + Pi.single b 1

private theorem pairWord_mem_core (a b : Fin 12) : pairWord a b ∈ BinaryPermutation.core (Fin 12) := by
  simp [pairWord, BinaryPermutation.mem_core, Finset.sum_add_distrib]
  decide

private def pairHeart (a b : Fin 12) : M12Heart :=
  ⟨(constants (Fin 12)).mkQ (pairWord a b), ⟨_, pairWord_mem_core a b, rfl⟩⟩

private theorem action_pairWord (g : Equiv.Perm (Fin 12)) (a b : Fin 12) :
    representation (Fin 12) g (pairWord a b) = pairWord (g a) (g b) := by
  ext i
  simp [pairWord, Pi.single_apply, Equiv.symm_apply_eq]

private theorem pairHeart_fixed (a b : Fin 12) (ha : zPerm a = a) (hb : zPerm b = b) :
    pairHeart a b ∈ fixedSpace m12HeartRepresentation (Subgroup.zpowers z) := by
  rw [mem_fixedSpace_zpowers_iff]
  apply Subtype.ext
  change (constants (Fin 12)).mkQ (representation (Fin 12) zPerm (pairWord a b)) = _
  rw [action_pairWord, ha, hb]
  rfl

private theorem pairWord_eq_of_quotient_eq (a b c d : Fin 12)
    (h : (constants (Fin 12)).mkQ (pairWord a b) = (constants (Fin 12)).mkQ (pairWord c d)) :
    pairWord a b = pairWord c d := by
  change (Submodule.Quotient.mk (pairWord a b) : Deleted (Fin 12)) = Submodule.Quotient.mk (pairWord c d) at h
  obtain ⟨t, ht⟩ := (mem_constants_iff _).mp ((Submodule.Quotient.eq _).mp h)
  have hcard : ({a,b,c,d} : Finset (Fin 12)).card < (Finset.univ : Finset (Fin 12)).card :=
    lt_of_le_of_lt Finset.card_le_four (by decide)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  have ht0 : t = 0 := by
    have := ht i
    simpa [pairWord, Pi.single_apply, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2] using this.symm
  ext i
  exact sub_eq_zero.mp ((ht i).trans ht0)

private theorem pair_preserved (g : M12)
    (h : ∀ v ∈ fixedSpace m12HeartRepresentation (Subgroup.zpowers z), m12HeartRepresentation g v = v)
    (a b : Fin 12) (ha : zPerm a = a) (hb : zPerm b = b) (hab : a ≠ b) :
    g.val a = a ∨ g.val a = b := by
  have he := congrArg Subtype.val (h _ (pairHeart_fixed a b ha hb))
  change (constants (Fin 12)).mkQ (representation (Fin 12) g.val (pairWord a b)) =
    (constants (Fin 12)).mkQ (pairWord a b) at he
  rw [action_pairWord] at he
  have he := congrFun (pairWord_eq_of_quotient_eq _ _ _ _ he) (g.val a)
  have hab' : g.val a ≠ g.val b := g.val.injective.ne hab
  by_contra hn
  simp only [not_or] at hn
  simp [pairWord, hab', hn.1, hn.2] at he

private theorem fixes_fixedLabel (g : M12)
    (h : ∀ v ∈ fixedSpace m12HeartRepresentation (Subgroup.zpowers z), m12HeartRepresentation g v = v)
    (i : Fin 4) : g.val (fixedLabel i) = fixedLabel i := by
  have hf (j : Fin 4) : zPerm (fixedLabel j) = fixedLabel j :=
    (fixed_iff _).mpr ⟨j, rfl⟩
  have hne : ∀ j : Fin 4, fixedLabel j ≠ fixedLabel (j + 1) ∧
      fixedLabel j ≠ fixedLabel (j + 2) ∧ fixedLabel (j + 1) ≠ fixedLabel (j + 2) := by
    decide +kernel
  rcases pair_preserved g h _ _ (hf i) (hf (i + 1)) (hne i).1 with hi | hi
  · exact hi
  rcases pair_preserved g h _ _ (hf i) (hf (i + 2)) (hne i).2.1 with hi' | hi'
  · exact hi'
  exact False.elim ((hne i).2.2 (hi.symm.trans hi'))

/-- The pointwise stabilizer of the four letters fixed by the marked involution. -/
noncomputable def fixedLettersStabilizer : Subgroup M12 :=
  ⨅ i : Fin 4, MulAction.stabilizer M12 (fixedLabel i)

/-- Membership means pointwise fixation in the native twelve-letter action. -/
theorem mem_fixedLettersStabilizer (g : M12) :
    g ∈ fixedLettersStabilizer ↔ ∀ i, g.val (fixedLabel i) = fixedLabel i := by
  simp only [fixedLettersStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

/-- A pointwise fixer of the marked involution's heart fixed space fixes every
letter fixed by that involution. Pair-supported even words detect the letters. -/
theorem fixedSpace_z_pointwise_fixer_fixes_letters (g : M12)
    (h : ∀ v ∈ fixedSpace m12HeartRepresentation (Subgroup.zpowers z),
      m12HeartRepresentation g v = v)
    (i : Fin 12) (hi : zPerm i = i) : g.val i = i := by
  obtain ⟨j, rfl⟩ := (fixed_iff i).mp hi
  exact fixes_fixedLabel g h j

private def fiveLetters : Fin 5 ↪ Fin 12 := ⟨![2,7,9,0,1], by decide +kernel⟩

private theorem rightEmbedding_fixedLabel :
    ∀ (q : QuaternionGroup 2) (i : Fin 4),
      (rightEmbedding q).val (fixedLabel i) = fixedLabel i := by
  decide +kernel

private theorem rightEmbedding_orbit : ∀ point : Fin 12,
    (∀ i, point ≠ fixedLabel i) → ∃ q : QuaternionGroup 2, (rightEmbedding q).val 1 = point := by
  decide +kernel

/-- Sharp five-transitivity identifies the four-letter stabilizer with the
actual image of the right quaternion embedding. -/
theorem fixedLettersStabilizer_eq_rightFactor : fixedLettersStabilizer = rightFactor := by
  apply le_antisymm
  · intro g hg
    have hf := (mem_fixedLettersStabilizer g).mp hg
    have hm : ∀ i, g.val 1 ≠ fixedLabel i := by
      intro i hi
      have he := g.val.injective (hi.trans (hf i).symm)
      have hn : ∀ j : Fin 4, (1 : Fin 12) ≠ fixedLabel j := by decide +kernel
      exact hn i he
    obtain ⟨q, hq⟩ := rightEmbedding_orbit _ hm
    refine ⟨q, ?_⟩
    apply m12_isSharplyFivePretransitive.bijective_orbitMap fiveLetters |>.injective
    apply Function.Embedding.ext
    intro i
    fin_cases i
    · exact (rightEmbedding_fixedLabel q 0).trans (hf 0).symm
    · exact (rightEmbedding_fixedLabel q 1).trans (hf 1).symm
    · exact (rightEmbedding_fixedLabel q 2).trans (hf 2).symm
    · exact (rightEmbedding_fixedLabel q 3).trans (hf 3).symm
    · exact hq
  · rintro g ⟨q, rfl⟩
    exact (mem_fixedLettersStabilizer _).mpr (rightEmbedding_fixedLabel q)

/-- The concrete quaternion isomorphism of the four-letter pointwise stabilizer. -/
noncomputable def fixedLettersQuaternionEquiv : fixedLettersStabilizer ≃* QuaternionGroup 2 :=
  (MulEquiv.subgroupCongr fixedLettersStabilizer_eq_rightFactor).trans
    (MonoidHom.ofInjective rightEmbedding_injective).symm

private theorem rightEmbedding_square_one : ∀ q : QuaternionGroup 2,
    rightEmbedding q ^ 2 = 1 → rightEmbedding q = 1 ∨ rightEmbedding q = z := by
  decide +kernel

/-- An elementary two-subgroup with the same fixed space as `z` lies in `⟨z⟩`:
it lies in the embedded quaternion group, whose only square-one elements are
`1` and `z`. -/
theorem elementary_common_fixedSpace_le_zpowers {A : Subgroup M12}
    [IsElementaryAbelian 2 A]
    (hfix : fixedSpace m12HeartRepresentation A = fixedSpace m12HeartRepresentation (Subgroup.zpowers z)) :
    A ≤ Subgroup.zpowers z := by
  intro g hg
  have hf : ∀ v ∈ fixedSpace m12HeartRepresentation (Subgroup.zpowers z), m12HeartRepresentation g v = v := by
    intro v hv
    rw [← hfix] at hv
    exact hv ⟨g, hg⟩
  have hgR : g ∈ rightFactor := by
    rw [← fixedLettersStabilizer_eq_rightFactor, mem_fixedLettersStabilizer]
    exact fixes_fixedLabel g hf
  obtain ⟨q, rfl⟩ := hgR
  rcases rightEmbedding_square_one q (elemPow_eq_one_of_isElementaryAbelian _ hg) with he | he
  · rw [he]; exact (Subgroup.zpowers z).one_mem
  · rw [he]; exact Subgroup.mem_zpowers z

/-- The quaternion obstruction bounds the binary rank by one. -/
theorem elementary_common_fixedSpace_rank_le_one {A : Subgroup M12}
    [IsElementaryAbelian 2 A]
    (hfix : fixedSpace m12HeartRepresentation A = fixedSpace m12HeartRepresentation (Subgroup.zpowers z)) :
    rank A ≤ 1 := by
  have hc := Subgroup.card_le_of_le (elementary_common_fixedSpace_le_zpowers hfix)
  rw [Nat.card_zpowers, z_order] at hc
  exact (Nat.log_mono_right hc).trans (by decide : Nat.log 2 2 ≤ 1)

/-- If the elementary subgroup also contains `z`, it is precisely `⟨z⟩`. -/
theorem elementary_common_fixedSpace_eq_zpowers {A : Subgroup M12}
    [IsElementaryAbelian 2 A] (hz : z ∈ A)
    (hfix : fixedSpace m12HeartRepresentation A = fixedSpace m12HeartRepresentation (Subgroup.zpowers z)) :
    A = Subgroup.zpowers z :=
  le_antisymm (elementary_common_fixedSpace_le_zpowers hfix) (Subgroup.zpowers_le.mpr hz)

private theorem fixedSpace_conj_mem (A : Subgroup M12) (c : M12) (v : M12Heart) :
    v ∈ fixedSpace m12HeartRepresentation (A.map (MulAut.conj c).toMonoidHom) ↔
      m12HeartRepresentation c⁻¹ v ∈ fixedSpace m12HeartRepresentation A := by
  constructor
  · intro hv a
    have he := hv ⟨c * a.val * c⁻¹, Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom a.property⟩
    have he' := congrArg (m12HeartRepresentation c⁻¹) he
    change m12HeartRepresentation c⁻¹ (m12HeartRepresentation (c * a.val * c⁻¹) v) = _ at he'
    change m12HeartRepresentation a.val (m12HeartRepresentation c⁻¹ v) = _
    simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using he'
  · intro hv b
    obtain ⟨a, ha, hab⟩ := b.property
    change m12HeartRepresentation b.val v = v
    rw [← hab]
    change m12HeartRepresentation (c * a * c⁻¹) v = v
    simp only [map_mul, Module.End.mul_apply]
    have ha' : m12HeartRepresentation a (m12HeartRepresentation c⁻¹ v) =
        m12HeartRepresentation c⁻¹ v := hv ⟨a, ha⟩
    rw [ha', Representation.self_inv_apply]

private theorem fixedSpace_conj_eq {A B : Subgroup M12} (c : M12)
    (h : fixedSpace m12HeartRepresentation A = fixedSpace m12HeartRepresentation B) :
    fixedSpace m12HeartRepresentation (A.map (MulAut.conj c).toMonoidHom) =
      fixedSpace m12HeartRepresentation (B.map (MulAut.conj c).toMonoidHom) := by
  ext v
  rw [fixedSpace_conj_mem, fixedSpace_conj_mem, h]

/-- The obstruction is unchanged under genuine conjugation in native M₁₂. -/
theorem elementary_conjugate_common_fixedSpace_rank_le_one {A : Subgroup M12}
    [IsElementaryAbelian 2 A] (c : M12)
    (hfix : fixedSpace m12HeartRepresentation A =
      fixedSpace m12HeartRepresentation (Subgroup.zpowers (c * z * c⁻¹))) :
    rank A ≤ 1 := by
  have hfix' := fixedSpace_conj_eq c⁻¹ hfix
  have he : (MulAut.conj c⁻¹).toMonoidHom (c * z * c⁻¹) = z := by
    simp [mul_assoc]
  rw [MonoidHom.map_zpowers, he] at hfix'
  let : IsElementaryAbelian 2 (A.map (MulAut.conj c⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  simpa only [rank_map_conj] using elementary_common_fixedSpace_rank_le_one hfix'

/-- The rank-three case in the last paragraph of H.11.1 is impossible once
its fixed space is that of a conjugate of the marked central involution. -/
theorem no_rank_three_common_fixedSpace {A : Subgroup M12} (hA : IsElementaryTwo A)
    (hrank : rank A = 3) (c : M12) :
    fixedSpace m12HeartRepresentation A ≠
      fixedSpace m12HeartRepresentation (Subgroup.zpowers (c * z * c⁻¹)) := by
  let : IsElementaryAbelian 2 A := hA.2
  intro he
  have := elementary_conjugate_common_fixedSpace_rank_le_one c he
  omega

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.QuaternionFixer
