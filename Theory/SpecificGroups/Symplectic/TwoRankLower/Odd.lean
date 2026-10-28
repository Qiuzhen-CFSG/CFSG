module

public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.FinCases
/-!
# Elementary eights in odd-characteristic projective symplectic groups

In half-dimension at least three, two independent signs on hyperbolic pairs
commute with the standard symplectic matrix J. Its square is scalar minus
one, so their projective images are involutions. The unused third pair
removes every scalar ambiguity. In half-dimension two, exchange the second
sign for the simultaneous swap of both hyperbolic pairs; its anticommutation
with the first sign disappears in the actual central quotient.

Matrix entries prove independence in both cases. The center is used through
the existing transvection proof that central matrices are scalar.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

open Matrix
noncomputable section
namespace Theory.SpecificGroups.Symplectic.TwoRank
open SymplecticRoot
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))


variable (F : Type*) [Field F] {r : ℕ}
private def signMatrix (i : Fin r) : Matrix (Fin r) (Fin r) F :=
  diagonal (fun j => if j = i then -1 else 1)
private def signSp (i : Fin r) : Sp r F :=
  ⟨fromBlocks (signMatrix F i) 0 0 (signMatrix F i), by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [signMatrix, diagonal_mul_diagonal, diagonal_eq_one]
    funext j
    split_ifs <;> simp⟩
private theorem sign_sq (i : Fin r) : signSp F i ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, Submonoid.coe_one, pow_two]
  have hd : signMatrix F i * signMatrix F i = 1 := by
    rw [signMatrix, diagonal_mul_diagonal, diagonal_eq_one]
    funext j
    split_ifs <;> simp
  change fromBlocks _ _ _ _ * fromBlocks _ _ _ _ = _
  rw [fromBlocks_multiply]
  simp [hd, ← fromBlocks_one]
private theorem sign_commute (i j : Fin r) : Commute (signSp F i) (signSp F j) := by
  apply Subtype.ext
  change (signSp F i).val * (signSp F j).val = (signSp F j).val * (signSp F i).val
  simp [signSp, signMatrix, diagonal_mul_diagonal, mul_comm]
private theorem sign_J_commute (i : Fin r) : Commute (signSp F i) (SymplecticGroup.symJ (Fin r) F) := by
  apply Subtype.ext
  change (signSp F i).val * J (Fin r) F = J (Fin r) F * (signSp F i).val
  simp [signSp, J, fromBlocks_multiply]
private def imageSign (i : Fin r) : PSp r F := project (signSp F i)
private def imageJ : PSp r F := project (SymplecticGroup.symJ (Fin r) F)
private theorem imageSign_sq (i : Fin r) : imageSign F i ^ 2 = 1 := by
  rw [imageSign, ← map_pow, sign_sq, map_one]
private theorem imageJ_sq : imageJ (r := r) F ^ 2 = 1 := by
  rw [imageJ, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  simp only [Submonoid.coe_mul, SymplecticGroup.coe_J, pow_two]
  rw [J_squared]
  simp
private def embedding (i j : Fin r) : E →* PSp r F :=
  tripleHom (imageSign F i) (imageSign F j) (imageJ F)
    (imageSign_sq F i) (imageSign_sq F j) (imageJ_sq F)
    ((sign_commute F i j).map project) ((sign_J_commute F i).map project)
    ((sign_J_commute F j).map project)
private def raw (i j : Fin r) (x : E) : Sp r F :=
  (if x.1.1 = 1 then 1 else signSp F i) * (if x.1.2 = 1 then 1 else signSp F j) *
    (if x.2 = 1 then 1 else SymplecticGroup.symJ (Fin r) F)
private theorem embedding_raw (i j : Fin r) (x : E) : embedding F i j x = project (raw F i j x) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk, raw, map_mul]
  split_ifs <;> simp [imageSign,imageJ]
private theorem central_scalar (g : Sp r F) (hg : g ∈ Subgroup.center (Sp r F)) :
    ∃ s : F, g.val = diagonal (fun _ => s) := by
  obtain ⟨s,hs⟩ := PSp4Three.central_is_scalar g hg
  refine ⟨s, ?_⟩
  ext i j
  have h := congrFun (hs (Pi.single j 1)) i
  simpa [PSp4Three.smul_eq_mulVec, Matrix.mulVec_single,
    Pi.single_apply, diagonal_apply, eq_comm] using h
private theorem injective (hF : (2:F) ≠ 0) (i j k : Fin r)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Function.Injective (embedding F i j) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [embedding_raw] at hx
  have hc : raw F i j x ∈ Subgroup.center (Sp r F) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨s,hs⟩ := central_scalar F _ hc
  have h01 := congrArg (fun M => M (.inl i) (.inr i)) hs
  have hkk := congrArg (fun M => M (.inl k) (.inl k)) hs
  have hii := congrArg (fun M => M (.inl i) (.inl i)) hs
  have hjj := congrArg (fun M => M (.inl j) (.inl j)) hs
  have hn : (-1:F) ≠ 1 := by intro h; apply hF; linear_combination -h
  have hz : x.2 = 1 := by
    by_contra hz
    rcases x with ⟨⟨a,b⟩,c⟩
    simp only [raw, Submonoid.coe_mul] at h01
    split_ifs at h01 <;>
      simp [signSp, signMatrix, J, diagonal_mul_diagonal, hij] at h01
  have hab : x.1.1 = 1 ∧ x.1.2 = 1 := by
    simp only [raw, hz, ↓reduceIte, mul_one, Submonoid.coe_mul] at hkk hii hjj
    by_cases ha : x.1.1 = 1 <;> by_cases hb : x.1.2 = 1
    all_goals simp [ha,hb,signSp,signMatrix,hij,Ne.symm hij,Ne.symm hik,Ne.symm hjk] at hkk hii hjj
    · exact ⟨ha,hb⟩
    · exact (hn (hjj.trans hkk.symm)).elim
    · exact (hn (hii.trans hkk.symm)).elim
    · exact (hn (hii.trans hkk.symm)).elim
  exact Prod.ext (Prod.ext hab.1 hab.2) hz
private def swapSp : Sp 2 F :=
  ⟨fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0], by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply]⟩
private theorem swap_sq : swapSp F ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow,Submonoid.coe_one,pow_two]
  change fromBlocks _ _ _ _ * fromBlocks _ _ _ _ = _
  rw [fromBlocks_multiply]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp
private theorem swap_J_commute : Commute (swapSp F) (SymplecticGroup.symJ (Fin 2) F) := by
  apply Subtype.ext
  change (swapSp F).val * J (Fin 2) F = J (Fin 2) F * (swapSp F).val
  simp [swapSp, J, fromBlocks_multiply]
private def imageSwap : PSp 2 F := project (swapSp F)
private theorem imageSwap_sq : imageSwap F ^ 2 = 1 := by
  rw [imageSwap,← map_pow,swap_sq,map_one]
private theorem imageSign_swap_commute : Commute (imageSign F (0:Fin 2)) (imageSwap F) := by
  have hm : signSp F (0:Fin 2) * swapSp F =
      SymplecticGroup.symJ (Fin 2) F ^ 2 * (swapSp F * signSp F 0) := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, pow_two, SymplecticGroup.coe_J]
    rw [J_squared]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [signSp,signMatrix,swapSp,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two]
  have hq := congrArg (project (F := F)) hm
  change imageSign F (0:Fin 2) * imageSwap F = imageSwap F * imageSign F 0
  have hj : project (SymplecticGroup.symJ (Fin 2) F) ^ 2 = 1 := imageJ_sq F
  simpa only [map_mul,map_pow,hj,one_mul,imageSign,imageSwap] using hq
private def embeddingFour : E →* PSp 2 F :=
  tripleHom (imageSign F 0) (imageSwap F) (imageJ F)
    (imageSign_sq F 0) (imageSwap_sq F) (imageJ_sq F)
    (imageSign_swap_commute F) ((sign_J_commute F 0).map project)
    ((swap_J_commute F).map project)
private def rawFour (x : E) : Sp 2 F :=
  (if x.1.1 = 1 then 1 else signSp F 0) * (if x.1.2 = 1 then 1 else swapSp F) *
    (if x.2 = 1 then 1 else SymplecticGroup.symJ (Fin 2) F)
private theorem embeddingFour_raw (x : E) : embeddingFour F x = project (rawFour F x) := by
  simp only [embeddingFour,tripleHom,MonoidHom.noncommCoprod_apply,binaryHom,
    MonoidHom.coe_mk,OneHom.coe_mk,rawFour,map_mul]
  split_ifs <;> simp [imageSign,imageSwap,imageJ]
private theorem injectiveFour (hF : (2:F) ≠ 0) : Function.Injective (embeddingFour F) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [embeddingFour_raw] at hx
  have hc : rawFour F x ∈ Subgroup.center (Sp 2 F) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨s,hs⟩ := central_scalar F _ hc
  have h00 := congrArg (fun M => M (.inl 0) (.inl 0)) hs
  have h11 := congrArg (fun M => M (.inl 1) (.inl 1)) hs
  have h01 := congrArg (fun M => M (.inl 0) (.inl 1)) hs
  have h02 := congrArg (fun M => M (.inl 0) (.inr 0)) hs
  have h03 := congrArg (fun M => M (.inl 0) (.inr 1)) hs
  have hn : (-1:F) ≠ 1 := by intro h; apply hF; linear_combination -h
  simp only [rawFour,Submonoid.coe_mul] at h00 h11 h01 h02 h03
  by_cases ha : x.1.1 = 1 <;> by_cases hb : x.1.2 = 1 <;> by_cases hz : x.2 = 1
  all_goals simp [ha,hb,hz,signSp,signMatrix,swapSp,J,
    Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.one_apply] at h00 h11 h01 h02 h03
  · exact Prod.ext (Prod.ext ha hb) hz
  · exact (hn (h00.trans h11.symm)).elim
/-- Every odd-characteristic projective symplectic group of half-dimension at least two
contains an elementary abelian group of order eight. -/
public theorem odd_rank_ge [Finite F] {r : ℕ} (hr : 2 ≤ r) (hF : (2:F) ≠ 0) :
    3 ≤ primeRank 2 (PSp r F) := by
  by_cases h2 : r = 2
  · subst r
    apply primeRank_ge_of_elementary_embedding (f := embeddingFour F)
    · exact (by decide +kernel : ∀ x : E, x ^ 2 = 1)
    · simp [E,C2,Nat.card_eq_fintype_card]
    · exact injectiveFour F hF
  · let i : Fin r := ⟨0,by omega⟩
    let j : Fin r := ⟨1,by omega⟩
    let k : Fin r := ⟨2,by omega⟩
    apply primeRank_ge_of_elementary_embedding (f := embedding F i j)
    · exact (by decide +kernel : ∀ x : E, x ^ 2 = 1)
    · simp [E,C2,Nat.card_eq_fintype_card]
    · apply injective F hF i j k
      all_goals intro h; have hh := congrArg Fin.val h; simp [i,j,k] at hh
end Theory.SpecificGroups.Symplectic.TwoRank
