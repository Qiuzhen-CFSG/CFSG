module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Fusion
/-!
# Proper E8 images extend into the source E16 containers

An explicit native point-stabilizer word acts on the remaining E8 as a
seven-cycle on its nonzero elements. The seven planes form one orbit, and
one of them is contained in the first certified E16. A small Boolean check
of the XOR subgroup law places every proper subgroup in one of these planes.
The literal aligned embedding lifts the conjugator to M22 and yields the
source dichotomy: an elementary image lies in an E16, or is the entire E8.

The Boolean check enumerates eight coordinates.
No order, normality or Sylow-normalization assumption is made on the image.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1
and Proposition 2.2.2, pp.489--490. Native ATLAS generators and their membership
proofs come from the imported M23 fusion certificate. All new point and subgroup
identities are checked by Lean's kernel.
-/

public noncomputable section
open Subgroup Sporadic.Mathieu Theory.GroupTheory MathieuCode
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open M23Geometry FusionCertificate ElementarySylow M22ChapterH M22ChapterH.CompatibleSylow

private def wordElement (w : List (Fin 6)) : M23 :=
  ⟨Theory.GroupTheory.evalWord ambientGen w, by
    induction w with
    | nil => exact M23.one_mem
    | cons i w ih => exact M23.mul_mem (ambientGen_mem i) ih⟩

private def sevenElement : M23 := wordElement
  [2, 2, 2, 2, 2, 0, 4, 4, 0, 1, 0, 1, 0, 4, 0, 1, 0, 1, 1, 0, 4, 0, 1, 0, 1, 5, 5, 5, 5, 5]

private def sevenTable : Fin 23 → Fin 23 :=
  ![0, 7, 21, 17, 10, 14, 11, 5, 4, 3, 19, 16, 18, 2, 12, 15, 9, 22, 20, 13, 1, 8, 6]

private theorem seven_points : ∀ x : Fin 23,
    sevenElement.val x = sevenTable x := by decide +kernel
attribute [local irreducible] sevenElement

private def sevenAction : Fin 8 → Fin 8 := ![0,6,1,7,2,4,3,5]

private theorem seven_action_points : ∀ (i : Fin 8) (x : Fin 23),
    sevenTable (pointTable (smallIndex 0 i) x) =
      pointTable (smallIndex 0 (sevenAction i)) (sevenTable x) := by decide +kernel

private theorem proper_plane_test : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    let f : Fin 8 → Bool := ![b0,b1,b2,b3,b4,b5,b6,b7]
    f 0 = true →
    (∀ i j, f i = true → f j = true → f (i ^^^ j) = true) →
    (∀ i, f i = true) ∨ ∃ k : Fin 7, ∀ i, f i = true →
      (sevenAction^[k.val]) i = 0 ∨ (sevenAction^[k.val]) i = 2 ∨
      (sevenAction^[k.val]) i = 5 ∨ (sevenAction^[k.val]) i = 7 := by decide +kernel

private theorem proper_plane_cover (f : Fin 8 → Bool) (h0 : f 0 = true)
    (hm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true) :
    (∀ i, f i = true) ∨ ∃ k : Fin 7, ∀ i, f i = true →
      (sevenAction^[k.val]) i = 0 ∨ (sevenAction^[k.val]) i = 2 ∨
      (sevenAction^[k.val]) i = 5 ∨ (sevenAction^[k.val]) i = 7 := by
  have he : (![f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7] : Fin 8 → Bool) = f := by
    funext i; fin_cases i <;> rfl
  have ht := proper_plane_test (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  dsimp only at ht
  rw [he] at ht
  exact ht h0 hm


private def smallPoint (i : Fin 8) : M23 := sylowElement (smallIndex 0 i)

private theorem smallPoint_mul (i j : Fin 8) :
    smallPoint i * smallPoint j = smallPoint (i ^^^ j) :=
  Subtype.ext (smallIndex_mul 0 i j)

private theorem seven_conjugate (i : Fin 8) :
    (MulAut.conj sevenElement) (smallPoint i) = smallPoint (sevenAction i) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change sevenElement.val (pointTable (smallIndex 0 i) (sevenElement.val.symm x)) =
    pointTable (smallIndex 0 (sevenAction i)) x
  have h := seven_action_points i (sevenElement.val.symm x)
  rw [← seven_points,← seven_points,Equiv.apply_symm_apply] at h
  exact h

private theorem seven_power_conjugate (n : ℕ) (i : Fin 8) :
    (MulAut.conj (sevenElement^n)) (smallPoint i) = smallPoint ((sevenAction^[n]) i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (MulAut.conj (sevenElement^(n+1))) (smallPoint i) =
        (MulAut.conj sevenElement) ((MulAut.conj (sevenElement^n)) (smallPoint i)) := by
      simp [pow_succ',mul_assoc]
    rw [he,ih,seven_conjugate,Function.iterate_succ_apply']

private theorem smallPoint_in_candidate (i : Fin 8)
    (hi : i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) : smallPoint i ∈ candidate 0 := by
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨7,rfl⟩

/-- Every proper subgroup of the fixed E8 can be conjugated into the first
permutation E16 by a power of one explicit element fixing the M22 point. -/
theorem proper_small_extends (A : Subgroup M23) (hA : A < small 0) :
    ∃ g : M23, g ∈ alignedEmbedding.range ∧
      A.map (MulAut.conj g).toMonoidHom ≤ candidate 0 := by
  classical
  let f : Fin 8 → Bool := fun i => decide (smallPoint i ∈ A)
  have hf0 : f 0 = true := by
    change decide (smallPoint 0 ∈ A) = true
    have he : smallPoint 0 = 1 := Subtype.ext initial
    simp [he]
  have hfm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true := by
    intro i j hi hj
    have hi' : smallPoint i ∈ A := of_decide_eq_true hi
    have hj' : smallPoint j ∈ A := of_decide_eq_true hj
    apply decide_eq_true
    rw [← smallPoint_mul]
    exact A.mul_mem hi' hj'
  obtain hall | ⟨k,hk⟩ := proper_plane_cover f hf0 hfm
  · exfalso
    apply hA.not_ge
    rintro y ⟨i,hi⟩
    have he : smallPoint i = y := Subtype.ext hi
    exact he ▸ of_decide_eq_true (hall i)
  · refine ⟨sevenElement^k.val,?_,?_⟩
    · apply Subgroup.pow_mem
      rw [alignedEmbedding_range]
      exact seven_points 0
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨i,hi⟩ := hA.le hy
      have he : smallPoint i = y := Subtype.ext hi
      rw [← he]
      change (MulAut.conj (sevenElement^k.val)) (smallPoint i) ∈ candidate 0
      rw [seven_power_conjugate]
      exact smallPoint_in_candidate _ (hk i (by
        change decide (smallPoint i ∈ A) = true
        exact decide_eq_true (he.symm ▸ hy)))

private theorem conjugation_map (B : Subgroup M22) (g : M22) :
    (B.map (MulAut.conj g).toMonoidHom).map alignedEmbedding =
      (B.map alignedEmbedding).map (MulAut.conj (alignedEmbedding g)).toMonoidHom := by
  rw [map_map,map_map]
  apply congrArg (fun f : M22 →* M23 => B.map f)
  apply MonoidHom.ext
  intro x
  change alignedEmbedding (g*x*g⁻¹) = alignedEmbedding g * alignedEmbedding x * (alignedEmbedding g)⁻¹
  simp only [map_mul,map_inv]

/-- A proper subgroup of the genuine native E8 lies in a conjugate of one of
the two source E16 kernels. The M22 conjugator is lifted from the checked word. -/
theorem proper_smallContainer_extends (A : Subgroup M22) (hA : A < smallContainer 0) :
    ∃ g : M22,
      A ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom := by
  have hmap : A.map alignedEmbedding < small 0 := by
    rw [← smallContainer_map 0]
    apply lt_of_le_of_ne (map_mono hA.le)
    exact fun h => hA.ne (Subgroup.map_injective alignedEmbedding_injective h)
  obtain ⟨g,⟨n,hn⟩,hg⟩ := proper_small_extends _ hmap
  obtain ⟨B,hB,hrow⟩ := large_candidate_native
  have hle : A.map (MulAut.conj n).toMonoidHom ≤ B := by
    apply (Subgroup.map_le_map_iff_of_injective alignedEmbedding_injective).mp
    rwa [conjugation_map,hB,hn]
  have hback : A ≤ B.map (MulAut.conj n⁻¹).toMonoidHom := by
    intro x hx
    exact ⟨(MulAut.conj n) x,hle (mem_map_of_mem _ hx),by simp [mul_assoc]⟩
  refine ⟨n⁻¹,?_⟩
  rcases hrow with rfl | rfl
  · exact Or.inl hback
  · exact Or.inr hback

private theorem conjugate_comp (B : Subgroup M22) (g h : M22) :
    (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  apply congrArg (fun f : M22 →* M22 => B.map f)
  apply MonoidHom.ext
  intro x
  change g*(h*x*h⁻¹)*g⁻¹ = (g*h)*x*(g*h)⁻¹
  simp [mul_assoc]

/-- The precise image alternatives needed by KW Proposition 2.2.2: if the
image cannot be placed in one of the E16 kernels, it is the WHOLE E8, not an
arbitrary subgroup of it. -/
theorem elementary_native_exact_cases (A : Subgroup M22) [IsElementaryAbelian 2 A] :
    ∃ g : M22,
      A ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom ∨
      A = (smallContainer 0).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := elementary_native_three_cases A
  rcases hg with h | h | h
  · exact ⟨g,Or.inl h⟩
  · exact ⟨g,Or.inr (Or.inl h)⟩
  · by_cases he : A = (smallContainer 0).map (MulAut.conj g).toMonoidHom
    · exact ⟨g,Or.inr (Or.inr he)⟩
    let B := A.map (MulAut.conj g⁻¹).toMonoidHom
    have hback : B.map (MulAut.conj g).toMonoidHom = A := by
      rw [conjugate_comp]
      simp only [mul_inv_cancel]
      change A.map (MonoidHom.id M22) = A
      exact map_id A
    have hB : B < smallContainer 0 := by
      apply lt_of_le_of_ne
      · rintro _ ⟨x,hx,rfl⟩
        obtain ⟨y,hy,hyx⟩ := h hx
        have hy' : (MulAut.conj g⁻¹) x = y := by rw [← hyx]; simp [mul_assoc]
        exact hy' ▸ hy
      · intro hh
        exact he (hback.symm.trans (congrArg (fun C => C.map (MulAut.conj g).toMonoidHom) hh))
    obtain ⟨n,hn⟩ := proper_smallContainer_extends B hB
    have transfer (C : Subgroup M22) (hC : B ≤ C.map (MulAut.conj n).toMonoidHom) :
        A ≤ C.map (MulAut.conj (g*n)).toMonoidHom := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hC
      rwa [hback,conjugate_comp] at hh
    exact ⟨g*n,hn.imp (transfer _) (fun hh => Or.inl (transfer _ hh))⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
