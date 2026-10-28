module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Quotient
public import Theory.GroupTheory.CoreFreeAbelianComplement

/-!
# Normal Sylow subgroups in conjugate unique maximal overgroups

In a finite solvable group, let `M` be the unique maximal overgroup of a Sylow
`2`-subgroup `T`. If `U ≤ T` is normalized by `T` and lies in a conjugate of
`M`, then either `U` lies in the normal core of `M` or that conjugate is `M`.

Quotient by the normal core and apply `quotientCoreFree_data`. Its normal
elementary abelian complement has trivial intersection with the maximal image
and generates the quotient together with the Sylow image. A product
decomposition therefore identifies those two images. The image of `U` is
normalized by the maximal image, so the core-free complement theorem applies.
Finally, lift triviality of the image of `U`, or equality of the conjugates,
using that the normal core lies in every conjugate of `M`.

This supplies the finite-group transfer behind the opposite generating
equality in Stellmacher, Journal of Algebra 190 (1997), proof of (9.2), p. 48.
It uses the primitive quotient from (3.3), not (9.2) or its consequences.
-/

namespace Stellmacher.SectionThree

open scoped Pointwise IsMulCommutative

universe u

private theorem map_conjugate {Q R : Type u} [Group Q] [Group R]
    (f : Q →* R) (B : Subgroup Q) (actor : Q) :
    (B.conjBy actor).map f = (B.map f).conjBy (f actor) := by
  simp only [Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

public theorem normal_sylow_subgroup_le_conjugate_unique_maximal
    {Q : Type u} [Group Q] [Finite Q]
    (hsolv : Group.IsSolvable Q) (T : Sylow 2 Q) (M U : Subgroup Q)
    (hM : IsCoatom M) (hTM : (T : Subgroup Q) ≤ M)
    (hunique : ∀ M' : Subgroup Q, IsCoatom M' → (T : Subgroup Q) ≤ M' → M' = M)
    (hUT : U ≤ (T : Subgroup Q)) (hnormal : (T : Subgroup Q) ≤ Subgroup.normalizer U)
    (actor : Q) (hactor : U ≤ M.conjBy actor) :
    U ≤ M.normalCore ∨ M.conjBy actor = M := by
  classical
  let N := M.normalCore
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  let B := M.map q
  let S := (T : Subgroup Q).map q
  let V := U.map q
  have hcomapB : B.comap q = M := by
    simpa [B, q, N, QuotientGroup.ker_mk', sup_eq_left.2 M.normalCore_le] using
      (Subgroup.comap_map_eq q M)
  have hB : IsCoatom B := by
    refine ⟨?_, ?_⟩
    · intro htop
      apply hM.ne_top
      rw [← hcomapB, htop]
      simp
    · intro D hBD
      have hMlt : M < D.comap q := by
        refine lt_of_le_of_ne ?_ ?_
        · intro x hx
          exact hBD.le (Subgroup.mem_map_of_mem q hx)
        · intro heq
          apply hBD.ne
          apply le_antisymm hBD.le
          intro x hx
          obtain ⟨y, rfl⟩ := hqsurj x
          have hy : y ∈ D.comap q := hx
          rw [← heq] at hy
          exact Subgroup.mem_map_of_mem q hy
      have hDtop := hM.2 (D.comap q) hMlt
      apply top_unique
      intro x _
      obtain ⟨y, rfl⟩ := hqsurj x
      have hy : y ∈ D.comap q := by rw [hDtop]; trivial
      exact hy
  have hcore : B.normalCore = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨y, rfl⟩ := hqsurj x
    have hnormalCore : (B.normalCore.comap q).Normal := inferInstance
    have hleM : B.normalCore.comap q ≤ M := by
      exact (Subgroup.comap_mono B.normalCore_le).trans hcomapB.le
    have hleN : B.normalCore.comap q ≤ N :=
      @Subgroup.normal_le_normalCore Q _ M _ hnormalCore |>.mpr hleM
    exact (QuotientGroup.eq_one_iff y).2 (hleN hx)
  obtain ⟨prime, K, _, _, hKnormal, hKelem, hKB, hKS, _⟩ :=
    Stellmacher.SectionThree.quotientCoreFree_data (T : Subgroup Q) M T rfl
      hM hTM hunique hsolv
  let _ : K.Normal := hKnormal
  let _ : IsElementaryAbelian prime K := hKelem
  change K ⊓ B = ⊥ at hKB
  have hSB : S ≤ B := Subgroup.map_mono hTM
  have hBS : B ≤ S := by
    intro x hx
    have hxtop : x ∈ K ⊔ S := by rw [hKS]; trivial
    have hprod : (↑(K ⊔ S) : Set (Q ⧸ N)) = (K : Set (Q ⧸ N)) * S :=
      Subgroup.coe_mul_of_right_le_normalizer_left K S Subgroup.le_normalizer_of_normal
    change x ∈ (↑(K ⊔ S) : Set (Q ⧸ N)) at hxtop
    rw [hprod] at hxtop
    obtain ⟨k, hk, s, hs, hks⟩ := hxtop
    have hkB : k ∈ B := by
      have hmem := B.mul_mem hx (B.inv_mem (hSB hs))
      simpa [← hks, mul_assoc] using hmem
    have hkone : k = 1 := by
      have hkbot : k ∈ K ⊓ B := ⟨hk, hkB⟩
      simpa [hKB] using hkbot
    simpa [← hks, hkone] using hs
  have hBeq : B = S := le_antisymm hBS hSB
  have hVB : V ≤ B := Subgroup.map_mono (hUT.trans hTM)
  have hBnorm : B ≤ Subgroup.normalizer V := by
    rw [hBeq]
    exact (Subgroup.map_mono hnormal).trans (Subgroup.le_normalizer_map q)
  have hKBtop : K ⊔ B = ⊤ := by rw [hBeq]; exact hKS
  have hVactor : V ≤ B.conjBy (q actor) := by
    rw [← map_conjugate]
    exact Subgroup.map_mono hactor
  rcases Subgroup.normal_subgroup_le_conjugate_corefree_complement
      K B V hKnormal inferInstance hB hcore hKB hKBtop hVB hBnorm
      (q actor) hVactor with hVbot | hBeqconj
  · left
    intro x hx
    have hqx : q x ∈ V := Subgroup.mem_map_of_mem q hx
    have hqxone : q x = 1 := by simpa [hVbot] using hqx
    exact (QuotientGroup.eq_one_iff x).1 hqxone
  · right
    have hNconj : N ≤ M.conjBy actor := by
      intro x hx
      apply Subgroup.mem_map.mpr
      refine ⟨actor⁻¹ * x * actor, ?_, ?_⟩
      · apply M.normalCore_le
        simpa using (inferInstance : N.Normal).conj_mem x hx actor⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
    have hcomapConj : ((M.conjBy actor).map q).comap q = M.conjBy actor := by
      simpa [q, QuotientGroup.ker_mk', sup_eq_left.2 hNconj] using
        (Subgroup.comap_map_eq q (M.conjBy actor))
    rw [← hcomapConj, map_conjugate, hBeqconj, hcomapB]

end Stellmacher.SectionThree

