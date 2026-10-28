module

public import Theory.GroupTheory.ConjugationFiberProduct.Quotient
public import Theory.GroupTheory.SelfCentralizingNormalFourComplement
import Theory.GroupTheory.PGroup.CriticalSubgroup

/-! Extensions with a common conjugation image, a four-element central
kernel and outer index six are isomorphic over the prescribed core map.
The diagonal fiber quotient has order24 and a self-centralizing normal
four-group. Its actual complement lifts to the graph of the equivalence.
This retains the central kernels and does not choose matching complements
in the original groups. -/

public noncomputable section
open Subgroup
namespace ConjugationFiberProduct
private theorem complement_restriction_bijective {F C : Type*} [Group F] [Group C]
  (p : F →* C) (L : Subgroup F)
    (hp : Function.Surjective p) (hLp : p.ker.IsComplement' L) :
    Function.Bijective (p.comp L.subtype) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hLp.disjoint.le_bot ⟨hx,x.property⟩)
  · intro c
    obtain ⟨x,rfl⟩ := hp c
    obtain ⟨⟨k,l⟩,hkl⟩ := hLp.2 x
    refine ⟨l,?_⟩
    change p l = p x
    rw [←hkl,map_mul,show p k = 1 from k.property,one_mul]

variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

/-- The common action determines the whole extension, retaining the given
core equivalence, when the residual diagonal quotient has the S₄ shape. -/
theorem exists_mulEquiv_of_four_kernel_index_six
    (N : Subgroup A) (M : Subgroup B) [N.Normal] [M.Normal] (d : N ≃* M)
    (hZ : Nat.card (center N) = 4)
    (hZC : centralizer ((center N).map N.subtype : Set A) ≤ N)
    (hcM : centralizer (M : Set B) ≤ M)
    (hi : N.index = 6)
    (himage : (action N M d).range = (MulAut.conjNormal : A →* MulAut N).range) :
    ∃ e : A ≃* B, ∀ n : N, e n = (d n : B) := by
  have hcN : centralizer (N : Set A) ≤ N := by
    apply le_trans _ hZC
    apply centralizer_le
    rintro _ ⟨z,_,rfl⟩
    exact z.property
  have hCM : Nat.card (centralizer (M : Set B)) = 4 := by
    have he : (center M).map M.subtype = centralizer (M : Set B) := by
      rw [map_center_subtype_eq_inf_centralizer,inf_eq_right.mpr hcM]
    rw [←he,card_map_of_injective M.subtype_injective,
      ←Nat.card_congr (centerCongr d).toEquiv]
    exact hZ
  have hQ : Nat.card (Quotient N M d) = 24 := by
    have h := (diagonal N M d).card_mul_index
    change Nat.card (diagonal N M d) * Nat.card (Quotient N M d) =
      Nat.card (fiber N M d) at h
    rw [card_diagonal,card_fiber N M d himage,hCM] at h
    have hA := N.card_mul_index
    rw [hi] at hA
    rw [←hA] at h
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N))
    calc
      Nat.card N * Nat.card (Quotient N M d) = 4 * (Nat.card N * 6) := h
      _ = Nat.card N * 24 := by omega
  have hK : Nat.card (kernelImage N M d) = 4 :=
    (Nat.card_congr (kernelImageEquiv N M d).toEquiv).symm.trans
      ((Nat.card_congr (fstKerEquiv N M d).toEquiv).trans hCM)
  obtain ⟨U,hU⟩ := exists_complement_of_selfCentralizing_normal_four (kernelImage N M d)
    (IsPGroup.of_card (p := 2) (n := 2) (by simpa using hK)) hK
    (kernelImage_selfCentralizing N M d hZC) hQ
  let f := fst N M d
  let g := snd N M d
  let q := quotientMap N M d
  let L := U.comap q
  have hL : f.ker.IsComplement' L := QuotientKernelComplement.complement_comap q f.ker U
    (by simpa only [q,quotientMap,QuotientGroup.ker_mk'] using
      (disjoint_diagonal_fst_ker N M d).symm) hU
  have hL' : g.ker.IsComplement' L := QuotientKernelComplement.complement_comap q g.ker U
    (by simpa only [q,quotientMap,QuotientGroup.ker_mk'] using
      (disjoint_diagonal_snd_ker N M d).symm)
    ((kernel_images_eq N M d hcN hcM) ▸ hU)
  let ef := MulEquiv.ofBijective (f.comp L.subtype) (complement_restriction_bijective f L (fst_surjective N M d himage) hL)
  let eg := MulEquiv.ofBijective (g.comp L.subtype) (complement_restriction_bijective g L (snd_surjective N M d himage) hL')
  refine ⟨ef.symm.trans eg,?_⟩
  intro n
  have hn : diagonalHom N M d n ∈ L := by
    change q (diagonalHom N M d n) ∈ U
    rw [quotientMap_diagonal]
    exact U.one_mem
  let l : L := ⟨diagonalHom N M d n,hn⟩
  change eg (ef.symm (ef l)) = (d n : B)
  rw [ef.symm_apply_apply]
  rfl

end ConjugationFiberProduct
