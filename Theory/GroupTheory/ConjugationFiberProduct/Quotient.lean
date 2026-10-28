module

public import Theory.GroupTheory.ConjugationFiberProduct

/-!
# The central kernel in the diagonal action quotient

The diagonal meets either projection kernel trivially. Thus its quotient
retains an isomorphic copy of either kernel. If the first core is exactly
the centralizer of its center, this kernel image is self-centralizing:
centralization in the quotient lifts because the diagonal has trivial
intersection with the projection kernel; compatibility then places the first
coordinate in the core, where a diagonal correction kills it.
-/

@[expose] public section
noncomputable section
namespace ConjugationFiberProduct
open Subgroup
variable {A B : Type*} [Group A] [Group B]
variable (N : Subgroup A) (M : Subgroup B) [N.Normal] [M.Normal] (d : N ≃* M)

instance kernelImage_normal : (kernelImage N M d).Normal :=
  Subgroup.Normal.map inferInstance (quotientMap N M d)
    (QuotientGroup.mk'_surjective _)

/-- The first central kernel survives the diagonal quotient injectively. -/
def kernelImageEquiv : (fst N M d).ker ≃* kernelImage N M d := by
  let f : (fst N M d).ker →* kernelImage N M d :=
    ((quotientMap N M d).comp (fst N M d).ker.subtype).codRestrict _
      (fun x => ⟨x,x.property,rfl⟩)
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_antisymm _ bot_le
    intro x hx
    have hxD : x.val ∈ diagonal N M d :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    exact Subtype.ext ((disjoint_diagonal_fst_ker N M d).le_bot ⟨hxD,x.property⟩)
  · rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩

private theorem right_center_mem (z : center N) :
    (1,(d z.val : B)) ∈ fiber N M d := by
  change MulAut.conjNormal (1 : A) = action N M d (d z.val)
  rw [map_one]
  apply MulEquiv.ext
  intro n
  apply d.injective
  rw [action_apply]
  change d n = d z.val * d n * (d z.val)⁻¹
  have he : d z.val * d n = d n * d z.val := by
    simpa only [map_mul] using congrArg d ((mem_center_iff.mp z.property n).symm)
  rw [he,mul_inv_cancel_right]

/-- Faithfulness on the center of the first core becomes self-centralization
of the retained central kernel in the diagonal quotient. -/
theorem kernelImage_selfCentralizing
    (hc : centralizer ((center N).map N.subtype : Set A) ≤ N) :
    centralizer (kernelImage N M d : Set (Quotient N M d)) ≤ kernelImage N M d := by
  intro v hv
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (diagonal N M d) v
  have ha : fst N M d x ∈ N := by
    apply hc
    rw [mem_centralizer_iff]
    rintro _ ⟨z,hz,rfl⟩
    let k : fiber N M d := ⟨(1,(d z : B)),right_center_mem N M d ⟨z,hz⟩⟩
    have hk : k ∈ (fst N M d).ker := rfl
    have he : quotientMap N M d k * quotientMap N M d x =
        quotientMap N M d x * quotientMap N M d k :=
      mem_centralizer_iff.mp hv _ ⟨k,hk,rfl⟩
    let w := k*x*(x*k)⁻¹
    have hwD : w ∈ diagonal N M d := by
      apply (QuotientGroup.eq_one_iff _).mp
      change quotientMap N M d (k*x*(x*k)⁻¹) = 1
      rw [map_mul,map_mul,map_inv,map_mul,he,mul_inv_cancel]
    have hwK : w ∈ (fst N M d).ker := by
      change fst N M d (k*x*(x*k)⁻¹) = 1
      rw [map_mul,map_mul,map_inv,map_mul,show fst N M d k = 1 from hk,
        one_mul,mul_one,mul_inv_cancel]
    have hw : w = 1 := (disjoint_diagonal_fst_ker N M d).le_bot ⟨hwD,hwK⟩
    have heq : k*x = x*k := mul_inv_eq_one.mp hw
    have hb : (d z : B) * snd N M d x = snd N M d x * (d z : B) :=
      congrArg (snd N M d) heq
    have hfix : MulAut.conjNormal (snd N M d x) (d z) = d z := by
      apply Subtype.ext
      change snd N M d x * (d z : B) * (snd N M d x)⁻¹ = (d z : B)
      rw [← hb,mul_inv_cancel_right]
    have hefix := compatible N M d x z
    rw [hfix] at hefix
    have hfixA := congrArg Subtype.val (d.injective hefix)
    change fst N M d x * (z : A) * (fst N M d x)⁻¹ = z at hfixA
    exact (mul_inv_eq_iff_eq_mul.mp hfixA).symm
  let n : N := ⟨fst N M d x,ha⟩
  let y := x * (diagonalHom N M d n)⁻¹
  refine ⟨y,?_,?_⟩
  · change fst N M d (x * (diagonalHom N M d n)⁻¹) = 1
    rw [map_mul,map_inv]
    exact mul_inv_cancel _
  · simp only [y,map_mul,map_inv,quotientMap_diagonal,inv_one,mul_one]
    rfl

end ConjugationFiberProduct
