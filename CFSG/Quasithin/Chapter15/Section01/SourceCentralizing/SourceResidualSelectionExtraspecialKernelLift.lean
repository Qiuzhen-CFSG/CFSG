module

public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.GroupTheory.PGroup.ExtraspecialThreeActorGeneration

/-!
# A normal three-subgroup above the extraspecial action

An involution centralizing the action kernel lies in its normal centralizer.
If its image is a nontrivial center-fixing actor on the normal extraspecial
group of order 27, that centralizer maps onto the extraspecial group. The
restricted map has central kernel, so its three-core still maps onto it.

This supplies a normal three-subgroup in the quotient by the original
two-core, before any coprimality assertion about the action kernel.
Source application: Aschbacher--Smith 15.1.14, printed p.1091.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel

variable {A D : Type*} [Group A] [Finite A] [Group D] [Finite D]

/-- The three-core of the kernel centralizer covers the marked extraspecial
group. In particular, the lift is normal and centralizes the entire kernel. -/
theorem extraspecial_le_map_kernel_centralizer_threeCore
    (f : A →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (t : A)
    (htK : t ∈ centralizer (f.ker : Set A))
    (ht : (f t) ^ 2 = 1)
    (hne : (MulAut.conjNormal (f t) : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal (f t) : MulAut P) z = z) :
    P ≤ ((centralizer (f.ker : Set A)).pCoreIn 3).map f := by
  let C := centralizer (f.ker : Set A)
  let I := C.map f
  let : I.Normal := Normal.map inferInstance f hf
  have hPI : P ≤ I := IsExtraspecial.le_normal_of_center_fixing_involution
    P hP (f t) ht hne hcenter I ⟨t, htK, rfl⟩
  let g := f.subgroupMap C
  have hg : Function.Surjective g := f.subgroupMap_surjective C
  have hgK : g.ker ≤ center C := by
    intro x hx
    have hxK : (x : A) ∈ f.ker := by
      change g x = 1 at hx
      exact congrArg Subtype.val hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact (y.property x hxK).symm
  have hcore := g.map_pCore_of_central_kernel_centered (p := 3) hg hgK
  have hPIcore : P ≤ I.pCoreIn 3 :=
    le_pCoreIn_of_normalizes (IsExtraspecial.isPGroup 3 P) hPI le_normalizer_of_normal
  apply hPIcore.trans
  change (pCore 3 I).map I.subtype ≤ ((pCore 3 C).map C.subtype).map f
  rw [← hcore, map_map, map_map]
  exact le_rfl

/-- The normal three-core of the prequotient maps onto the marked
extraspecial group, without any prime-to-three kernel assumption. -/
theorem extraspecial_le_map_threeCore
    (f : A →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (t : A)
    (htK : t ∈ centralizer (f.ker : Set A))
    (ht : (f t) ^ 2 = 1)
    (hne : (MulAut.conjNormal (f t) : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal (f t) : MulAut P) z = z) :
    P ≤ (pCore 3 A).map f := by
  apply (extraspecial_le_map_kernel_centralizer_threeCore
    f hf P hP t htK ht hne hcenter).trans
  apply map_mono
  let : ((centralizer (f.ker : Set A)).pCoreIn 3).Normal :=
    inferInstanceAs (((pCore 3 (centralizer (f.ker : Set A))).map
      (centralizer (f.ker : Set A)).subtype).Normal)
  exact le_sSup ⟨inferInstance, isPGroup_pCoreIn 3 _⟩

/-- The same original actor moves the actual normal three-core of the
prequotient; this is the input needed by the rank-two centralizer theorem. -/
theorem not_centralizes_threeCore_of_extraspecial_image
    (f : A →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (t : A)
    (htK : t ∈ centralizer (f.ker : Set A))
    (ht : (f t) ^ 2 = 1)
    (hne : (MulAut.conjNormal (f t) : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal (f t) : MulAut P) z = z) :
    t ∉ centralizer (pCore 3 A : Set A) := by
  intro hc
  have hPc := extraspecial_le_map_threeCore f hf P hP t htK ht hne hcenter
  apply hne
  ext z
  obtain ⟨x, hx, he⟩ := hPc z.property
  have hcomm : (z : D) * f t = f t * z := by
    simpa only [map_mul, he] using congrArg f (hc x hx)
  change f t * (z : D) * (f t)⁻¹ = (z : D)
  rw [← hcomm, mul_inv_cancel_right]

/-- The usual source input expresses nontriviality by the order of the
action involution and self-centralization of the marked extraspecial group. -/
theorem not_centralizes_threeCore_of_selfCentralizing_extraspecial_image
    (f : A →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hCP : centralizer (P : Set D) ≤ P) (t : A)
    (htK : t ∈ centralizer (f.ker : Set A))
    (ht : orderOf (f t) = 2)
    (hcenter : f t ∈ centralizer ((center P).map P.subtype : Set D)) :
    t ∉ centralizer (pCore 3 A : Set A) := by
  have hne : (MulAut.conjNormal (f t) : MulAut P) ≠ 1 := by
    intro he
    have htCP : f t ∈ centralizer (P : Set D) := by
      intro x hx
      have hc := congrArg (fun a : MulAut P => ((a ⟨x, hx⟩ : P) : D)) he
      change f t * x * (f t)⁻¹ = x at hc
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    have hd := P.orderOf_dvd_natCard (hCP htCP)
    rw [ht, hP] at hd
    norm_num at hd
  apply not_centralizes_threeCore_of_extraspecial_image
    f hf P hP t htK (ht ▸ pow_orderOf_eq_one (f t)) hne
  intro z hz
  apply Subtype.ext
  change f t * (z : D) * (f t)⁻¹ = (z : D)
  rw [← hcenter z ⟨z, hz, rfl⟩, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
