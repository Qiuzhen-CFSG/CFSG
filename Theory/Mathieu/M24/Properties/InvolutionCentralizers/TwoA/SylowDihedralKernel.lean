module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels

/-!
# A dihedral quotient of each native Mathieu Sylow with its full kernel

The marked two-central centralizer maps onto PSL3(2) with the literal
order-128 kernel. Its Sylow image is dihedral of order eight, and the full
kernel lies inside the centralizer Sylow. That Sylow has the full ambient
two-part, so Sylow conjugacy transports the quotient homomorphism to every
specified Sylow of M24. The kernel remains self-centralizing and isomorphic
to the entire marked kernel.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private theorem centralizer_sylow_dihedral (R : Sylow 2 centralizer2A) :
    ∃ π : R →* DihedralGroup 4, Function.Surjective π ∧
      centralizer (π.ker : Set R) ≤ π.ker ∧ Nonempty (π.ker ≃* kernel) := by
  let q : centralizer2A →* Matrix.PSL3Two.PSL :=
    quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' kernel)
  have hq : Function.Surjective q := quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective kernel)
  have hk : q.ker = kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ quotientEquiv.injective,
      QuotientGroup.ker_mk']
  obtain ⟨e⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral
    (R.mapSurjective hq)
  let r : R →* R.mapSurjective hq := q.subgroupMap (R : Subgroup centralizer2A)
  let π : R →* DihedralGroup 4 := e.toMonoidHom.comp r
  have hker : π.ker = kernel.subgroupOf R := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    change (q.subgroupMap (R : Subgroup centralizer2A)).ker = _
    rw [Subgroup.ker_subgroupMap,hk]
  have hKR : kernel ≤ (R : Subgroup centralizer2A) :=
    kernel_isTwoGroup.le_sylow_of_normal R
  refine ⟨π,e.surjective.comp (q.subgroupMap_surjective _),?_,
    ⟨(MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hKR)⟩⟩
  rw [hker]
  intro x hx
  apply kernel_selfCentralizing
  intro y hy
  exact congrArg Subtype.val (hx ⟨y,hKR hy⟩ hy)

/-- Every native M24 Sylow maps onto D8 with a self-centralizing kernel
isomorphic to the entire literal two-central kernel. -/
theorem exists_sylow_dihedral_kernel (S : Sylow 2 M24) :
    ∃ π : S →* DihedralGroup 4, Function.Surjective π ∧
      centralizer (π.ker : Set S) ≤ π.ker ∧ Nonempty (π.ker ≃* kernel) := by
  let R : Sylow 2 centralizer2A := Classical.choice inferInstance
  let R₀ := (R : Subgroup centralizer2A).map centralizer2A.subtype
  have hRc : Nat.card R₀ = 1024 := by
    rw [card_map_of_injective centralizer2A.subtype_injective,R.card_eq_multiplicity,
      centralizer_card]
    decide +kernel
  let S₀ : Sylow 2 M24 := Sylow.ofCard R₀ (by rw [hRc,m24_order]; decide +kernel)
  let e₀ : R ≃* S₀ := (R : Subgroup centralizer2A).equivMapOfInjective
    centralizer2A.subtype centralizer2A.subtype_injective
  let e : S ≃* R := (S.equiv S₀).trans e₀.symm
  obtain ⟨f,hf,hC,⟨eK⟩⟩ := centralizer_sylow_dihedral R
  let π : S →* DihedralGroup 4 := f.comp e.toMonoidHom
  have hk : π.ker.map e.toMonoidHom = f.ker := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      change f (e (e.symm x)) = 1
      rw [e.apply_symm_apply]
      exact hx
  let eπ : π.ker ≃* f.ker :=
    (π.ker.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hk)
  refine ⟨π,hf.comp e.surjective,?_,⟨eπ.trans eK⟩⟩
  intro x hx
  apply hC
  intro y hy
  have hpre : e.symm y ∈ π.ker := by
    change f (e (e.symm y)) = 1
    rw [e.apply_symm_apply]
    exact hy
  have hc := congrArg e (hx (e.symm y) hpre)
  change y * e x = e x * y
  simpa only [map_mul,e.apply_symm_apply] using hc

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
