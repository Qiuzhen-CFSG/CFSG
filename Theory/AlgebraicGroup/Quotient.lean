module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic

universe u v

/-!
The abstract quotient-group universal property for closed normal subgroups.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- A monoid homomorphism killing a normal subgroup factors uniquely through
the group quotient. -/
public theorem quotientGroup_factorization_existsUnique
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∀ {M : Type*} [Monoid M]
      (φ : Variety.Point G →* M),
      H.toSubgroup ≤ φ.ker →
        ∃! ψ : (Variety.Point G ⧸ H.toSubgroup) →* M,
          ψ.comp (QuotientGroup.mk' H.toSubgroup) = φ := by
  let : H.toSubgroup.Normal := hN
  let q : Variety.Point G →* (Variety.Point G ⧸ H.toSubgroup) :=
    QuotientGroup.mk' H.toSubgroup
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective _
  intro M _ φ hφ
  let ψ : (Variety.Point G ⧸ H.toSubgroup) →* M :=
    QuotientGroup.lift H.toSubgroup φ hφ
  refine ⟨ψ, ?_, ?_⟩
  · apply MonoidHom.ext
    intro x
    simp [ψ]
  · intro ψ' hψ'
    apply MonoidHom.ext
    intro y
    rcases hq_surj y with ⟨x, rfl⟩
    have h₁ := congrArg (fun m : Variety.Point G →* M => m x) hψ'
    calc
      ψ' (q x) = φ x := by
        change ψ' (↑x) = φ x
        exact h₁
      _ = ψ (q x) := by
        symm
        simp [ψ, q]

/-! A surjective homomorphism on a normal supplement extends across the subgroup join. -/

section

/-- If a surjective homomorphism on `N` has kernel `H ∩ N`, where `H` is
normal in the ambient group, then it extends to `H ⊔ N`, kills exactly `H`,
and retains its original values on `N`. -/
public lemma Subgroup.exists_surjective_supHom_of_ker_eq_subgroupOf
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (H N : Subgroup G) [H.Normal]
    (φ : N →* Q) (hφ : Function.Surjective φ)
    (hker : H.subgroupOf N = φ.ker) :
    ∃ ψ : (H ⊔ N : Subgroup G) →* Q,
      Function.Surjective ψ ∧
      ψ.ker = H.subgroupOf (H ⊔ N) ∧
      ∀ n : N, ψ (Subgroup.inclusion le_sup_right n) = φ n := by
  let eSecond := QuotientGroup.quotientInfEquivProdNormalQuotient N H
  let ePhi := QuotientGroup.liftEquiv (H.subgroupOf N) hφ hker
  let ψ' : (N ⊔ H : Subgroup G) →* Q :=
    ePhi.toMonoidHom.comp
      (eSecond.symm.toMonoidHom.comp
        (QuotientGroup.mk' (H.subgroupOf (N ⊔ H))))
  have hψ'surj : Function.Surjective ψ' :=
    ePhi.surjective.comp (eSecond.symm.surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hψ'ker : ψ'.ker = H.subgroupOf (N ⊔ H) := by
    ext x
    change ψ' x = 1 ↔ x ∈ H.subgroupOf (N ⊔ H)
    change ePhi (eSecond.symm (QuotientGroup.mk' _ x)) = 1 ↔ _
    rw [ePhi.map_eq_one_iff, eSecond.symm.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hψ'restrict : ∀ n : N,
      ψ' (Subgroup.inclusion le_sup_left n) = φ n := by
    intro n
    change ePhi (eSecond.symm
      (QuotientGroup.mk' (H.subgroupOf (N ⊔ H))
        (Subgroup.inclusion le_sup_left n))) = φ n
    calc
      _ = ePhi (QuotientGroup.mk' (H.subgroupOf N) n) := by
        congr 1
        apply eSecond.injective
        rw [eSecond.apply_symm_apply]
        rfl
      _ = φ n := QuotientGroup.liftEquiv_mk (H.subgroupOf N) hφ hker n
  let eSup : (H ⊔ N : Subgroup G) ≃* (N ⊔ H : Subgroup G) :=
    { toFun := fun x => ⟨x, by rw [sup_comm]; exact x.property⟩
      invFun := fun x => ⟨x, by rw [sup_comm]; exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let ψ : (H ⊔ N : Subgroup G) →* Q := ψ'.comp eSup.toMonoidHom
  refine ⟨ψ, hψ'surj.comp eSup.surjective, ?_, ?_⟩
  · ext x
    change ψ' (eSup x) = 1 ↔ x ∈ H.subgroupOf (H ⊔ N)
    rw [← MonoidHom.mem_ker, hψ'ker]
    rfl
  · intro n
    change ψ' (eSup (Subgroup.inclusion le_sup_right n)) = φ n
    exact hψ'restrict n

end

/-! Point-group lifts along surjective morphisms with prescribed kernel. -/

section

variable {k : Type u} [Field k]

public lemma Morphism.pointLift_existsUnique_of_surjective_kernel
    {G Q I : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (hN : H.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism G Q) (hπ : Function.Surjective π.onPoints)
    (hker : π.kernel = H.toSubgroup)
    (φ : AlgebraicGroup.Morphism G I) (hφ : H.toSubgroup ≤ φ.kernel) :
    ∃! ψ : Variety.Point Q →* Variety.Point I, ψ.comp π.onPoints = φ.onPoints := by
  let : H.toSubgroup.Normal := hN
  obtain ⟨θ, hθ, -⟩ :=
    quotientGroup_factorization_existsUnique H hN φ.onPoints hφ
  let : π.kernel.Normal := MonoidHom.normal_ker π.onPoints
  let e : (Variety.Point G ⧸ H.toSubgroup) ≃* Variety.Point Q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π.onPoints hπ)
  let ψ : Variety.Point Q →* Variety.Point I := θ.comp e.symm.toMonoidHom
  have hψ : ψ.comp π.onPoints = φ.onPoints := by
    apply MonoidHom.ext
    intro x
    change θ (e.symm (π.onPoints x)) = φ.onPoints x
    have he : e (QuotientGroup.mk x) = π.onPoints x := by
      change QuotientGroup.quotientKerEquivOfSurjective π.onPoints hπ
        (QuotientGroup.quotientMulEquivOfEq hker.symm (QuotientGroup.mk x)) = π.onPoints x
      rw [QuotientGroup.quotientMulEquivOfEq_mk]
      rfl
    rw [← he, e.symm_apply_apply]
    exact congrArg (fun m : Variety.Point G →* Variety.Point I => m x) hθ
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply MonoidHom.ext
  intro y
  rcases hπ y with ⟨x, rfl⟩
  have hx := congrArg (fun m : Variety.Point G →* Variety.Point I => m x) hψ'
  have hψx := congrArg (fun m : Variety.Point G →* Variety.Point I => m x) hψ
  exact hx.trans hψx.symm

end
end Theory.AlgebraicGroup

