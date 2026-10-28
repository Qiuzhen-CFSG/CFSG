module

public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.RootSubgroups.CocharacterExistence

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A root datum identified with the character lattice of a subtorus realizes
every coroot by an algebraic cocharacter. -/
public theorem exists_rootCocharacters_of_rootDatumRealization
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hT : IsSubtorus T) (D : RootGroupData K T)
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hDatum : IsRootDatumRealization D P e weightEquiv) :
    ∃ h : D.Root → ClosedSubgroupTorusCocharacter T,
      ∀ α β, WeightCocharacterEquation T (D.rootWeight α) (h β)
        (P.pairing (e α) (e β)) := by
  let weightAddEquiv : X ≃+ Additive (TorusWeight T) :=
    (AddEquiv.additiveMultiplicative X).symm.trans weightEquiv.toAdditive
  let φ : D.Root → Additive (TorusWeight T) →+ ℤ := fun β =>
    (P.coroot' (e β)).toAddMonoidHom.comp weightAddEquiv.symm.toAddMonoidHom
  have hφ (α β : D.Root) :
      φ β (Additive.ofMul (D.rootWeight α)) = P.pairing (e α) (e β) := by
    change P.coroot' (e β)
      (weightAddEquiv.symm (Additive.ofMul (D.rootWeight α))) = _
    have hweight : weightAddEquiv.symm
        (Additive.ofMul (D.rootWeight α)) = P.root (e α) := by
      apply weightAddEquiv.injective
      rw [weightAddEquiv.apply_symm_apply]
      change Additive.ofMul (D.rootWeight α) =
        Additive.ofMul (weightEquiv (Multiplicative.ofAdd (P.root (e α))))
      rw [hDatum α]
    rw [hweight]
    exact P.root_coroot_eq_pairing (e α) (e β)
  have hexists (β : D.Root) :
      ∃ h : ClosedSubgroupTorusCocharacter T,
        ∀ χ, WeightCocharacterEquation T χ h (φ β (Additive.ofMul χ)) :=
    exists_cocharacter_realizing_characterFunctional T hT (φ β)
  choose h hh using hexists
  refine ⟨h, ?_⟩
  intro α β
  rw [← hφ α β]
  exact hh β (D.rootWeight α)

end Theory.AlgebraicGroup
