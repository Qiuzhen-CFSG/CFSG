module

public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A quotient by `U` is identified with a torus factor `T` once a
same-kernel comparison morphism restricts to an isomorphism on `T`. -/
public theorem quotient_iso_torus_of_comparison
    {K Q I : Variety k}
    [AlgebraicGroup K] [AlgebraicGroup Q] [AlgebraicGroup I]
    (U T : ClosedSubgroup K)
    (π : AlgebraicGroup.Morphism K Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = U.toSubgroup)
    (hfactor : ∀ x : Variety.Point K, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u)
    (hquot : ∀ {J : Variety k} (_ : AlgebraicGroup J)
      (φ : AlgebraicGroup.Morphism K J), U.toSubgroup ≤ φ.kernel →
      ∃! ψ : AlgebraicGroup.Morphism Q J, ψ.comp π = φ)
    (δ : AlgebraicGroup.Morphism K I)
    (hδker : U.toSubgroup ≤ δ.kernel)
    (eTI : AlgebraicGroup.Iso T.carrierVariety I)
    (heTI : eTI.hom = δ.comp T.inclusion) :
    ∃ e : AlgebraicGroup.Iso Q T.carrierVariety,
      ∀ t : Variety.Point T.carrierVariety,
        e.hom.onPoints (π.onPoints (T.inclusion.onPoints t)) = t := by
  obtain ⟨ψ, hψπ, _⟩ := hquot (inferInstance : AlgebraicGroup I) δ hδker
  have hψπ_point (x : Variety.Point K) :
      ψ.onPoints (π.onPoints x) = δ.onPoints x := by
    exact congrArg (fun f => f.onPoints x) hψπ
  let e : AlgebraicGroup.Iso Q T.carrierVariety :=
    { hom := eTI.inv.comp ψ
      inv := π.comp T.inclusion
      hom_inv_id := by
        intro q
        obtain ⟨x, rfl⟩ := hπsurj q
        obtain ⟨t, u, ht, hu, htu⟩ := hfactor x
        let tT : Variety.Point T.carrierVariety :=
          T.pointEquiv.symm ⟨t, ht⟩
        have htT : T.inclusion.onPoints tT = t := by
          change (T.pointEquiv tT).val = t
          simp [tT]
        have hπu : π.onPoints u = 1 := by
          change u ∈ π.kernel
          rw [hπker]
          exact hu
        have hδu : δ.onPoints u = 1 := by
          change u ∈ δ.kernel
          exact hδker hu
        have hδt : δ.onPoints t = eTI.hom.onPoints tT := by
          have h := congrArg (fun f => f.onPoints tT) heTI
          change eTI.hom.onPoints tT =
            δ.onPoints (T.inclusion.onPoints tT) at h
          rw [htT] at h
          exact h.symm
        have hehom :
            (eTI.inv.comp ψ).onPoints (π.onPoints x) = tT := by
          change eTI.inv.onPoints (ψ.onPoints (π.onPoints x)) = tT
          rw [hψπ_point]
          calc
            eTI.inv.onPoints (δ.onPoints x) =
                eTI.inv.onPoints (δ.onPoints (t * u)) := by rw [htu]
            _ = eTI.inv.onPoints
                (δ.onPoints t * δ.onPoints u) := by rw [map_mul]
            _ = eTI.inv.onPoints (δ.onPoints t) := by rw [hδu, mul_one]
            _ = eTI.inv.onPoints (eTI.hom.onPoints tT) := by rw [hδt]
            _ = tT := eTI.hom_inv_id tT
        change π.onPoints
            (T.inclusion.onPoints
              ((eTI.inv.comp ψ).onPoints (π.onPoints x))) = π.onPoints x
        rw [hehom, htT, htu, map_mul, hπu, mul_one]
      inv_hom_id := by
        intro t
        change eTI.inv.onPoints
            (ψ.onPoints (π.onPoints (T.inclusion.onPoints t))) = t
        rw [hψπ_point]
        have h := congrArg (fun f => f.onPoints t) heTI
        change eTI.hom.onPoints t =
          δ.onPoints (T.inclusion.onPoints t) at h
        rw [← h]
        exact eTI.hom_inv_id t }
  refine ⟨e, ?_⟩
  exact e.inv_hom_id

end Theory.AlgebraicGroup
