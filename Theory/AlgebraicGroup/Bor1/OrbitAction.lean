module

public import Theory.AlgebraicGroup.RightTranslation.Exterior

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

omit [IsAlgClosed k] in
public lemma chevalleyPluckerPoint_stabilizer
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
      MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
    MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint = H.toSubgroup := by
  let : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
    MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
  ext g
  change g • H.rightTranslateVanishingPluckerPoint =
      H.rightTranslateVanishingPluckerPoint ↔ g ∈ H.toSubgroup
  rw [ClosedSubgroup.rightTranslateVanishingPluckerPoint]
  change H.rightTranslateVanishingExteriorGeneralLinear g •
      Projectivization.mk k H.rightTranslateVanishingPluckerVector _ =
        Projectivization.mk k H.rightTranslateVanishingPluckerVector _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  change (∃ a : k, a • H.rightTranslateVanishingPluckerVector =
      exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
        H.rightTranslateVanishingPluckerVector) ↔ _
  rw [← Submodule.mem_span_singleton]
  exact H.chevalleyPluckerLine_stabilizer_iff g

variable {Γ : Type*} [Group Γ]
variable {X : Type v} [MulAction Γ X]

omit [IsAlgClosed k] in
public lemma stabilizer_eq_ker_toPermHom_orbit_of_normal
    (x : X) (hN : (MulAction.stabilizer Γ x).Normal) :
    (MulAction.toPermHom Γ (MulAction.orbit Γ x)).ker =
      MulAction.stabilizer Γ x := by
  ext g
  constructor
  · intro hg
    change (MulAction.toPermHom Γ (MulAction.orbit Γ x)) g = 1 at hg
    have hbase := congrArg (fun σ : Equiv.Perm (MulAction.orbit Γ x) =>
      σ ⟨x, MulAction.mem_orbit_self x⟩) hg
    change g • x = x
    exact Subtype.ext_iff.mp hbase
  · intro hg
    change (MulAction.toPermHom Γ (MulAction.orbit Γ x)) g = 1
    apply Equiv.Perm.ext
    intro y
    obtain ⟨a, ha⟩ := y.2
    apply Subtype.ext
    change g • (y : X) = (y : X)
    rw [← ha]
    rw [← mul_smul]
    have hconj : a⁻¹ * g * a ∈ MulAction.stabilizer Γ x := by
      simpa [mul_assoc] using hN.conj_mem g hg a⁻¹
    have hfix : (a⁻¹ * g * a) • x = x := hconj
    calc
      (g * a) • x = (a * (a⁻¹ * g * a)) • x := by
        congr 1
        simp [mul_assoc]
      _ = a • ((a⁻¹ * g * a) • x) := by rw [mul_smul]
      _ = a • x := by rw [hfix]

omit [IsAlgClosed k] in
public lemma chevalleyPluckerOrbitAction_ker
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
      MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
    (MulAction.toPermHom (Variety.Point G)
      (MulAction.orbit (Variety.Point G)
        H.rightTranslateVanishingPluckerPoint)).ker = H.toSubgroup := by
  let : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
    MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
  have hstab : MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint = H.toSubgroup :=
    chevalleyPluckerPoint_stabilizer H
  have hstabN : (MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint).Normal := by
    rw [hstab]
    exact hN
  calc
    (MulAction.toPermHom (Variety.Point G)
      (MulAction.orbit (Variety.Point G)
        H.rightTranslateVanishingPluckerPoint)).ker =
        MulAction.stabilizer (Variety.Point G)
          H.rightTranslateVanishingPluckerPoint :=
      stabilizer_eq_ker_toPermHom_orbit_of_normal
        H.rightTranslateVanishingPluckerPoint hstabN
    _ = H.toSubgroup := hstab

end Theory.AlgebraicGroup.Bor1
