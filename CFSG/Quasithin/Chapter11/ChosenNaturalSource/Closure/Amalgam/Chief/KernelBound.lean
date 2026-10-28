module

public import Theory.GroupTheory.CComponent.NormalizerTwoCore
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.KernelSetup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Transport

/-!
# The actual exceptional-component action kernel

The kernel C_K(U) is normal in K and normalizes L₁ by the preceding
uniqueness argument. Since L₁ is a proper perfect subgroup with simple
quotient by its two-core, C-component minimality makes that kernel central
modulo O₂(K). The result uses the literal embedded quotient center and does
not assert ambient normality of K in G.

The local rank-one marking is an earlier source premise from
qt-d-1222-natural-flag-cartan; relative-component status is supplied by
qt-d-1222-natural-relative-components. The surviving chief-section
construction remains with qt-d-1222-amalgam-chief-section.
Source: Aschbacher--Smith, last paragraph of 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- The literal source two-center bound, using the local rank-one quotient. -/
theorem K_centralizer_le_two_center (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    [IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁)] :
    E.K ⊓ centralizer (localClosure E : Set G) ≤
      ((center (E.K ⧸ pCore 2 E.K)).comap (QuotientGroup.mk' (pCore 2 E.K))).map
        E.K.subtype := by
  let A := E.L₁.subgroupOf E.K
  let N := (centralizer (localClosure E : Set G)).subgroupOf E.K
  let e : A ≃* E.L₁ := subgroupOfEquivOfLe hlt.le
  let : Group.IsPerfect E.L₁ := by
    change Group.IsPerfect ((solvableResidual (L ⊓ E.G₁ : Subgroup G)).map (L ⊓ E.G₁).subtype)
    exact Group.IsPerfect.map _
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let eqt := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eqt.isSimpleGroup
  have hAn : N ≤ normalizer (A : Set E.K) := by
    apply le_normalizer_iff.mpr
    intro n hn a ha
    exact le_normalizer_iff.mp (K_centralizer_normalizes_L₁ E h)
      (n : G) ⟨n.property, hn⟩ (a : G) ha
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((show E.K ≤ KT E from le_sup_left).trans
      ((le_normalizer_conjugateSpanBy V (KT E)).trans
        (normalizer_le_normalizer_centralizer (localClosure E))))
  have hAt : A ≠ ⊤ := by
    intro he
    exact hlt.not_ge (subgroupOf_eq_top.mp he)
  have hbound := normalizer_kernel_le_two_center_of_simple_quotient
    (Models.component_top E hK) A N hAt hAn
  intro x hx
  exact ⟨⟨x,hx.1⟩, hbound hx.2, rfl⟩

/-- The literal rank-one marking from the flag calculations supplies simplicity. -/
theorem K_centralizer_le_two_center_of_rank_one (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree)) :
    E.K ⊓ centralizer (localClosure E : Set G) ≤
      ((center (E.K ⧸ pCore 2 E.K)).comap (QuotientGroup.mk' (pCore 2 E.K))).map
        E.K.subtype := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := hlocal
  have hlarge : 4 ≤ Nat.card F := by
    rw [hcard]
    change (2 : ℕ)^2 ≤ 2 ^ E.input.field.degree
    exact Nat.pow_le_pow_right (by decide) (by have := E.input.nonbinary; omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := e.isSimpleGroup
  exact K_centralizer_le_two_center E h hK hlt

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
