module
public import Theory.Representation.SL3.NaturalDualFixed
public import Theory.Representation.SemilinearFixedPointCentralizer
public import Theory.Representation.FiniteFieldSemilinearDisplacement

/-!
# The common field coefficient of an odd actor on a natural/dual pair

The two additive blocks induce the same automorphism of the original SL₃.
The scalar commutant constructs the natural coefficient, and evaluation
duality forces that same coefficient on the second block. A nontrivial
odd-prime coefficient moves at least four field degrees on the whole pair.
Otherwise both original blocks are field-linear.

Source: Aschbacher--Smith H.0.1 and H.4.1, printed pp.377 and379.
-/
public section
open Matrix Module Subgroup
namespace Representation.SL3NaturalFixed
open BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- An odd-prime actor with small paired displacement is linear on both
the natural space and its literal field dual. -/
theorem paired_odd_field_linear_of_small
    (β : Representation (ZMod 2) H (Fin 3 → F))
    (γ : Representation (ZMod 2) H (Module.Dual F (Fin 3 → F)))
    (α : H →* MulAut (SpecialLinearGroup (Fin 3) F))
    (hβ : ∀ x g v, β x (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (α x g) (β x v))
    (hγ : ∀ x g φ, γ x ((specialLinearNatural 3).dual g φ) =
      (specialLinearNatural 3).dual (α x g) (γ x φ))
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (x : H) (hx : orderOf x=p)
    (hsmall : fixedCodim (β.prod γ) (zpowers x) < 4*finrank (ZMod 2) F) :
    (∀ (c : F) v, β x (c • v)=c • β x v) ∧
      (∀ (c : F) φ, γ x (c • φ)=c • γ x φ) := by
  let b (y : H) := (LinearMap.GeneralLinearGroup.toLinearEquiv (β.asGroupHom y)).toAddEquiv
  let d (y : H) := (LinearMap.GeneralLinearGroup.toLinearEquiv (γ.asGroupHom y)).toAddEquiv
  have hs (y : H) : ∃ σ : F ≃+* F, ∀ c v, β y (c • v)=σ c • β y v :=
    semilinear_of_intertwines (b y) (α y) (hβ y)
  let π := SemilinearFixedPointCentralizer.coefficient β hs
  have hb (y : H) (c : F) (v : Fin 3 → F) : β y (c • v)=π y c • β y v :=
    SemilinearFixedPointCentralizer.coefficient_smul β hs y c v
  have hd (y : H) (c : F) (φ : Module.Dual F (Fin 3 → F)) :
      γ y (c • φ)=π y c • γ y φ :=
    paired_semilinear (b y) (d y) (α y) (π y) (hb y) (hβ y) (hγ y) c φ
  have hπ : π x=1 := by
    by_contra hne
    have horder : orderOf (π x)=p :=
      ((Nat.dvd_prime hp).mp (hx ▸ orderOf_map_dvd π x)).resolve_left
        (fun he => hne (orderOf_eq_one_iff.mp he))
    have hsemi (c : F) (v : (Fin 3 → F) × Module.Dual F (Fin 3 → F)) :
        (β.prod γ) x (c • v)=π x c • (β.prod γ) x v := Prod.ext (hb x c v.1) (hd x c v.2)
    have hbound := FiniteFieldSemilinearDisplacement.two_thirds_le_fixedCodim
      (β.prod γ) hp hodd x hx (π x) horder hsemi
    have hdim : finrank F ((Fin 3 → F) × Module.Dual F (Fin 3 → F))=6 := by
      rw [Module.finrank_prod]
      simp
    rw [hdim] at hbound
    omega
  constructor
  · intro c v
    simpa only [hπ,RingAut.one_apply] using hb x c v
  · intro c φ
    simpa only [hπ,RingAut.one_apply] using hd x c φ
end Representation.SL3NaturalFixed
