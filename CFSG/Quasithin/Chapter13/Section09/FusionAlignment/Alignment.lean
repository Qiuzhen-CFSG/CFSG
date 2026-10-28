module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.WeakClosure
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The residual after marked factor alignment

The literal subgroup `C_K(t)` is `N_G(B) ∩ C_G(t)`. An actual direct-product
splitting into subgroups `R₁,X` of the original ambient group retains the
equation multiplying their two coordinates back to the original element.
Its first coordinate kills the two-residual, so that residual lies in `X`.
The second coordinate and the marked `X ≃ S₄` identify it with `A₄`.

The final application obtains `E ≤ R₁` using the weak-closure contradiction
and derives centralization of this literal residual. The independent local
splitting and contrary-alignment witness construction remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.10, printed p.973 (PDF p.990).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section09.FusionAlignment

open Subgroup

variable {G : Type*} [Group G]

/-- The literal `C_K(t)`, with `K = N_G(B)`. -/
abbrev normalizerCentralizer (B : Subgroup G) (t : G) : Subgroup G :=
  normalizer (B : Set G) ⊓ centralizer ({t} : Set G)

/-- The two-residual, embedded through the original centralizer's inclusion. -/
def normalizerCentralizerResidual (B : Subgroup G) (t : G) : Subgroup G :=
  (pResidual 2 (normalizerCentralizer B t)).map (normalizerCentralizer B t).subtype

/-- A marked splitting implies that the actual residual lies in its second
factor, rather than merely in an abstract isomorphic group. -/
theorem residual_le_second_factor (B R₁ X : Subgroup G) (t : G)
    (split : normalizerCentralizer B t ≃* R₁ × X) (hR : IsPGroup 2 R₁)
    (hcoordinates : ∀ x : normalizerCentralizer B t,
      (x : G) = ((split x).1 : G) * ((split x).2 : G)) :
    normalizerCentralizerResidual B t ≤ X := by
  rintro _ ⟨x, hx, rfl⟩
  change (x : G) ∈ X
  have hfirst := fst_eq_one_of_mem_pResidual 2 split hR hx
  rw [hcoordinates x, hfirst, Subgroup.coe_one, one_mul]
  exact (split x).2.property

/-- The actual centralizer residual is A₄, once the source's marked
two-group/S₄ splitting has been constructed. -/
noncomputable def normalizerCentralizerResidualEquiv [Finite G]
    (B R₁ X : Subgroup G) (t : G)
    (split : normalizerCentralizer B t ≃* R₁ × X)
    (hR : IsPGroup 2 R₁) (eX : X ≃* Equiv.Perm (Fin 4)) :
    normalizerCentralizerResidual B t ≃* alternatingGroup (Fin 4) :=
  ((pResidual 2 (normalizerCentralizer B t)).equivMapOfInjective
      (normalizerCentralizer B t).subtype (normalizerCentralizer B t).subtype_injective).symm |>.trans
    ((pResidualEquivOfPGroupFactor 2 split hR).trans
      (((pResidual 2 X).equivMapOfInjective eX.toMonoidHom eX.injective).trans
        (MulEquiv.subgroupCongr ((map_pResidual 2 eX).trans
          (Equiv.Perm.twoResidual_eq_alternating (Fin 4))))))

/-- The conditional 13.9.10 assembly on the original `E = T₁ ∩ A`, where
`T₁ = T ∩ M₁` and `A = O₂(M)`. No centralization premise about E is used. -/
theorem centralizes_residual_of_marked_splitting [Finite G]
    (d : Configuration G) (M₁ B Q R₁ X : Subgroup G) (z t : G)
    (hBT : B ≤ (d.T : Subgroup G))
    (hweak : ∀ a : G, B.map (MulAut.conj a).toMonoidHom ≤ (d.T : Subgroup G) →
      B.map (MulAut.conj a).toMonoidHom = B)
    (hzB : z ∈ B) (hC : centralizer (B ⊓ Q : Set G) = B)
    (split : normalizerCentralizer B t ≃* R₁ × X) (hR : IsPGroup 2 R₁)
    (hcoordinates : ∀ x : normalizerCentralizer B t,
      (x : G) = ((split x).1 : G) * ((split x).2 : G))
    (hcomm : R₁ ≤ centralizer (X : Set G))
    (hwitness : ¬ ((d.T : Subgroup G) ⊓ M₁) ⊓ d.M.pCoreIn 2 ≤ R₁ →
      ∃ (g : G) (D : Subgroup G), MulAut.conj g z ∉ B ∧
        D ≤ centralizer
          (B.map (MulAut.conj g).toMonoidHom ⊓ Q.map (MulAut.conj g).toMonoidHom : Set G) ∧
        Nat.card D = Nat.card B ∧ D ≤ normalizer (B : Set G)) :
    ((d.T : Subgroup G) ⊓ M₁) ⊓ d.M.pCoreIn 2 ≤
      centralizer (normalizerCentralizerResidual B t : Set G) := by
  have hE := factor_alignment_of_centralizer_witnesses d.T B Q
    (((d.T : Subgroup G) ⊓ M₁) ⊓ d.M.pCoreIn 2) R₁ z hBT hweak hzB hC hwitness
  exact hE.trans (hcomm.trans (centralizer_le
    (residual_le_second_factor B R₁ X t split hR hcoordinates)))

end CFSG.Quasithin.Chapter13.Section09.FusionAlignment
