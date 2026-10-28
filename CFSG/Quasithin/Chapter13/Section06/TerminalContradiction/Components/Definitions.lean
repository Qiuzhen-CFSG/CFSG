module

public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.SolvableResidual
public import Theory.PGroupCore
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.Mathieu.M23.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!+# The actual exceptional alternatives in 13.6.27

Here H denotes G₁ = C_G(z), and T denotes the ambient Sylow subgroup
restricted to H. Thus the source equality G₁ = KT is written K ⊔ T = ⊤
inside H. Components, cores, residuals and quotient images are all intrinsic
to these actual groups. No family tag stands for a group identification.

For the A₂ diagram, the two nodes are the conjugacy classes of point and
line parabolics of PSL₃(4). Nontrivial diagram action means that an element
of T exchanges these two classes by its actual conjugation on K, pulled
back through K → K/O₂(K) ≃ PSL₃(4). Both exchanges are recorded, together
with normalization of K. These are the literal matrix flag stabilizers.

`Conclusion` specifies the source alternatives and the structural output
used when the next paragraph resets K := H∞. It is a target proposition;
this definitions module does not assert that it holds.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 13.6.27
and its terminal application, printed pp.934–935 (PDF pp.951–952).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components

open Subgroup Theory.GroupTheory

/-- The actual field of four elements. -/
abbrev F4 := GaloisField 2 2

/-- The projective special linear group on the three-dimensional four-field space. -/
abbrev L3Four := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4

/-- The projective general linear group on the same space. -/
abbrev PGL3Four := Matrix.ProjGenLinGroup (Fin 3) F4

variable {H : Type*} [Group H]

/-- The actual component image in H/O₂(H). -/
def componentImage (K : Subgroup H) : Subgroup (H ⧸ pCore 2 H) :=
  K.map (QuotientGroup.mk' (pCore 2 H))

/-- Pull a concrete projective parabolic back to K and retain its embedding in H. -/
def liftedParabolic (K : Subgroup H) (e : (K ⧸ pCore 2 K) ≃* L3Four)
    (P : Subgroup L3Four) : Subgroup H :=
  (P.comap (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map K.subtype

/-- Nontrivial action on the actual A₂ diagram, expressed by exchange of its
two parabolic conjugacy classes. The inner conjugators lie in K itself. -/
def NontrivialDynkinAction (T K : Subgroup H)
    (e : (K ⧸ pCore 2 K) ≃* L3Four) : Prop :=
  T ≤ normalizer (K : Set H) ∧
    ∃ t ∈ T, ∃ k₀ k₁ : K,
      (liftedParabolic K e (Matrix.PSL3.LinearThree.pointParabolic F4)).map
          (MulAut.conj t).toMonoidHom =
        (liftedParabolic K e (Matrix.PSL3.LinearThree.lineParabolic F4)).map
          (MulAut.conj (k₀ : H)).toMonoidHom ∧
      (liftedParabolic K e (Matrix.PSL3.LinearThree.lineParabolic F4)).map
          (MulAut.conj t).toMonoidHom =
        (liftedParabolic K e (Matrix.PSL3.LinearThree.pointParabolic F4)).map
          (MulAut.conj (k₁ : H)).toMonoidHom

/-- The component alternatives before the final extension argument. The
linear branch includes the actual nontrivial diagram action. -/
def Candidate (T K : Subgroup H) : Prop :=
  Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
      ∃ e : (K ⧸ pCore 2 K) ≃* L3Four, NontrivialDynkinAction T K e

/-- The two alternatives of 13.6.27, with actual multiplicative equivalences
and O^{3′}, rather than a three-core or a three-residual. -/
def Alternative (T K : Subgroup H) : Prop :=
  (K ⊔ T = ⊤ ∧
    (Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23))) ∨
  (∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
    NontrivialDynkinAction T K e ∧
      primeToResidual 3 H ⊔ T = ⊤ ∧
      (K = primeToResidual 3 H ∨
        Nonempty (primeToResidual 3 (H ⧸ pCore 2 H) ≃* PGL3Four)))

/-- The exact source alternatives, supplemented by the structural facts
needed by the following paragraph. This is not an assumed certificate. -/
def Conclusion (T : Subgroup H) : Prop :=
  ∃ K : Subgroup H, K.IsCComponent ∧ Alternative T K ∧
    (∀ D : Subgroup H, D.IsCComponent → D = K) ∧
    generalizedFitting (H ⧸ pCore 2 H) = componentImage K ∧
    solvableResidual H = K

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
