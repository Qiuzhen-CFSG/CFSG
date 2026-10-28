module
public import CFSG.Quasithin.Chapter3.Section02.Setup
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.DiagramEquivalence

/-!
# The Hermitian tensor row of the original Fundamental Setup

The marking identifies K/O₂(K) and the conjugation action on the actual
V = ⟨V◦ᵀ⟩ with the faithful nine-dimensional Hermitian module. Conjugation by
an original t in T provides the binary intertwiner, so the computed normalizer
fixes the Dynkin diagram. Comparing arbitrary quotient markings retains the
same geometric diagram classes used in the exceptional residual argument.

This proves the diagram clause of 3.2.9(4) for this genuine module row. It does
not assert that every FSU with PSL₃(4) quotient has that row: seed invariance,
the natural/FF exclusions and tensor recognition remain with
qt-d-1222-linear-residual-maximal-nonfaithful. In particular the marking is
an actual action isomorphism, not a consequence of a dimension or family tag.

Source: Aschbacher–Smith 3.2.5, 3.2.8 and 3.2.9(4), printed pp.580–583;
5.1.14, p.638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Representation.HermitianTensorThree
open Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K : Subgroup G} {𝒦 : GroupClass.{u}}
  (D : FundamentalSetup 𝒦 T K)

/-- Actual quotient and additive coordinates for the tensor row of 3.2.9(4).
The action equation is literal ambient conjugation on the full T-orbit module. -/
structure HermitianFourMarking where
  quotient : (K ⧸ pCore 2 K) ≃* PSL(3,E 1)
  coordinates : Additive D.moduleSubgroup ≃+ Space 1
  equivariant : ∀ (k : K) (w : D.moduleSubgroup),
    coordinates (Additive.ofMul (D.moduleSubgroup.normalizerMonoidHom
      ⟨k,((le_componentOrbit K (T : Subgroup G)).trans D.orbit_normalizes_module)
        k.property⟩ w)) =
      projectiveAction (quotient (QuotientGroup.mk' (pCore 2 K) k))
        (coordinates (Additive.ofMul w))

/-- The original Sylow actor preserves the diagram in every quotient marking
once the actual FSU module is identified with the Hermitian tensor. -/
theorem hermitianFour_diagram_trivial
    (m : D.HermitianFourMarking)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : G) = t * k * t⁻¹)
    (hb : ∀ k, e (QuotientGroup.mk' (pCore 2 K) (a k)) =
      b (e (QuotientGroup.mk' (pCore 2 K) k))) :
    b ∈ diagramTrivial F := by
  let j := e.symm.trans m.quotient
  let β := MulAut.congr j b
  let q : K →* PSL(3,E 1) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hβ (k : K) : q (a k) = β (q k) := by
    change m.quotient (QuotientGroup.mk' (pCore 2 K) (a k)) =
      m.quotient (e.symm (b (e (m.quotient.symm
        (m.quotient (QuotientGroup.mk' (pCore 2 K) k))))))
    rw [m.quotient.symm_apply_apply,← hb,e.symm_apply_apply]
  apply diagramTrivial_of_equiv_four hF (card_E 1) j b
  exact diagram_trivial_of_conjugation K D.moduleSubgroup
    ((le_componentOrbit K (T : Subgroup G)).trans D.orbit_normalizes_module)
    q (m.quotient.surjective.comp (QuotientGroup.mk'_surjective _))
    m.coordinates m.equivariant t (D.sylow_normalizes_module ht) a ha β hβ

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup

