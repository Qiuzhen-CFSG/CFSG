module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.SourceCalculations
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The extended centralizer in the original ambient group

The subtype equivalence identifies the relative centralizer in I with
I intersect C_G(w). It transports the odd core and the actual extraspecial
Sylow three-subgroup, retaining the original involution and cardinalities.
Source: Aschbacher–Smith15.3.38, printed p.1137.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer
variable {G : Type*} [Group G] [Finite G]

/-- Relative centralizers retain their literal common ambient subgroup. -/
def ambientCentralizerEquiv (I : Subgroup G) (w : I) :
    centralizerIn w ≃* (I ⊓ centralizer ({(w : G)} : Set G) : Subgroup G) where
  toFun x := ⟨x, ⟨x.val.property, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩⟩
  invFun x := ⟨⟨x, x.property.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The local calculation supplies the exact odd core and Sylow subgroup
inside I intersect C_G(w), as required by the Chapter15 source consumer. -/
theorem NormalizerGeometry.ambient_oddCore_and_sylow
    (I : Subgroup G) {L : Subgroup I} [L.Normal]
    (d : Overgroup L) (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    Nonempty (pPrimeCore 2 (I ⊓ centralizer ({(n.graphFieldI : G)} : Set G) : Subgroup G) ≃*
      ElementaryNine) ∧
      ∃ P : Sylow 3 (I ⊓ centralizer ({(n.graphFieldI : G)} : Set G) : Subgroup G),
        IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 := by
  obtain ⟨⟨eO⟩, P, hP, hc, he⟩ := n.oddCore_and_sylow d e
  let j := ambientCentralizerEquiv I n.graphFieldI
  have hmap := pPrimeCore_map_iso 2 j
  let jO : pPrimeCore 2 (centralizerIn n.graphFieldI) ≃*
      pPrimeCore 2 (I ⊓ centralizer ({(n.graphFieldI : G)} : Set G) : Subgroup G) :=
    (j.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  let Q : Sylow 3 (I ⊓ centralizer ({(n.graphFieldI : G)} : Set G) : Subgroup G) :=
    P.mapSurjective (f := j.toMonoidHom) j.surjective
  let k : P ≃* Q := j.subgroupMap (P : Subgroup (centralizerIn n.graphFieldI))
  exact ⟨⟨jO.symm.trans eO⟩, Q, IsExtraspecial.of_mulEquiv k hP,
    (Nat.card_congr k.toEquiv).symm.trans hc,
    (Monoid.exponent_eq_of_mulEquiv k).symm.trans he⟩

end Matrix.PSL3Four.ExtendedCentralizer
