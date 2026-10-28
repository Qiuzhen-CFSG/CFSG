module

public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction

/-!
# The enlargement and the marked eight-point conclusion

These are output specifications for Aschbacher–Smith, 16.3.9–11, combined
manuscript of 1 March 2004, printed pp.1180–1181. They assert no classification
result. The enlargement is the actual layer closure in C_G(t).

The binary graph action is given by inverse transpose, up to an inner
factor, on SL₄(2). This binary special linear group is also PSL₄(2).
The sporadic alternatives use the actual quotients by O₂(K), and retain
nontriviality of that two-core. The final marking uses one equivalence of
K⟨z⟩ with S₈, identifying K, L and z simultaneously; the A₆ subgroup fixes
points 0 and 1 individually.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.EnlargementSieve
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The source subgroup K = ⟨L^{E(C_G(t))}⟩. -/
abbrev enlargement (t : G) (L : Subgroup G) : Subgroup G :=
  ComponentTransfer.layerClosure (involutionCentralizer t) L

/-- The order-four lift used in both exceptional-cover contradictions on
p.1181. Its incompatibility with the contrary setup must be proved from
the dihedral/semidihedral geometry; it is not an assumed source theorem. -/
def NormalizerSquareWitness (L : Subgroup G) (t : G) : Prop :=
  ∃ u : G, orderOf u = 4 ∧ u ∈ normalizer L ∧ u ^ 2 = t

/-- The actual graph-action alternative in 16.3.9(1), on the binary matrix
model. The normalization condition makes the displayed action well-defined. -/
def BinaryFourGraphAlternative (K L : Subgroup G) (z : G) : Prop :=
  ∃ (hz : z ∈ normalizer K)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (a : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)),
    (∀ x : K, e (K.normalizerMonoidHom ⟨z, hz⟩ x) =
      a * (Matrix.SpecialLinearGroup.transpose (e x))⁻¹ * a⁻¹) ∧
    Nonempty (L ≃* alternatingGroup (Fin 6))

/-- Cases (2)–(4) of 16.3.9, including their nontrivial two-core clause.
These are equivalences of the specified groups, not unattached family labels. -/
def SporadicCoverAlternative (K L : Subgroup G) : Prop :=
  pCore 2 K ≠ ⊥ ∧
    ((Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.m12.Carrier) ∧
        Nonempty (L ≃* alternatingGroup (Fin 5))) ∨
     (Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.j2.Carrier) ∧
        (Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
         Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))) ∨
     (Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.hs.Carrier) ∧
        (Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
         Nonempty (L ≃* alternatingGroup (Fin 8)))))

/-- All four alternatives of 16.3.9. This is an output to prove. -/
def FourAlternatives (K L : Subgroup G) (z : G) : Prop :=
  BinaryFourGraphAlternative K L z ∨ SporadicCoverAlternative K L

/-- The standard A₆ inside S₈ fixes the two points moved by z. -/
def standardSix : Subgroup (Equiv.Perm (Fin 8)) :=
  alternatingGroup (Fin 8) ⊓
    (MulAction.stabilizer (Equiv.Perm (Fin 8)) (0 : Fin 8) ⊓
     MulAction.stabilizer (Equiv.Perm (Fin 8)) (1 : Fin 8))

/-- A single compatible eight-point marking for the Thompson calculation
following 16.3.11. In particular the images of K and L are not independent
isomorphism tags. This structure is a conclusion, never a standing hypothesis
of 16.3.9–11. -/
structure MarkedEightSix (K L : Subgroup G) (z : G) where
  smaller_le : L ≤ K
  equiv : (K ⊔ zpowers z : Subgroup G) ≃* Equiv.Perm (Fin 8)
  involution_image : equiv ⟨z, (le_sup_right : zpowers z ≤ K ⊔ zpowers z)
    (mem_zpowers z)⟩ = Equiv.swap 0 1
  larger_image : (K.subgroupOf (K ⊔ zpowers z)).map equiv.toMonoidHom =
    alternatingGroup (Fin 8)
  smaller_image : (L.subgroupOf (K ⊔ zpowers z)).map equiv.toMonoidHom = standardSix

end CFSG.Quasithin.Chapter16.EnlargementSieve
