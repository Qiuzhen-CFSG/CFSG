module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Pairing
public import Theory.Representation.CyclicDefect.ProjectivePairing

/-!
# Tensor positivity after projective lifting

The actual edge module makes the linear-Hom representation projective. Its
ordinary comparison, once constructed, turns the literal class sum with
reciprocal centralizer weights into the dimension supplied by character
averaging. The root-order bound uses exactly the source group order.

The remaining model premise is the projective lifting and comparison step of
Feit IV.3.3, not an existence premise for the already supplied stem or edges.
Unconditional reciprocity requires discharging it.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation
variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The precise representation used by reciprocity is projective, from the
projectivity retained in the actual edge data. -/
public theorem projective_tensorIntertwining (s : RealStem G d)
    (P : ProjectiveEdges s) (i j k : Fin 10) :
    Module.Projective (MonoidAlgebra ElevenClosure G)
      (linHom (P k).rep ((s.rep i).tprod (s.rep j))).asModule := by
  let : Fintype G := Fintype.ofFinite G
  let : Module.Projective (MonoidAlgebra ElevenClosure G) (P k).rep.asModule :=
    (P k).projective
  exact CyclicDefect.ProjectivePairing.projective_linHom (P k).rep _

/-- Conditional assembly with the exact source coefficient. The remaining
premise is the ordinary lifting/comparison theorem, not the existence of the
stem or of its projective edges. -/
public theorem tensorPositive_of_ordinaryModels (s : RealStem G d)
    (P : ProjectiveEdges s) (horder : Nat.card G = 175560)
    (models : ∀ i j k : Fin 10, CyclicDefect.ProjectivePairing.OrdinaryModel
      (G := G) (V := (Fin (P k).degree → ElevenClosure) →ₗ[ElevenClosure]
        TensorProduct ElevenClosure (Fin (s.degree i) → ElevenClosure)
          (Fin (s.degree j) → ElevenClosure)) 11 s.roots
      (linHom (P k).rep ((s.rep i).tprod (s.rep j)))) : s.TensorPositive := by
  intro i j k
  rw [tensorCoefficient_eq_projectivePairing s P i j k]
  exact CyclicDefect.regularPairing_tensor_nat_of_ordinaryModel 11 s.roots
    (regular_order_dvd_root_order horder) (s.rep i) (s.rep j) (P k).rep (models i j k)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
