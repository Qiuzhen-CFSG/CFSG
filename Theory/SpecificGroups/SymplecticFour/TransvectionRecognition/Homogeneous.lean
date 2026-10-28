module
public import Theory.Representation.RankOneSymplectic.Homogeneous
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure

/-!
# Homogeneous normal restriction in the actual transvection closure

The literal F-transvections generate their normal closure. Once this closure
acts irreducibly, the generic rank-one symplectic theorem makes restriction to
every normal subgroup homogeneous. The moving-pair consumer discharges the
irreducibility premise with the original geometry, retaining the exact group,
normal subgroup and coefficient field.

Source: the standing reduction after Aschbacher--Smith G.4.6, printed p.340,
as used in G.4.9 and the E.2.7 transvection branch, printed pp.219--221.
-/

public noncomputable section
open Subgroup Module
open scoped MonoidAlgebra
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes TwoConjugate
variable {F : Type*} [Field F]

theorem transvectionClosure_normal_restriction_isotypic
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible
      (((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype))
    (N : Subgroup (transvectionClosure H)) [N.Normal]
    (A : Subrepresentation
      ((((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype).comp N.subtype))
    [hA : A.toRepresentation.IsIrreducible] :
    IsIsotypicOfType F[N]
      (Representation.asModule ((((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype).comp N.subtype)) A.asSubmodule := by
  let ρ : Representation F (transvectionClosure H) (Vector F) :=
    ((Representation.symplecticNatural 2).comp H.subtype).comp (transvectionClosure H).subtype
  let : ρ.IsIrreducible := hi
  have hs : ∀ d : transvectionClosure H, IsB1 ((d:H):Sp F) → d*d=1 := by
    intro d hd
    apply Subtype.ext
    apply Subtype.ext
    have h := pow_orderOf_eq_one ((d:H):Sp F)
    rwa [hd.1,pow_two] at h
  have hr : ∀ d : transvectionClosure H, IsB1 ((d:H):Sp F) →
      finrank F (LinearMap.range (ρ d-LinearMap.id))=1 := by
    intro d hd
    change finrank F (movedSpace ((d:H):Sp F))=1
    exact hd.2
  exact Representation.RankOneSymplectic.Homogeneous.normal_restriction_isotypic
    ρ N (form F) TwoLocalCover.form_alternating TwoLocalCover.form_nondegenerate
    (fun d => preserves_form (F:=F) ((d:H):Sp F)) (by simp [Vector])
    {d : transvectionClosure H | IsB1 ((d:H):Sp F)} (transvectionClosure_generated H) hs hr A

theorem moving_pair_transvectionClosure_normal_restriction_isotypic [CharP F 2] [Finite F]
    (hq : 2<Nat.card F) (a : EvenBorelTorus.ActorReduction.stabilizer (F:=F))
    (ha : ¬DiagramAutomorphisms.PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hV : V.map a.val.toMonoidHom=V)
    (hc : V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype)
    (hr : 2<Nat.card V) (hex : ∃ h∈oppositePair V, IsB1 h)
    (N : Subgroup (transvectionClosure (oppositePair V))) [N.Normal]
    (A : Subrepresentation (((pairAction V).comp
      (transvectionClosure (oppositePair V)).subtype).comp N.subtype))
    [hA : A.toRepresentation.IsIrreducible] :
    IsIsotypicOfType F[N]
      (Representation.asModule
        (((pairAction V).comp (transvectionClosure (oppositePair V)).subtype).comp N.subtype))
      A.asSubmodule :=
  transvectionClosure_normal_restriction_isotypic (oppositePair V)
    (moving_pair_transvectionClosure_irreducible hq a ha V hV hc hr hex) N A (hA := hA)

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
