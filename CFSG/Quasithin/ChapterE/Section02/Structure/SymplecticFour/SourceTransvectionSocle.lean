module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SocleAssembly
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceTransvectionClosure
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceQuadraticOddCore

/-!
# Simple socle of the original transvection-containing pair

The original geometry supplies irreducibility of the F-transvection closure,
vanishing of its Fitting subgroup and exclusion of every compatible quadratic
form invariant under the pair. A nonsimple layer would give two commuting
perfect factors and hence an actual quadratic form invariant under its
symplectic normalizer, contradicting that exclusion. The resulting actual
simple generalized Fitting subgroup acts irreducibly on the original F-space.

This discharges the simple-socle reduction of Aschbacher--Smith G.4.9 in the
original E.2.7 geometry. The c2 witness and coefficient-field model inspection
remain separate source arguments.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate TransvectionRecognition
open ChapterB InvolutionTypes Theory.GroupTheory
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original pair's literal transvection closure has simple irreducible
F*, with no additional component, Fitting or quadratic-form premise. -/
theorem source_transvection_closure_simple_socle {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    IsComponent C (generalizedFitting C) ∧ IsSimpleGroup (generalizedFitting C) ∧
      Representation.IsIrreducible
        (((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp C.subtype).comp
          (generalizedFitting C).subtype) := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  have hi := source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr hex
  have hf := (source_geometry_fitting_cores_eq_bot hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr).2.2
  exact transvectionClosure_simple_generalizedFitting H hi hex hf
    (fun Q hQ => source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr Q hQ)

/-- The actual original pair itself has the same simple irreducible socle
as its F-transvection closure. -/
theorem source_pair_simple_socle {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    generalizedFitting H=(generalizedFitting (transvectionClosure H)).map
      (transvectionClosure H).subtype ∧ IsSimpleGroup (generalizedFitting H) ∧
      Representation.IsIrreducible
        ((pairAction (V.comap (L.subtype.comp e.toMonoidHom))).comp
          (generalizedFitting H).subtype) := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  have hi := source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr hex
  have hf := source_geometry_fitting_cores_eq_bot hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr
  exact ambient_simple_generalizedFitting_of_transvections H hi hex hf.2.1 hf.2.2
    (fun Q hQ => source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr Q hQ)

/-- The same simple socle is retained as an actual subgroup of the
original Sp4(F), normalized by the original pair. -/
theorem source_transvection_simple_socle_image {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (hex:∃ h∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),IsB1 h) :
    let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    let C := transvectionClosure H
    let N := (generalizedFitting C).map (H.subtype.comp C.subtype)
    IsSimpleGroup N ∧
      Representation.IsIrreducible ((Representation.symplecticNatural 2).comp N.subtype) ∧
      H≤normalizer (N:Set (Sp F)) := by
  dsimp only
  let H := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
  have hi := source_transvection_closure_irreducible hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr hex
  have hf := (source_geometry_fitting_cores_eq_bot hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr).2.2
  exact transvectionClosure_simple_socle_image H hi hex hf
    (fun Q hQ => source_geometry_quadratic_exclusion hF hn T hP hJ L e hmark hgen
      V hVT hVM hVN hr Q hQ)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
