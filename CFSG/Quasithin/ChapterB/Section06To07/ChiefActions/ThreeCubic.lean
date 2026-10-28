module
public import Theory.SpecificGroups.SymmetricThree.CubicSelection
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The selected cubic on an actual symmetric-three chief action

A nontrivial elementary actor in S₃ has order two and acts nontrivially
on the canonical cubic A₃=O²(S₃). The resulting subgroup geometry transports
through the specified chief-action coordinates. The same construction works
for SL₂(2) through its three-point action. On the literal faithful chief
image every hypothesis comes from the supplied original offender image;
no assertion about the original action kernel being a two-group is needed.

Source: Aschbacher–Smith, 3.1.9(5) and 15.1.12(3–4), pp.577–578,1090.
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Representation Representation.BinaryOffender
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- The prescribed S₃ coordinates select a cubic for the same offender. -/
theorem three_action_cubic_selection
    (ρ : Representation (ZMod 2) G W) (S : Subgroup G) (A : Subgroup G)
    (hAS : A ≤ S) (hA : IsOffender ρ A) (e : G ≃* Equiv.Perm (Fin 3)) :
    ∃ L R : Subgroup G, Nat.card L = 3 ∧ R ≤ A ∧ R.relIndex A = 2 ∧
      A ≤ normalizer (R : Set G) ∧ L ≤ centralizer (R : Set G) ∧
      A ≤ normalizer (L : Set G) ∧ L = ⁅L,A⁆ ∧ L ⊔ S = ⊤ := by
  let : IsElementaryAbelian 2 A := hA.1.2
  exact Theory.SpecificGroups.SymmetricThree.CubicSelection.exists_selection_of_equiv
    e S A hA.1.1 hAS

/-- The same geometry for the actual special linear group over two elements. -/
theorem linear_two_action_cubic_selection
    (ρ : Representation (ZMod 2) G W) (S A : Subgroup G)
    (hAS : A ≤ S) (hA : IsOffender ρ A)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    ∃ L R : Subgroup G, Nat.card L = 3 ∧ R ≤ A ∧ R.relIndex A = 2 ∧
      A ≤ normalizer (R : Set G) ∧ L ≤ centralizer (R : Set G) ∧
      A ≤ normalizer (L : Set G) ∧ L = ⁅L,A⁆ ∧ L ⊔ S = ⊤ :=
  three_action_cubic_selection ρ S A hAS hA
    (e.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

/-- The seven image-geometry inputs for the original chief-action selection
are discharged on the literal action image, retaining the original actor. -/
theorem chief_three_image_geometry
    (ρ : Representation (ZMod 2) G W) (S : Subgroup G) (A : Subgroup G)
    (hAS : A ≤ S)
    (hA : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (e : actionImage ρ ≃* Equiv.Perm (Fin 3)) :
    ∃ R L : Subgroup (actionImage ρ),
      R ≤ S.map (actionHom ρ) ∧
      A.map (actionHom ρ) ≤ normalizer (R : Set (actionImage ρ)) ∧
      L ≤ normalizer (R : Set (actionImage ρ)) ∧
      A.map (actionHom ρ) ≤ normalizer (L : Set (actionImage ρ)) ∧
      R.relIndex (A.map (actionHom ρ)) = 2 ∧
      L = ⁅L,A.map (actionHom ρ)⁆ ∧ L ⊔ S.map (actionHom ρ) = ⊤ := by
  obtain ⟨L,R,hcard,hRA,hi,hAR,hLR,hAL,hcomm,hgen⟩ :=
    three_action_cubic_selection (imageRepresentation ρ) (S.map (actionHom ρ))
      (actionSubgroup ρ A) (map_mono hAS) hA e
  exact ⟨R,L,hRA.trans (map_mono hAS),hAR,
    hLR.trans (centralizer_le_normalizer _),hAL,hi,hcomm,hgen⟩

end CFSG.Quasithin.ChapterB
