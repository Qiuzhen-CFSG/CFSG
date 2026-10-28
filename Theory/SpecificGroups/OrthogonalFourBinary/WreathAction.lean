module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.DefinitePlanes
public import Theory.GroupAction.ComplementaryFourWreathAction
public import Theory.Representation.BinaryGroupAction
public import Mathlib.GroupTheory.Index

/-!
# The full binary plus-four isometry group as a natural wreath product

The two original definite planes are complementary four-groups, and the
checked isometry coordinates permute them. Faithfulness and the original
order72 calculation identify the whole isometry action with SL₂(2)≀C₂,
including coordinates for every original vector and actor.

Source: the O₄⁺(2) / S₃≀C₂ action in Aschbacher–Smith 13.2.8(3), p.880.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace OrthogonalFourBinary
open TerminalLines SylowGeometry

private theorem definitePlane_compl : IsCompl (definitePlane false) (definitePlane true) := by
  constructor
  · rw [disjoint_iff]
    apply bot_unique
    intro v hv
    change v = 1
    apply Multiplicative.toAdd.injective
    exact Prod.ext hv.2 hv.1
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    let a : Multiplicative Space := Multiplicative.ofAdd (v.toAdd.1,0)
    let b : Multiplicative Space := Multiplicative.ofAdd (0,v.toAdd.2)
    have ha : a ∈ definitePlane false := rfl
    have hb : b ∈ definitePlane true := rfl
    have he : a*b=v := by apply Multiplicative.toAdd.injective; simp [a,b]
    rw [← he]
    exact (definitePlane false ⊔ definitePlane true).mul_mem ((le_sup_left : definitePlane false ≤ definitePlane false ⊔ definitePlane true) ha)
      ((le_sup_right : definitePlane true ≤ definitePlane false ⊔ definitePlane true) hb)

private theorem finite_plane_transport : ∀ i : Code, ∀ b : Bool, ∀ v : Space,
    (if b then v.1=0 else v.2=0) →
      (if xor b i.2.2 then (eval i v).1=0 else (eval i v).2=0) := by
  decide +kernel

/-- Actual isometries permute the original two definite planes. -/
theorem vectorAction_permute_definite (g : TerminalLines.IsometryGroup) :
    ((definitePlane false).map (vectorAction g).toMonoidHom = definitePlane false ∧
     (definitePlane true).map (vectorAction g).toMonoidHom = definitePlane true) ∨
    ((definitePlane false).map (vectorAction g).toMonoidHom = definitePlane true ∧
     (definitePlane true).map (vectorAction g).toMonoidHom = definitePlane false) := by
  obtain ⟨i,rfl⟩ := codeMap_bijective.surjective g
  have he (b : Bool) : (definitePlane b).map (vectorAction (codeMap i)).toMonoidHom =
      definitePlane (xor b i.2.2) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨v,hv,rfl⟩
      change (if xor b i.2.2 then (candidate i v.toAdd).1=0 else (candidate i v.toAdd).2=0)
      rw [candidate_eval]
      exact finite_plane_transport i b v.toAdd hv
    · have hc : Nat.card ((definitePlane b).map (vectorAction (codeMap i)).toMonoidHom) =
          Nat.card (definitePlane b) := Subgroup.card_map_of_injective (vectorAction (codeMap i)).injective
      rw [hc,definitePlane_card,definitePlane_card]
  cases hb : i.2.2
  · exact Or.inl ⟨by simpa [hb] using he false,by simpa [hb] using he true⟩
  · exact Or.inr ⟨by simpa [hb] using he false,by simpa [hb] using he true⟩

/-- The exact isometry actor and its whole natural module are the binary wreath action. -/
theorem isometry_equiv_natural_wreath :
    ∃ eG : TerminalLines.IsometryGroup ≃* RegularWreathProduct
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)),
      ∃ eV : Multiplicative Space ≃*
          (Multiplicative (ZMod 2) → Multiplicative (Fin 2 → ZMod 2)),
        ∀ g v i, eV (vectorAction g v) i = Multiplicative.ofAdd
          (Matrix.mulVec ((eG g).left i).1
            (Multiplicative.toAdd (eV v ((eG g).right⁻¹ * i)))) := by
  let : IsElementaryAbelian 2 (Multiplicative Space) := Representation.BinaryGroupAction.elementary
  let := MulDistribMulAction.compHom (Multiplicative Space) vectorAction
  let _ : FaithfulSMul TerminalLines.IsometryGroup (Multiplicative Space) := by
    rw [faithfulSMul_iff]
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hg (Multiplicative.ofAdd v)
  have hf : fixingSubgroup TerminalLines.IsometryGroup (Set.univ : Set (Multiplicative Space)) = ⊥ := by
    apply bot_unique
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative Space)
    intro v
    exact (mem_fixingSubgroup_iff _).mp hg v (Set.mem_univ _)
  exact ComplementaryFourWreathAction.equiv_natural_wreath_of_complementary_four
    (definitePlane false) (definitePlane true) definitePlane_compl
    (definitePlane_card false) (definitePlane_card true) hf isometryGroup_card
    vectorAction_permute_definite

end OrthogonalFourBinary
