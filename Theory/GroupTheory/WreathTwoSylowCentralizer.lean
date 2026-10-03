module

public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.SpecificGroups.DihedralEightCentralizer

/-!
# Sylow centralizers in the concrete `SL₂(2)` wreath product

Let `P` be a Sylow two-subgroup of `SL₂(2) ≀ᵣ C₂`, and let `V ≤ P` have
at least four elements. Then `P ⊓ C(V)` is contained in `V` and has at most
four elements. No commutativity or normality hypothesis on `V` is needed.

The concrete Sylow model identifies `P` with `DihedralGroup 4`. Restricting
`V` to `P` and mapping it through this equivalence preserves its cardinality,
so the intrinsic dihedral centralizer theorem applies. Commutation transports
pointwise: every element of the actual ambient intersection maps into the
model centralizer. Its containment in the image of `V` gives the first
conclusion; the injectivity of this map gives the cardinal bound.

This independent finite-group calculation supports Stellmacher (9.1),
relation (9), journal p.47. Transport through the faithful quotient and the
geometric lower bound on the image of `V` belong to the caller. This module
uses only the concrete group and imports no campaign hypotheses.
-/

private theorem transport {G : Type*} [Group G] (P V : Subgroup G)
    (equiv : P ≃* DihedralGroup 4) (hVP : V ≤ P) (hV : 4 ≤ Nat.card V) :
    P ⊓ Subgroup.centralizer (V : Set G) ≤ V ∧
      Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) ≤ 4 := by
  let W := (V.subgroupOf P).map equiv.toMonoidHom
  have hcardW : Nat.card W = Nat.card V :=
    (Nat.card_congr (equiv.subgroupMap (V.subgroupOf P)).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv)
  obtain ⟨hcontain, hbound⟩ := DihedralGroup.centralizer_le_of_card_ge_four W (hcardW ▸ hV)
  let central := P ⊓ Subgroup.centralizer (V : Set G)
  have hmap (element : central) :
      equiv ⟨element.val, element.property.1⟩ ∈
        Subgroup.centralizer (W : Set (DihedralGroup 4)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨preimage, hpreimage, rfl⟩ := hother
    have hcomm := Subgroup.mem_centralizer_iff.mp element.property.2
      preimage.val hpreimage
    change equiv preimage * equiv ⟨element.val, element.property.1⟩ =
      equiv ⟨element.val, element.property.1⟩ * equiv preimage
    rw [← map_mul, ← map_mul]
    apply congrArg equiv
    exact Subtype.ext hcomm
  constructor
  · intro element helement
    obtain ⟨preimage, hpreimage, heq⟩ := hcontain (hmap ⟨element, helement⟩)
    have heq' := equiv.injective heq
    have hval : preimage.val = element := congrArg Subtype.val heq'
    change preimage.val ∈ V at hpreimage
    exact hval ▸ hpreimage
  · let embedding : central → Subgroup.centralizer (W : Set (DihedralGroup 4)) :=
      fun element => ⟨equiv ⟨element.val, element.property.1⟩, hmap element⟩
    apply le_trans (Nat.card_le_card_of_injective embedding ?_) hbound
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun element : P => element.val)
      (equiv.injective (congrArg Subtype.val heq))

/-- A subgroup of a concrete wreath Sylow two-subgroup with at least four
elements contains its Sylow centralizer, whose order is at most four. -/
public theorem wreath_two_sylow_centralizer_le_of_card_ge_four
    (P : Sylow 2 (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))))
    (V : Subgroup (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))))
    (hVP : V ≤ (P : Subgroup _)) (hV : 4 ≤ Nat.card V) :
    ((P : Subgroup _) ⊓ Subgroup.centralizer (V : Set _)) ≤ V ∧
      Nat.card ↥((P : Subgroup _) ⊓ Subgroup.centralizer
        (V : Set (RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (Multiplicative (ZMod 2))))) ≤ 4 := by
  obtain ⟨equiv⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  exact transport (P : Subgroup _) V equiv hVP hV
