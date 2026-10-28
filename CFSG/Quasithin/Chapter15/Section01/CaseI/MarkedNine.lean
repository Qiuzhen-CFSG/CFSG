module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedTransport
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import CFSG.Quasithin.ChapterB.Section02.Thompson.CyclicImage
public import Theory.SpecificGroups.OrthogonalFourBinary.MarkedNine

/-!
# The marked subgroup in the elementary-nine source row

The actual chosen action is embedded in the four-dimensional binary
orthogonal group by `SourceCases.Nine`. A cyclic Sylow group of order four
has a unique involution; every Thompson image lies in that involution group.
The finite orthogonal calculation selects a nonzero fixed vector whose
stabilizer has order six and generates the image together with the Sylow.
Pulling it back constructs the literal subgroup Z₁ of the original V and
proves the initial Sylow intersection in its ambient centralizer.

Source: Aschbacher--Smith 15.1.16(b) and 15.1.17, printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Retain the marked image stabilizer for the subsequent centralizer quotient. -/
theorem chosen_nine_marked_image
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ∃ (v : Additive V) (K : Subgroup (internalActionImage M V hn)),
      v ≠ 0 ∧
      v ∈ fixedSpace (imageRepresentation M V hn)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hn).rangeRestrict) ∧
      (∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v) ∧
      K ⊔ (((T : Subgroup G).subgroupOf M).map
        (actionHom M V hn).rangeRestrict) = ⊤ ∧
      Nat.card K = 6 ∧
      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K := by
  let f := (actionHom M V hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let ρ := imageRepresentation M V hn
  obtain ⟨l, _, _, hD, _, _, hS, x, φ, hφ, hcoord⟩ := h9
  let hcyc : IsCyclic S := hS.1
  obtain ⟨A, hAS, hA, hJA⟩ := ChapterB.exists_cyclic_two_marker
    (T : Subgroup G) M hTM f S le_rfl hS.2 1
  obtain ⟨z, hz, hfix, hgen, hKcard, hSyl⟩ :=
    @OrthogonalFourBinary.MarkedNine.exists_marked_vector _ _ _ φ hφ hD S hcyc hS.2
  let v : Additive V := x.symm z
  let K := OrthogonalFourBinary.MarkedNine.pointStabilizer φ z
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg x h
    simp only [v, x.apply_symm_apply, map_zero] at hh
    exact hz hh
  have hK : ∀ d, d ∈ K ↔ ρ d v = v := by
    intro d
    change (φ d).val z = z ↔ ρ d v = v
    constructor
    · intro hd
      apply x.injective
      calc
        x (ρ d v) = (φ d).val (x v) := hcoord d v
        _ = (φ d).val z := by rw [show x v = z from x.apply_symm_apply z]
        _ = z := hd
        _ = x v := (x.apply_symm_apply z).symm
    · intro hd
      have hh := congrArg x hd
      rw [hcoord d v] at hh
      simpa only [v, x.apply_symm_apply] using hh
  have hvfixed : v ∈ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f) := by
    intro d
    apply (hK d).mp
    apply hfix d (hAS (hJA d.property))
    have hp := pow_card_eq_one' (x := (⟨(d : internalActionImage M V hn), hJA d.property⟩ : A))
    rw [hA] at hp
    exact congrArg Subtype.val hp
  exact ⟨v, K, hv, hvfixed, hK, hgen, hKcard, hSyl⟩

/-- The elementary-nine row supplies the literal marked subgroup and the initial
Sylow statement of original 15.1.16(b)--17. -/
theorem chosen_nine_marked_Z1
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ∃ Z1 : Subgroup G, Z1 ≤ thompsonFixed T V ∧ Z1 ≠ ⊥ ∧
      M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G) ∧
      ∃ P : Sylow 2 ↥(M ⊓ centralizer (Z1 : Set G)),
        (P : Subgroup ↥(M ⊓ centralizer (Z1 : Set G))).map
          (M ⊓ centralizer (Z1 : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer (Z1 : Set G) := by
  obtain ⟨v, K, hv, hfixed, hK, hgen, _, hSyl⟩ := chosen_nine_marked_image T hTM hn h9
  exact ⟨zpowers (v.toMul : G),
    marked_zpowers_and_sylow_of_image_stabilizer T hTM hn v hv hfixed K hK hgen hSyl⟩

end CFSG.Quasithin.Chapter15.Section01
