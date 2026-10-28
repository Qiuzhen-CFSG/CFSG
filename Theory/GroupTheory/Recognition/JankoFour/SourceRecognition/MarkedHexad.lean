module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadQuotient
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedThompson

/-!
# Identifying the constructed hexad subgroup in a marked cocode normalizer

The faithful non-FF cocode action identifies the Thompson subgroup of the
full normalizer with its elementary kernel W. Every elementary subgroup
of order 2048 in that normalizer must therefore equal W. Apply this to
the image in G of the source hexad construction E, using the literal
point-plane overlap and the already proved order and elementary structure.

This identifies the actual constructed E, not just an isomorphic elementary
group. The original surjection, cocode equivariance and hexad-preimage
equality remain explicit; the Mathieu application supplies them.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6)–(4.8), pp.598–599, DOI 10.1007/BF01232280.
The marked argument does not construct the cocode marking for an arbitrary
type-J4 group.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry
variable {G : Type*} [Group G] [Finite G]
variable (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ n v, F (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (F (Additive.ofMul v)))

include hf hk hF in
/-- The actual cocode kernel is the unique elementary subgroup of its order
inside its full normalizer. -/
theorem marked_cocode_elementary_eq (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (W : Set G)) (hAc : Nat.card A = 2048) : A = W := by
  let N := normalizer (W : Set G)
  have hWc : Nat.card W = 2048 := by
    change Nat.card (Additive W) = _
    rw [Nat.card_congr F.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hJ := marked_cocode_thompson W f hf hk F hF N W.le_normalizer le_rfl
  obtain ⟨C,hC⟩ := elementaryAbelianMaxSubgroups_nonempty N
  have hCW : C = W := eq_of_le_of_card_ge ((le_sSup hC).trans hJ.le)
    (hC.2.2 W W.le_normalizer inferInstance)
  have hAmax : A ∈ elementaryAbelianMaxSubgroups N := by
    refine ⟨hAN,inferInstance,?_⟩
    intro B hBN hB
    have hc := hC.2.2 B hBN hB
    rwa [hCW,hWc,←hAc] at hc
  exact eq_of_le_of_card_ge ((le_sSup hAmax).trans hJ.le) (by rw [hAc,hWc])

include hf hk hF in
/-- At a marked Mathieu overlap, the source hexad construction recovers the
original cocode subgroup in the ambient group. -/
theorem marked_hexadElementary_eq {z : G} (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (CubicLift.subgroup e))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hpre : (normalizer (W : Set G)).subgroupOf (centralizer z) = originalPlaneHexad e B) :
    (originalHexadElementary h e X B).map (centralizer z).subtype = W := by
  let A := (originalHexadElementary h e X B).map (centralizer z).subtype
  let := (originalHexadElementary_data h e X hB).2.2.1
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAN : A ≤ normalizer (W : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := originalHexadElementary_le h e X B hx
    rw [←hpre] at hh
    exact hh
  apply marked_cocode_elementary_eq W f hf hk F hF A hAN
  rw [card_map_of_injective (centralizer z).subtype_injective,
    (originalHexadElementary_data h e X hB).2.2.2.1]

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
