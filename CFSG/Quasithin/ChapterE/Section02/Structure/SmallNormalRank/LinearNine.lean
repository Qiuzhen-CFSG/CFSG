module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SmallNormalRank
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# The normal PSL₂(9) row in the literal parabolic star quotient

The exceptional isomorphism PSL₂(9) ≃ A₆ is uniform in the field model.
Composing it with the binary symplectic comparison brings the normal
generating component under the checked Aut(A₆) two-rank bound. Hence the
whole star quotient has two-rank at most three, and every elementary image
has order at most eight. For an ordinary component the quotient map has
kernel its center, so the original marked central-quotient model supplies
the literal star model without an additional identification premise.

Source: Aschbacher--Smith 1.1.5, E.2.2 and 14.6.9,
printed pp.501--503,215--216,1027--1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

private theorem linear_nine_equiv_binary_derived
    {D : Type*} [Group D] (hm : ClassicalGroup.IsPSL D 2 9) :
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  exact ⟨(e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hcard)).trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩

/-- A normal generating PSL₂(9) star image bounds the entire star quotient. -/
theorem source_star_linear_nine_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 9) :
    primeRank 2 (H ⧸ ChapterB.minimalParabolicCore T hP) ≤ 3 := by
  exact source_star_small_binary_rank_le_three T hP hs K hK hgen
    (Or.inr (linear_nine_equiv_binary_derived hm))

/-- Every literal elementary image has order at most eight in this source row. -/
theorem source_star_linear_nine_elementary_card_le_eight
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 9)
    (V : Subgroup H) [IsElementaryAbelian 2 V] :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 8 := by
  exact source_star_small_binary_elementary_card_le_eight T hP hs K hK hgen
    (Or.inr (linear_nine_equiv_binary_derived hm)) V

/-- The marked ordinary-component central quotient from 14.6.9 supplies the
rank bound directly; its identification with the star image is constructed. -/
theorem source_ordinary_linear_nine_rank_le_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : IsComponent H K) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 9) :
    primeRank 2 (H ⧸ ChapterB.minimalParabolicCore T hP) ≤ 3 := by
  let : IsQuasisimple K := hK.2
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  have hi := source_component_simple_image T hP hs K hK.isCComponent hgen
  let : IsSimpleGroup (K.map q) := hi.1
  let : IsQuasisimple (K.map q) := hi.2.1.2
  let f : Covering K (K.map q) :=
    { toMonoidHom := q.subgroupMap K, surjective := q.subgroupMap_surjective K }
  let e : (K ⧸ center K) ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq f.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
  exact source_star_linear_nine_rank_le_three T hP hs K hK.isCComponent hgen
    (hm.of_mulEquiv e.symm)

/-- The actual elementary quotient-image bound for the ordinary PSL₂(9) row. -/
theorem source_ordinary_linear_nine_elementary_card_le_eight
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : IsComponent H K) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 9)
    (V : Subgroup H) [IsElementaryAbelian 2 V] :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≤ 8 := by
  let W := V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  exact (primeRank_le_iff_elementary_card_le _).mp
    (source_ordinary_linear_nine_rank_le_three T hP hs K hK hgen hm) W inferInstance

end CFSG.Quasithin.ChapterE.Structure
