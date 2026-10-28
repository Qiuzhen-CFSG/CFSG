module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CoreCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import Theory.ElementaryAbelian.Injective

/-!
# Original endpoint cores and the literal complementary sections

Transport the full original parabolic two-cores through either endpoint of
the specified amalgam isomorphism. Their original Sylow containment places
them inside the same split U. Relative normality then identifies each core
with the literal complementary section, provided the earlier section 2/5
local-kernel containment holds. Elementary abelianness and the full-Borel
index follow the same maps.

The numerator of the marked quotient may be an infinite geometric completion.
Only the specified endpoint and overlap maps are used; there is no descent
map from that completion to the original ambient group.

Source: DGS, Groups and Graphs (1985), reduction pp.95--96 and (10.5),
(11.7)--(11.8), pp.156--157 and 174--176; Fong--Seitz I (2B), (5C),
and (6A), printed pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

include e in
/-- The full original endpoint core follows the same endpoint embedding. -/
theorem marked_core_map (i : Fin 2) :
    (((parabolic L S i).pCoreIn 2).subgroupOf (parabolic L S i)).map
        (MarkedLocal.endpointMap Q e i) =
      (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 := by
  change (((pCore 2 (parabolic L S i)).map (parabolic L S i).subtype).comap
    (parabolic L S i).subtype).map (MarkedLocal.endpointMap Q e i) = _
  rw [comap_map_eq_self_of_injective (parabolic L S i).subtype_injective,
    MarkedLocal.endpointMap, ← map_map, pCore_map_iso]
  rfl

include e in
/-- The original Sylow marking places the transported core in the specified U. -/
theorem marked_core_le_unipotent (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 ≤ split.U := by
  rw [← marked_core_map Q e i]
  rintro x ⟨a, ha, rfl⟩
  have hs : (a : G) ∈ S := h.parabolic_core_le_S i ha
  rw [← MarkedLocal.sylow_range Q e h split]
  exact ⟨⟨a, hs⟩, (MarkedLocal.endpoint_sylow Q e h i ⟨a, hs⟩).symm⟩

include e in
/-- Elementary abelianness transports through the full original endpoint. -/
theorem marked_core_elementary (i : Fin 2)
    (hc : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2)) :
    IsElementaryAbelian 2 ((Q.tits.standardParabolic {Q.simple i}).pCoreIn 2) := by
  let : IsElementaryAbelian 2
      ((pCore 2 (parabolic L S i)).map (parabolic L S i).subtype) := hc
  let a := MarkedLocal.endpoint Q e i
  let c := (pCore 2 (parabolic L S i)).equivMapOfInjective
    (parabolic L S i).subtype (parabolic L S i).subtype_injective
  let : IsElementaryAbelian 2 (pCore 2 (parabolic L S i)) :=
    IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  have hd : IsElementaryAbelian 2 ((pCore 2 (parabolic L S i)).map a.toMonoidHom) :=
    IsElementaryAbelian.map _
  rw [pCore_map_iso] at hd
  let := hd
  exact IsElementaryAbelian.map _

include e in
/-- The entire common Borel, with both amalgam squares retained, counts the simple root. -/
theorem marked_commonBorel_root_index (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    (commonBorel L S).relIndex (parabolic L S i) =
      1 + Nat.card (simpleRoot Q split i) := by
  rw [← lemma_F_1_3_6 h]
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa only [RankTwoAmalgam.ofSubgroups, inclusion_range, relIndex] using
      (marked_amalgam_left_index Q e).trans (singleton_parabolic_root_index Q split 0)
  · simpa only [RankTwoAmalgam.ofSubgroups, inclusion_range, relIndex] using
      (marked_amalgam_right_index Q e).trans (singleton_parabolic_root_index Q split 1)


include e in
/-- Earlier local-kernel containment identifies the actual section with the full core. -/
theorem marked_remainder_eq_core (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    simpleRemainder Q split i = (Q.tits.standardParabolic {Q.simple i}).pCoreIn 2 :=
  Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_eq_parabolic_core
    Q split i hV (marked_core_le_unipotent Q e h split i)

include e in
/-- The elementary-core clause of the original profile applies to this same complementary section. -/
theorem marked_remainder_elementary (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2)) :
    IsElementaryAbelian 2 (simpleRemainder Q split i) := by
  let := marked_core_elementary Q e i hc
  exact IsElementaryAbelian.of_injective
    (inclusion (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_le_parabolic_core
      Q split i hV)) (inclusion_injective _)

include e in
/-- An elementary original core supplies the exact opposite-root commutator in either orientation. -/
theorem marked_root_commutator_of_elementary_core (split : SplitData Q.tits)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split j ≤ localKernel Q j)
    (hc : IsElementaryAbelian 2 ((parabolic L S j).pCoreIn 2)) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  let := marked_core_elementary Q e j hc
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.root_commutator_eq_bot_of_abelian_core
    Q split i j hij hV inferInstance

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
