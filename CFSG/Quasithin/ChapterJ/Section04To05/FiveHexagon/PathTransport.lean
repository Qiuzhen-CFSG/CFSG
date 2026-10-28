module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.Geometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.ShortPaths
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedInverter

/-!
# Original long-root labels along the J.4.7 four-point path

The actual faithful completion of a compatibly marked source amalgam supplies
an explicit nonbacktracking four-edge path. The genuine F.4.6 nine-path action
makes it a geodesic, while three endpoint-local root equations identify its
last central involution with the original marked inverter. Its ambient fusion
therefore follows without smallness or a global completion equivalence.

The same middle embedding transfers the order-four product of the two marked
six-step endpoint words; no six-step geodesic assertion is made here. The final
consumer applies the original five-centralizer results with their ambient-fusion
premise discharged. The compatible F.1.12 amalgam marking and its original z
and five-subgroup equations remain with their earlier source producer.

Source: Aschbacher--Smith, F.4.6 and J.4.7, printed pp.276 and442–444.
-/

public section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo
open MarkedInverter Centralizers.Choices
noncomputable section

variable {K : Type*} [Group K] (q : Completion K)

theorem four_point_distance :
    q.graph.dist (base q.family false) (completionFourthWord q • base q.family false) = 4 :=
  q.four_path_geodesic (completionFourPath q) (completionFourPath_nonbacktracking q)

theorem modelZ_middle : modelZ = amalgam.left (middleRoot 9) := by
  apply Subtype.ext
  exact middleRoot_nine_coe.symm

theorem modelU_middle : modelU = amalgam.left (middleRootOne^2) := by
  apply Subtype.ext
  exact middleRootOne_square_coe.symm

theorem marked_fusion : IsConj (q.left modelU) (q.left modelZ) := by
  rw [modelZ_middle,modelU_middle]
  exact completion_fusion q

theorem marked_four_point :
    q.graph.dist (base q.family false) (completionFourthWord q • base q.family false) = 4 ∧
    orderOf (q.left modelU) = 2 ∧
    stabilizer q.family (completionFourthWord q • base q.family false) ≤
      centralizer {q.left modelU} ∧
    IsConj (q.left modelU) (q.left modelZ) := by
  refine ⟨four_point_distance q,?_,?_,marked_fusion q⟩
  · obtain ⟨g,hg⟩ := marked_fusion q
    have ho := SemiconjBy.orderOf_eq (g : K) hg
    rw [ho,modelZ_middle]
    exact completion_root_order q
  · rw [modelU_middle]
    exact completion_fourth_centralizes q

/-- Construct the actual completion from the compatible source amalgam
isomorphism. The source endpoint embeddings are the original subgroup inclusions. -/
theorem ofSource_marked_fusion
    (P₁ T P₂ : Subgroup K) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂) amalgam) :
    IsConj (e.left.symm modelU : K) (e.left.symm modelZ : K) :=
  marked_fusion (ofSource P₁ T P₂ h₁ h₂ hgen e)

/-- The two literal endpoint labels of the centered six-step word have product
order four; this algebraic assertion makes no claim that the six-step walk is shortest. -/
theorem marked_six_word_product_order :
    orderOf ((completionLeftWord q * q.left modelZ * (completionLeftWord q)⁻¹) * q.left modelU) = 4 := by
  rw [modelZ_middle,modelU_middle]
  change orderOf ((completionLeftWord q * q.middle (middleRoot 9) * (completionLeftWord q)⁻¹) *
    q.middle (middleRootOne^2)) = 4
  rw [completion_leftSix_conjugates]
  exact completion_endpoints_product_order q

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Centralizers.Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : K →* G)

/-- Literal compatibility of the earlier amalgam marking transports fusion
into the original ambient group, even when the completion generates a proper subgroup. -/
theorem source_fusion
    (hleft : ∀ a : first, f (q.left a) = (e a : G))
    (hz : (e modelZ : G) = c.z) : IsConj (sourceU e) c.z := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (marked_fusion q)
  apply isConj_iff.mpr
  refine ⟨f g,?_⟩
  have he := congrArg f hg
  simpa only [map_mul,map_inv,hleft,hz,sourceU] using he

/-- The original five-centralizer pair now follows from the earlier marked
completion, with no ambient-fusion premise. -/
theorem source_fixed_pair
    (hleft : ∀ a : first, f (q.left a) = (e a : G))
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    Nat.card (fixedFive B5 (sourceU e)) = 5 ∧
      Nat.card (fixedFive B5 (c.z * sourceU e)) = 5 ∧
      IsElementaryAbelian 5 (B5Image B5 ⊔ fixedFive B5 (sourceU e) : Subgroup G) ∧
      centralizer ((B5Image B5 ⊔ fixedFive B5 (sourceU e) : Subgroup G) : Set G) =
        B5Image B5 ⊔ fixedFive B5 (sourceU e) :=
  MarkedInverter.source_fixed_pair c B5 e hz hfive (source_fusion q c e f hleft hz)

end
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
