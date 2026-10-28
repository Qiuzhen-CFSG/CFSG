module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceReconstruction
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.SmallBound

/-!
# The Gol80 vertex-size consequence

For a finite Goldschmidt triple with trivial ambient two-core, the common
Sylow subgroup has order at most 128 and either vertex has order at most 384.
If the original overlap has order at least 64, the opposite-kernel coset
bound forces both vertices to have characteristic two. The small C3 and A4
residual reductions then supply the actual large universal residual action.
The four explicit source cuts recognize its marked normal base; the proved
normal-base reconstruction returns one of the four exceptional amalgams,
whose marked overlap has order 32, 64, 64, or 128.

Only the universal completion's vertex groups are finite. No lower bound
on its residual overlap, model assumption, or characteristic-two premise is
retained. This numerical consequence is separate from the compatible marked
enumeration; final discharge of its four source premises remains with the
`qt-goldschmidt-f6` assembly.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Theorem A,
Table 1 and Sections 3--6, pp.378--406. The small opposite-kernel bound is
also the exceptional branch of Aschbacher--Smith F.6.5, pp.304--305.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
open SourceAssembly SourceAssembly.Goldschmidt GreenBook
universe u

private theorem exceptional_overlap_card_le {G : Type*} [Group G]
    {A B : Subgroup G} (h : ExceptionalMarkedAmalgam A B) :
    Nat.card (A ⊓ B : Subgroup G) ≤ 128 := by
  rcases h with ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · rw [Nat.card_congr e.some.middle.toEquiv]
    have hc : Nat.card ExceptionalModels.G2.derivedB = 32 :=
      Atlas.G2.BinaryParabolicPair.card_derivedSylow
    omega
  · rw [Nat.card_congr e.some.middle.toEquiv]
    have hc : Nat.card ExceptionalModels.G2.fullB = 64 :=
      Atlas.G2.BinaryParabolicPair.card_unipotent_binary
    omega
  · rw [Nat.card_congr e.some.middle.toEquiv, MathieuTwelve.B_eq_S]
    exact (show Nat.card MathieuTwelve.S = 64 from
      Sporadic.Mathieu.M12SmallPair.card_sylowCandidate).le.trans (by decide)
  · rw [Nat.card_congr e.some.middle.toEquiv, AutMathieuTwelve.autB,
      card_map_of_injective (f := AutMathieuTwelve.ambientEquiv.toMonoidHom)
        AutMathieuTwelve.ambientEquiv.injective,
      AutMathieuTwelve.B_eq_S]
    exact (Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates.card_overlap
      Sporadic.Mathieu.M12ExceptionalExtension.innerModel).le

variable (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u})
include labels radius two three

/-- The bound is on the original common Sylow subgroup. Characteristic two
at both vertices is derived in the large case, rather than assumed. -/
theorem IsGoldschmidtTriple.intersection_card_le_128_of_source_cuts
    {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    Nat.card (A ⊓ B : Subgroup G) ≤ 128 := by
  by_cases hlarge : 64 ≤ Nat.card (A ⊓ B : Subgroup G)
  · have hA : generalizedFitting A = pCore 2 A := by
      by_contra hbad
      have hh := h.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad
      omega
    have hB : generalizedFitting B = pCore 2 B := by
      by_contra hbad
      have hh := h.symm.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad
      rw [inf_comm B A] at hh
      omega
    obtain ⟨s, hs⟩ := exists_largeTreeSource h hcore hA hB hlarge
    have hm := marked_base_of_source_cuts labels radius two three hs
    let F := RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B)
    have ht : CubicTreeAction F := universalCubicTreeAction_of_goldschmidt h hcore
    have hb : Nat.card (F false ⊓ F true : Subgroup _) ≤ 128 := by
      rcases exceptional_of_marked_residual ht hm with hAB | hBA
      · exact exceptional_overlap_card_le hAB
      · simpa only [inf_comm (F true) (F false)] using exceptional_overlap_card_le hBA
    let e := RankTwoAmalgam.Universal.markedIso (inclusionAmalgam A B)
      (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
    exact (Nat.card_congr e.middle.toEquiv).le.trans hb
  · omega

/-- The universal Gol80 vertex-size consequence used in Chapter 14, conditional
only on the four independent geometric and marked-recognition source cuts. -/
theorem IsGoldschmidtTriple.card_le_384_of_source_cuts
    {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) : Nat.card A ≤ 384 := by
  have hb := h.intersection_card_le_128_of_source_cuts labels radius two three hcore
  rw [h.local_card_eq_three_mul_intersection]
  omega

end CFSG.Quasithin.ChapterF
