module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.StrictSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.Source
/-!
# The strict original cubic bound outside nonbinary Sp4

The complete binary Sp4 source constructs its original two-conjugate pair
and proves its strict action bound. Together with the other source families,
this leaves precisely the normal nonbinary symplectic row, retaining its
actual component and full-core quotient map.
Source: Aschbacher–Smith E.2.7–9 and E.2.15, pp.219–222,228.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_cubicRatio_lt_two_or_nonbinary_symplectic
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ g ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 ∨
      ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧ K ⊔ (T : Subgroup H) = ⊤ ∧
        ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp
          (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f) := by
  rcases source_cubicRatio_lt_two_or_symplectic hH T hP V U hVT hvn hVM hout hfit hTI hTU hU with
    hb | ⟨K,hK,hN,hgen,hm⟩
  · exact Or.inl hb
  let := hN
  rcases hm with hm | ⟨e⟩
  · exact Or.inr ⟨K,hK,hN,hgen,hm⟩
  · rcases e with ⟨e⟩
    have hs : ¬ Group.IsSolvable H := by
      intro h
      let := h
      exact hK.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)
    exact Or.inl (SymplecticFour.Binary.source_cubicRatio_lt_two T hP hs K hK hgen e
      V hVT hvn hVM hout hfit hTI U hTU hU)
end CFSG.Quasithin.ChapterE.Witnesses
