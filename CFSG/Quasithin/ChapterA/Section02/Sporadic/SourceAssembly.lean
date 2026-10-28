module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Common
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Covers
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.HaradaNorton
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.SimpleRanks
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.LocalSections

/-!
# Sporadic source reductions with every carrier branch retained

The twenty-six actual sporadic carriers are split explicitly. The simple
case reduces to the precise output list and the two remaining Fischer model
inputs. The original central-cover counterexample reduces to McL, O’Nan
with center prime three, and the three Fischer carriers. These are source
reductions, not assertions that the remaining model inputs are proved.

Source: Aschbacher–Smith A.2.19, printed pp.40–41 (Case I and Case II).
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

public theorem sporadic_simple_reduction [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (hspor : KnownSimple.IsSporadicCarrier G) :
    IsTheoremBSporadicModel G ∨
      Nonempty (G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.Fischer.Fi24Prime.Carrier) := by
  obtain ⟨name,⟨e⟩⟩ := hspor
  cases name with
  | m11 => exact Or.inl (Or.inl ⟨.m11,⟨e⟩⟩)
  | m12 => exact Or.inl (Or.inl ⟨.m12,⟨e⟩⟩)
  | m22 => exact Or.inl (Or.inl ⟨.m22,⟨e⟩⟩)
  | m23 => exact Or.inl (Or.inl ⟨.m23,⟨e⟩⟩)
  | m24 => exact Or.inl (Or.inl ⟨.m24,⟨e⟩⟩)
  | j1 => exact Or.inl (Or.inr (Or.inl ⟨e⟩))
  | j2 => exact Or.inl (Or.inl ⟨.j2,⟨e⟩⟩)
  | j3 => exact Or.inl (Or.inl ⟨.j3,⟨e⟩⟩)
  | j4 => exact Or.inl (Or.inl ⟨.j4,⟨e⟩⟩)
  | hs => exact Or.inl (Or.inl ⟨.hs,⟨e⟩⟩)
  | mcl => exact Or.inl (Or.inr (Or.inr ⟨e⟩))
  | he => exact Or.inl (Or.inl ⟨.he,⟨e⟩⟩)
  | ru => exact Or.inl (Or.inl ⟨.ru,⟨e⟩⟩)
  | suz => exact (simple_suz ih hG hK hna e).elim
  | onan => exact (simple_onan e hG).elim
  | co1 => exact (simple_co1 ih hG hK hna e).elim
  | co2 => exact (simple_co2 ih hG hK hna e).elim
  | co3 => exact (simple_co3 ih hG hK hna e).elim
  | fi22 => exact (simple_fi22 e hG).elim
  | fi23 => exact Or.inr (Or.inl ⟨e⟩)
  | fi24Prime => exact Or.inr (Or.inr ⟨e⟩)
  | hn => exact (simple_hn e hG).elim
  | ly => exact (simple_ly ih hG hK hna e).elim
  | th => exact (simple_th ih hG hK hna e).elim
  | babyMonster => exact (simple_babyMonster e hG).elim
  | monster => exact (simple_monster ih hG hK hna e).elim

public theorem sporadic_strong_simple_reduction [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (hs : IsStronglyQuasithin G)
    (hspor : KnownSimple.IsSporadicCarrier G) :
    IsTheoremCModel G ∨
      Nonempty (G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.Fischer.Fi24Prime.Carrier) :=
  (sporadic_simple_reduction ih hG hK hna hspor).imp_left
    (theoremC_of_theoremBSporadicModel hs)

public theorem sporadic_cover_reduction {S : Type u} [Group S] [Finite S]
    [IsQuasisimple G] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G)) :
    Nonempty (G ⧸ center G ≃* _root_.Sporadic.LeechRelated.McL.Carrier) ∨
      (p = 3 ∧ Nonempty (G ⧸ center G ≃* ONan.Model)) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi22.Carrier) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) ∨
      Nonempty (G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi24Prime.Carrier) := by
  obtain ⟨name,⟨e⟩⟩ := hspor
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact h.2.2.2.2.2.1.pow
  cases name with
  | m11 => exact (cover_m11 h ih hP e).elim
  | m12 => exact (cover_m12 h ih hP e).elim
  | m22 => exact (cover_m22 h ih hP e).elim
  | m23 => exact (cover_m23 h ih hP e).elim
  | m24 => exact (cover_m24 h ih hP e).elim
  | j1 => exact (cover_j1 h ih hP e).elim
  | j2 => exact (cover_j2 h ih hP e).elim
  | j3 => exact (cover_j3 h ih hP e).elim
  | j4 => exact (cover_j4 h ih hP e).elim
  | hs => exact (cover_hs h ih hP e).elim
  | mcl => exact Or.inl ⟨e⟩
  | he => exact (cover_he h ih hP e).elim
  | ru => exact (cover_ru h ih hP e).elim
  | suz => exact (cover_suz ih h.1 h.2.1 e).elim
  | onan => exact Or.inr (Or.inl ⟨cover_onan_prime_three h.2.2.2.2.1 hP e h.1,⟨e⟩⟩)
  | co1 => exact (cover_co1 ih h.1 h.2.1 e).elim
  | co2 => exact (cover_co2 ih h.1 h.2.1 e).elim
  | co3 => exact (cover_co3 ih h.1 h.2.1 e).elim
  | fi22 => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | fi23 => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | fi24Prime => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
  | hn => exact (cover_hn h.2.2.2.2.1 h.2.2.2.2.2.1 hP e h.1).elim
  | ly => exact (cover_ly ih h.1 h.2.1 e).elim
  | th => exact (cover_th ih h.1 h.2.1 e).elim
  | babyMonster => exact (cover_babyMonster ih h.1 h.2.1 e).elim
  | monster => exact (cover_monster ih h.1 h.2.1 e ho).elim

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
