module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BaumannPair

/-!
# Comparing the same Baumann characteristic pair in the original outside pair

Choose one universal pair on Baum(T) and apply its original A₅ alternative
to both LT and KT=H. A nontrivial two-subgroup normalized by both groups
would have its full normalizer in N_G(L), by uniqueness over LT, forcing
H into that normalizer. Thus neither member of the prescribed pair can
be normalized by both groups. Unless one original component is an actual
alternating block, the groups normalize opposite, distinct pair members.

SourceAssembly/NonsolvableBaumannPair supplies both Contexts from the
original outside residual, with the source rechoice guards. The opposite
normalizer and alternating-block branches are retained; this does not
assert a residual elementary lift or n(H)>1.
Source: Aschbacher--Smith 1.2.7, C.1.18, C.1.24(a), and 13.2.8(1),
printed pp.506--507,126,130--131,880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterB ChapterC
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- No nontrivial subgroup of the original Sylow is normalized by both local groups. -/
theorem original_pair_common_normal_eq_bot
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (C : Subgroup G) (hCT : C ≤ (T : Subgroup G))
    (hLC : L ⊔ (T : Subgroup G) ≤ normalizer (C : Set G))
    (hHC : H ≤ normalizer (C : Set G)) : C = ⊥ := by
  by_contra hne
  have hn := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (T.isPGroup'.to_le hCT) hne hLC
  exact hH.1.2 (hHC.trans hn)

/-- Use one universal pair for both original groups. Unless a genuine
alternating block occurs, the groups normalize opposite members, and neither
member is normalized by both groups. -/
theorem original_pair_baumann_alternatives
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    ∃ D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)),
      D.Universal.{u,u} ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      (IsAlternatingBlock L 5 ∨ IsAlternatingBlock K 5 ∨
        (D.first ≠ D.second ∧
          ((L ⊔ (T : Subgroup G) ≤ normalizer
              (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
          (L ⊔ (T : Subgroup G) ≤ normalizer
              (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G))))) := by
  have hTne : (T : Subgroup G) ≠ ⊥ :=
    fun hz => d.chosen.ne_bot (bot_unique (d.chosen.le_sylow.trans_eq hz))
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  have hn (C : Subgroup (baumann (T : Subgroup G))) (hne : C ≠ ⊥) :
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (C.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G)) := by
    rintro ⟨hL,hH'⟩
    apply hne
    apply (C.map_eq_bot_iff_of_injective (baumann (T : Subgroup G)).subtype_injective).mp
    exact original_pair_common_normal_eq_bot d hH _
      ((map_subtype_le C).trans inf_le_left) hL hH'
  have hn₁ := hn D.first D.first_ne_bot
  have hn₂ := hn D.second D.second_ne_bot
  refine ⟨D,hD,hn₁,hn₂,?_⟩
  have hd := d.original_baumann_pair_alternatives hJd D hD
  have he := e.original_baumann_pair_alternatives hJe D hD
  rw [hjoin] at he
  rcases hd with hd | hd | hd
  · rcases he with he | he | he
    · exact (hn₁ ⟨hd,he⟩).elim
    · exact Or.inr (Or.inr ⟨fun hh => hn₁ ⟨hd,hh.symm ▸ he⟩,Or.inl ⟨hd,he⟩⟩)
    · exact Or.inr (Or.inl he.2.1)
  · rcases he with he | he | he
    · exact Or.inr (Or.inr ⟨fun hh => hn₂ ⟨hd,hh ▸ he⟩,Or.inr ⟨hd,he⟩⟩)
    · exact (hn₂ ⟨hd,he⟩).elim
    · exact Or.inr (Or.inl he.2.1)
  · exact Or.inl hd.2.1
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
