module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BaumannPair
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BaumannFirst

/-!
# Keeping the full block conclusion for the original Baumann pair

Reapply C.1.24 to the same universal pair already chosen for LT and KT=H.
The shared-normalizer exclusions are reused. Each surviving block branch
now retains its actual subnormal placement, U(L)=V or U(K)=W under the
literal subtype map, and the original Thompson commutator identity.
The first member cannot be normalized by either group when Ω₁Z(T) has
order two. Thus opposite normalization is also excluded in that case.

SourceAssembly/NonsolvableBlocks applies this result after every original
rechoice and excludes either block when Ω₁Z(T) has order two.
Source: Aschbacher--Smith C.1.24(a), pp.130--131, used in the original
outside pair of 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- Compare both original groups using one pair, retaining the complete block alternatives. -/
theorem original_pair_baumann_block_alternatives
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
      ((IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5 ∧
          (blockU L).map L.subtype = V ∧ L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) ∨
        (IsBlock (K.subgroupOf H) ∧ IsAlternatingBlock K 5 ∧
          (blockU K).map K.subtype = W ∧ K = ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆) ∨
        (D.first ≠ D.second ∧
          ((L ⊔ (T : Subgroup G) ≤ normalizer
              (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
          (L ⊔ (T : Subgroup G) ≤ normalizer
              (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G))))) := by
  obtain ⟨D,hD,hn₁,hn₂,_⟩ := original_pair_baumann_alternatives d e hjoin hH hJd hJe
  refine ⟨D,hD,hn₁,hn₂,?_⟩
  have hd := d.original_baumann_pair_alternatives hJd D hD
  have he := e.original_baumann_pair_alternatives hJe D hD
  rw [hjoin] at he
  rcases hd with hd | hd | hd
  · rcases he with he | he | he
    · exact (hn₁ ⟨hd,he⟩).elim
    · exact Or.inr (Or.inr ⟨fun hh => hn₁ ⟨hd,hh.symm ▸ he⟩,Or.inl ⟨hd,he⟩⟩)
    · exact Or.inr (Or.inl he)
  · rcases he with he | he | he
    · exact Or.inr (Or.inr ⟨fun hh => hn₂ ⟨hd,hh ▸ he⟩,Or.inr ⟨hd,he⟩⟩)
    · exact (hn₂ ⟨hd,he⟩).elim
    · exact Or.inr (Or.inl he)
  · exact Or.inl hd
/-- With a prime Sylow omega-center, opposite normalization is impossible:
one of the two original components must be a genuine alternating block. -/
theorem original_pair_block_of_omega_card_two
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    IsAlternatingBlock L 5 ∨ IsAlternatingBlock K 5 := by
  obtain ⟨D,_,_,_,hcases⟩ := original_pair_baumann_block_alternatives d e hjoin hH hJd hJe
  rcases hcases with hb | hb | hn
  · exact Or.inl hb.2.1
  · exact Or.inr hb.2.1
  · have hd := d.first_baumann_not_normalized_of_omega_card_two hJd hz D
    have he := e.first_baumann_not_normalized_of_omega_card_two hJe hz D
    rw [hjoin] at he
    rcases hn.2 with hn | hn
    · exact (hd hn.1).elim
    · exact (he hn.2).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
