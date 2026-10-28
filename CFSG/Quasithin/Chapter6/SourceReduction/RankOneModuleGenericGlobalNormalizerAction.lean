module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizer

/-!
# Faithful actions of the full normalizer completion

Write K = O²(H), J = ⟨L,K⟩ and M₀ = ⟨N_G(L),N_G(K)⟩. The source
normalizer product decompositions imply M₀ normalizes J. Its full ambient
centralizer lies in both normalizers and is normal in M₀. The trivial
M₀ two-core and characteristic two in a vertex force this centralizer to
vanish. Consequently conjugation embeds M₀ in Aut(J), with all inner
automorphisms in its image. Restricting this same map to the two full
normalizers gives faithful maps agreeing on their whole intersection,
and that intersection is exactly the intersection of their images.

These are actual actions on the original factor join, independently of
recognition. They apply also when the original S has index two over the
common factor Sylow: neither S nor the full overlap is replaced by that
Sylow. The Chapter12 companion discharges the local-condition input using
the completed Ree maximality theorem. Exhaustive amalgam comparison,
recognition of J as a concrete Lie group, and ambient recognition remain
with the generic-global owner. No assertion J = G is made here.

Source: Aschbacher–Smith 5.2.7 and 5.3.1–2, printed pp.651,658–659
(`refs/quasithin.pdf`). This supplies the faithful action and whole-overlap
compatibility needed by 5.3.2 after the perfect completion is identified.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G] {L K R : Subgroup G}

omit [Finite G] in
private theorem pair_normalizes_join :
    normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer ((L ⊔ K : Subgroup G) : Set G) :=
  normalizer_inf_normalizer_le_normalizer_sup L K

private theorem normalizer_pair_product
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    normalizer (L : Set G) ⊔ normalizer (K : Set G) =
      (L ⊔ K) ⊔ (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨l,hl,b,hb,rfl⟩ := h.factor_left x hx
      exact (L ⊔ K ⊔ (normalizer (L : Set G) ⊓ normalizer (K : Set G))).mul_mem
        (mem_sup_left (mem_sup_left hl)) (mem_sup_right hb)
    · intro x hx
      obtain ⟨k,hk,b,hb,rfl⟩ := h.factor_right x hx
      exact (L ⊔ K ⊔ (normalizer (L : Set G) ⊓ normalizer (K : Set G))).mul_mem
        (mem_sup_left (mem_sup_right hk)) (mem_sup_right hb)
  · exact sup_le (sup_le (L.le_normalizer.trans le_sup_left)
      (K.le_normalizer.trans le_sup_right)) (inf_le_left.trans le_sup_left)

/-- The full pair normalizes the join of the original factors. -/
theorem normalizer_pair_normalizes
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    normalizer (L : Set G) ⊔ normalizer (K : Set G) ≤
      normalizer ((L ⊔ K : Subgroup G) : Set G) := by
  rw [normalizer_pair_product h]
  exact sup_le (L ⊔ K).le_normalizer pair_normalizes_join

/-- The centralizer in the whole ambient group is trivial. -/
theorem normalizer_pair_centralizer_eq_bot
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    centralizer ((L ⊔ K : Subgroup G) : Set G) = ⊥ := by
  have hC : centralizer ((L ⊔ K : Subgroup G) : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (K : Set G) :=
    le_inf ((centralizer_le (show (L : Set G) ⊆ (L ⊔ K : Subgroup G) from fun _ hx => mem_sup_left hx)).trans (Subgroup.centralizer_le_normalizer _))
      ((centralizer_le (show (K : Set G) ⊆ (L ⊔ K : Subgroup G) from fun _ hx => mem_sup_right hx)).trans (Subgroup.centralizer_le_normalizer _))
  have hn := (normalizer_pair_normalizes h).trans
    (normalizer_le_normalizer_centralizer (L ⊔ K))
  exact AmalgamLocalCores.common_normal_eq_bot
    (normalizer (L : Set G)) (normalizer (K : Set G)) _ hC
    (le_sup_left.trans hn) (le_sup_right.trans hn) h.generated_twoCore
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.fitting_left)

/-- Faithful conjugation on the literal factor join. -/
theorem normalizer_pair_faithful_action
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    ∃ ρ : (normalizer (L : Set G) ⊔ normalizer (K : Set G) : Subgroup G) →*
        MulAut (L ⊔ K : Subgroup G),
      Function.Injective ρ ∧ ∀ g x, ((ρ g x : (L ⊔ K : Subgroup G)) : G) =
        (g : G) * (x : G) * (g : G)⁻¹ := by
  let ρ := (L ⊔ K).normalizerMonoidHom.comp (inclusion (normalizer_pair_normalizes h))
  refine ⟨ρ,?_,?_⟩
  · apply (MonoidHom.ker_eq_bot_iff ρ).mp
    ext g
    change ρ g = 1 ↔ g = 1
    constructor
    · intro hg
      have hc : (g : G) ∈ centralizer ((L ⊔ K : Subgroup G) : Set G) := by
        have hk : inclusion (normalizer_pair_normalizes h) g ∈
            (L ⊔ K).normalizerMonoidHom.ker := hg
        rwa [normalizerMonoidHom_ker] at hk
      rw [normalizer_pair_centralizer_eq_bot h] at hc
      exact Subtype.ext (mem_bot.mp hc)
    · rintro rfl
      exact map_one ρ
  · intro g x
    rfl

/-- The conjugation image contains all inner automorphisms of the factor join. -/
theorem normalizer_pair_inner_action
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    ∃ ρ : (normalizer (L : Set G) ⊔ normalizer (K : Set G) : Subgroup G) →*
        MulAut (L ⊔ K : Subgroup G),
      Function.Injective ρ ∧
      (∀ g x, ((ρ g x : (L ⊔ K : Subgroup G)) : G) =
        (g : G) * (x : G) * (g : G)⁻¹) ∧
      (MulAut.conj : (L ⊔ K : Subgroup G) →* MulAut (L ⊔ K : Subgroup G)).range ≤ ρ.range := by
  obtain ⟨ρ,hρ,he⟩ := normalizer_pair_faithful_action h
  refine ⟨ρ,hρ,he,?_⟩
  rintro a ⟨x,rfl⟩
  have hx : (x : G) ∈ normalizer (L : Set G) ⊔ normalizer (K : Set G) :=
    (sup_le (L.le_normalizer.trans le_sup_left) (K.le_normalizer.trans le_sup_right)) x.property
  refine ⟨⟨x,hx⟩,?_⟩
  ext y
  exact he ⟨x,hx⟩ y

/-- The two full-normalizer actions have exactly the whole overlap as intersection. -/
theorem normalizer_pair_compatible_actions
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R) :
    ∃ (l : normalizer (L : Set G) →* MulAut (L ⊔ K : Subgroup G))
      (r : normalizer (K : Set G) →* MulAut (L ⊔ K : Subgroup G))
      (b : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
        MulAut (L ⊔ K : Subgroup G)),
      Function.Injective l ∧ Function.Injective r ∧ Function.Injective b ∧
      (∀ g x, ((l g x : (L ⊔ K : Subgroup G)) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
      (∀ g x, ((r g x : (L ⊔ K : Subgroup G)) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
      (∀ x, l (inclusion inf_le_left x) = b x) ∧
      (∀ x, r (inclusion inf_le_right x) = b x) ∧
      l.range ⊓ r.range = b.range ∧
      (MulAut.conj : (L ⊔ K : Subgroup G) →* MulAut (L ⊔ K : Subgroup G)).range ≤
        l.range ⊔ r.range := by
  obtain ⟨ρ,hρ,he,hi⟩ := normalizer_pair_inner_action h
  let l := ρ.comp (inclusion (show normalizer (L : Set G) ≤
    normalizer (L : Set G) ⊔ normalizer (K : Set G) from le_sup_left))
  let r := ρ.comp (inclusion (show normalizer (K : Set G) ≤
    normalizer (L : Set G) ⊔ normalizer (K : Set G) from le_sup_right))
  let b := l.comp (inclusion (show normalizer (L : Set G) ⊓ normalizer (K : Set G) ≤
    normalizer (L : Set G) from inf_le_left))
  have hl : Function.Injective l := hρ.comp (inclusion_injective _)
  have hr : Function.Injective r := hρ.comp (inclusion_injective _)
  have hb : Function.Injective b := hl.comp (inclusion_injective _)
  refine ⟨l,r,b,hl,hr,hb,fun g x => he _ x,fun g x => he _ x,
    fun _ => rfl,fun _ => rfl,?_,?_⟩
  · apply le_antisymm
    · rintro a ⟨⟨x,rfl⟩,⟨y,hy⟩⟩
      have hxy : (y : G) = (x : G) := congrArg Subtype.val (hρ hy)
      refine ⟨⟨x,⟨x.property,hxy ▸ y.property⟩⟩,rfl⟩
    · rintro a ⟨x,rfl⟩
      exact ⟨⟨inclusion inf_le_left x,rfl⟩,⟨inclusion inf_le_right x,rfl⟩⟩
  · apply hi.trans
    have ht :
        (normalizer (L : Set G)).subgroupOf
          (normalizer (L : Set G) ⊔ normalizer (K : Set G)) ⊔
        (normalizer (K : Set G)).subgroupOf
          (normalizer (L : Set G) ⊔ normalizer (K : Set G)) = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    change ρ.range ≤ (ρ.comp _).range ⊔ (ρ.comp _).range
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range,
      ← Subgroup.map_sup,ht,← MonoidHom.range_eq_map]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
