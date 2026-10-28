module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SourceBlock
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.Representation.NormalElementaryQuotient

/-!
# The actual short seed in a centralizer quotient

An elementary internal module containing U(K) kills U(K) in the action image,
but cannot kill all of K: that would centralize its noncentral moved layer.
The proved C.1.8 quotient by U(K) therefore gives an actual quasisimple or
cubic image. This is the original image used by C.1.27, not a model replacement.

Source: Aschbacher--Smith C.1.8 and C.1.27, printed pp.123 and133.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Support in an elementary internal module makes the actual short image
quasisimple or cubic; no abstract quotient model is substituted. -/
theorem short_image_kind (V K : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hK : IsShort K) (hUV : (blockU K).map K.subtype ≤ V) :
    IsQuasisimple (K.map (QuotientGroup.mk' (centralizer (V : Set G)))) ∨
      Nat.card (K.map (QuotientGroup.mk' (centralizer (V : Set G)))) = 3 := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let f := q.subgroupMap K
  have hU : blockU K ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff x.val).mpr
    intro v hv
    let a : V := ⟨x,hUV (mem_map_of_mem K.subtype hx)⟩
    let b : V := ⟨v,hv⟩
    exact congrArg Subtype.val (mul_comm b a)
  let g : (K ⧸ blockU K) →* K.map q := QuotientGroup.lift (blockU K) f hU
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective K) hU
  have hne : K.map q ≠ ⊥ := by
    intro he
    have hc : K ≤ centralizer (V : Set G) := by
      have hh := (map_eq_bot_iff K).mp he
      rwa [QuotientGroup.ker_mk'] at hh
    have hu : blockU K ≤ center K := by
      intro x hx
      exact mem_center_iff.mpr fun k => Subtype.ext
        (hc k.property x (hUV (mem_map_of_mem K.subtype hx))).symm
    exact hK.irreducible.1.ne (inf_eq_left.mpr hu)
  have hn : Nontrivial (K.map q) := (nontrivial_iff_ne_bot _).mpr hne
  let := hn
  rcases hK.quotient_blockU with hq | h3
  · let := hq
    exact Or.inl (IsQuasisimple.of_surjective g hg)
  · have hd : Nat.card (K.map q) ∣ 3 := h3 ▸ card_dvd_of_surjective g hg
    exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
      (fun h => hne (card_eq_one.mp h)))

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
