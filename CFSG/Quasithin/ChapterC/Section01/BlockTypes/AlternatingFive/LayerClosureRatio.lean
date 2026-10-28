module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.NormalClosure
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Small quadratic ratio from the original A₅ layer split

For a normal elementary abelian W split as U(L) times C_W(L), the
centralizer quotient contains the original L/O₂(L) as an A₅ subgroup.
Choose an involution in that subgroup. Its displacement on W equals its
displacement on the four-dimensional U(L), and therefore has dimension
at most two. Its cyclic group witnesses q ≤ 2 for the literal action.

Source: Aschbacher–Smith 10.2.1, printed p.743. This supplies the numerical
input for the contained-layer branch, without classifying the overcomponent.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
/-- The original block has exactly its two-core as kernel on the split layer closure. -/
theorem IsAlternatingBlock.layer_split_quotient_kernel (L W : Subgroup G)
    (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (q : G →* H) (hk : q.ker = centralizer (W : Set G)) :
    (q.subgroupMap L).ker = pCore 2 L := by
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change q (l:G) = 1 ↔ l ∈ pCore 2 L
  rw [←MonoidHom.mem_ker,hk,←h.2.1.centralizer_blockU]
  constructor
  · intro hl u hu
    exact Subtype.ext (hl u (hUW (mem_map_of_mem L.subtype hu)))
  · intro hl
    have hU : (l:G) ∈ centralizer ((blockU L).map L.subtype : Set G) := by
      rintro u ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hl v hv)
    have hC : (l:G) ∈ centralizer (W ⊓ centralizer (L : Set G) : Set G) := by
      intro c hc
      exact (hc.2 l l.property).symm
    have hu : (blockU L).map L.subtype ≤ centralizer ({(l:G)} : Set G) := by
      intro u hu x hx
      have hx : x = (l:G) := Set.mem_singleton_iff.mp hx
      rw [hx]
      exact (hU u hu).symm
    have hc : W ⊓ centralizer (L : Set G) ≤ centralizer ({(l:G)} : Set G) := by
      intro c hc x hx
      have hx : x = (l:G) := Set.mem_singleton_iff.mp hx
      rw [hx]
      exact (hC c hc).symm
    have hw : W ≤ centralizer ({(l:G)} : Set G) := by rw [hs]; exact sup_le hu hc
    intro w hw'
    exact (hw hw' (l:G) (Set.mem_singleton _)).symm

omit [Finite G] [Finite H] in
/-- The image of the original block on its split layer closure is the actual A₅. -/
theorem IsAlternatingBlock.layer_split_quotient_image (L W : Subgroup G)
    (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (q : G →* H) (hk : q.ker = centralizer (W : Set G)) :
    Nonempty (L.map q ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let d : (L ⧸ pCore 2 L) ≃* L.map q :=
    (QuotientGroup.quotientMulEquivOfEq (h.layer_split_quotient_kernel L W hUW hs q hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap L) (q.subgroupMap_surjective L))
  exact ⟨d.symm.trans e⟩

/-- The actual centralizer quotient has an involution of displacement rank at most two. -/
theorem IsAlternatingBlock.layer_split_quotient_small_involution (L W : Subgroup G) [W.Normal]
    [IsElementaryAbelian 2 W] (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set G)) :
    ∃ t : H, t ∈ L.map q ∧ orderOf t = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range
        (NormalElementaryQuotient.representation W q hq hk t - 1)) ≤ 2 ∧
      quadraticRatio (NormalElementaryQuotient.representation W q hq hk) ≤ 2 := by
  let U := (blockU L).map L.subtype
  let K := L.map q
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let σ := ρ.comp K.subtype
  let J : Subrepresentation σ := {
    toSubmodule := NormalElementaryQuotient.subspace W (U.subgroupOf W)
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨l,hl,he⟩ := g.property
      change ((ρ (g:H) v).toMul:G) ∈ U
      rw [←he,NormalElementaryQuotient.representation_apply]
      exact (L.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image L (blockU L)) hl v.toMul).mp hv }
  have hd : Module.finrank (ZMod 2) J.toSubmodule = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) J.toSubmodule = Nat.card J.toSubmodule := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = Nat.card (U.subgroupOf W) := rfl
      _ = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv
      _ = 2^4 := (card_map_of_injective L.subtype_injective).trans h.blockU_card
  have hspan : J.toSubmodule ⊔ fixedSpace σ ⊤ = ⊤ := by
    apply top_unique
    intro v hv
    have hjoin : U.subgroupOf W ⊔ (W ⊓ centralizer (L : Set G)).subgroupOf W = ⊤ := by
      apply map_injective W.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hUW,
        map_subgroupOf_eq_of_le inf_le_left,←hs,←MonoidHom.range_eq_map,range_subtype]
    obtain ⟨u,hu,c,hc,he⟩ := Subgroup.mem_sup.mp (hjoin ▸ mem_top v.toMul)
    have huJ : Additive.ofMul u ∈ J.toSubmodule := hu
    have hcF : Additive.ofMul c ∈ fixedSpace σ ⊤ := by
      intro a
      obtain ⟨l,hl,he⟩ := a.val.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((ρ (a.val:H) (Additive.ofMul c)).toMul:G) = c
      rw [←he,NormalElementaryQuotient.representation_apply]
      change l * (c:G) * l⁻¹ = c
      have hec : l * (c:G) = (c:G) * l := hc.2 l hl
      rw [hec,mul_inv_cancel_right]
    have hev : Additive.ofMul u + Additive.ofMul c = v := congrArg Additive.ofMul he
    exact hev ▸ Submodule.add_mem_sup huJ hcF
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let ek : (L ⧸ pCore 2 L) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq (h.layer_split_quotient_kernel L W hUW hs q hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap L) (q.subgroupMap_surjective L))
  have hcard : Nat.card K = 60 := by
    rw [Nat.card_congr (ek.symm.trans e).toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hcard]; decide)
  have hspanT : J.toSubmodule ⊔ fixedSpace σ (zpowers t) = ⊤ :=
    top_unique (hspan ▸ sup_le_sup_left
      (show fixedSpace σ ⊤ ≤ fixedSpace σ (zpowers t) from
        fun v hv a => hv ⟨a,mem_top _⟩) J.toSubmodule)
  have hdim := (involution_actor_rank_and_fixedCodim J.toRepresentation t ht).2.2.2
  rw [hd,(fixedCodim_subrepresentation_eq_iff σ J (zpowers t)).mpr hspanT] at hdim
  have htH : orderOf (t:H) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨hA,hAr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ (t:H) htH
  have hcod : fixedCodim σ (zpowers t) = fixedCodim ρ (zpowers (t:H)) := by
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,MonoidHom.map_zpowers]
    rfl
  rw [hcod] at hdim
  have hr : fixedCodim ρ (zpowers (t:H)) ≤ 2 := by omega
  refine ⟨t,t.property,htH,?_,?_⟩
  · rwa [fixedCodim_zpowers_eq_displacement_rank] at hr
  · apply (quadraticRatio_le_two_iff ρ).mpr
    refine ⟨zpowers (t:H),hA,hquad,?_⟩
    rwa [hAr,Nat.mul_one]

/-- The cyclic involution on the original split closure supplies the B.4 ratio bound. -/
theorem IsAlternatingBlock.normalClosure_quotient_quadraticRatio_le_two
    (L W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set G)) :
    quadraticRatio (NormalElementaryQuotient.representation W q hq hk) ≤ 2 := by
  obtain ⟨_,_,_,_,hq⟩ := h.layer_split_quotient_small_involution L W hUW hs q hq hk
  exact hq
end CFSG.Quasithin.ChapterC
