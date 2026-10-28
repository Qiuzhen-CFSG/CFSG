module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5RankTwo
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5G2Radical
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient

/-!
# The original module excludes the G₂(4) ordinary row

The original module lies in the center of the actual radical. Its image in
an ordinary G₂(4) factor therefore lies in the center of the quotient radical,
of order at most sixteen. The genuine covering bound gives kernel of order
at most two, contradicting a module of order sixty-four.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- A module of order sixty-four excludes the actual G₂(4) quotient, using
its radical placement and the proved bound on the original covering kernel. -/
theorem ordinary_not_g2_four_of_module_card
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hV : Nat.card V = 64) (K : Subgroup H) (hK : IsComponent H K)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) 4) : False := by
  let := hK.2
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (p := 2) (f := 2) (by simpa only [Nat.card_eq_fintype_card,show (2 : ℕ)^2=4 from rfl] using hF)
  let P := (R.subgroupOf H).subgroupOf K
  let W := (V.subgroupOf H).subgroupOf K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center K := by
    dsimp [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hP : P.IsPRadical 2 := h.ordinary_radical_intersection_isRadical K hK
  have hkP : q.ker ≤ P := by
    rw [hker,hz]
    exact pCore_le_of_pCore_normalizer_le P hP.isPGroup hP.2.le
  have hPn : P.map q ≠ ⊥ := by
    intro he
    have hc : P ≤ center K := hker ▸ (map_eq_bot_iff P).mp he
    apply h.ordinary_radical_intersection_not_centralizes K hK
    intro r hr k hk
    exact congrArg (fun x : K => (x : H))
      (mem_center_iff.mp (hc (show (⟨r,hr.2⟩ : K) ∈ P from hr.1)) ⟨k,hk⟩)
  have hPq : (P.map q).IsPRadical 2 :=
    ⟨hPn,map_normalizer_core_of_p_kernel P hP.isPGroup hP.2 q hq hkP⟩
  have hbound : Nat.card (center (P.map q)) ≤ 16 := by
    simpa only [hF,show (4 : ℕ)^2=16 from rfl] using
      OrdinaryPlacement.NormalNaturalA5G2.radical_center_card_le (P.map q) hPq
  have hWP : W ≤ P := subgroupOf_mono K ((h.ordinary_module_placement K hK).1.trans inf_le_left)
  have hcomm (w : K) (hw : w ∈ W) (v : K) (hv : v ∈ P) : v*w=w*v := by
    obtain ⟨z,hzc,he⟩ := h.module_le_center_radical hw
    have hc := congrArg (fun x : R => (x : G))
      (mem_center_iff.mp hzc ⟨v.val.val,hv⟩)
    apply Subtype.ext
    apply Subtype.ext
    change v.val.val * (z : G) = (z : G) * v.val.val at hc
    change (z : G) = w.val.val at he
    change v.val.val * w.val.val = w.val.val * v.val.val
    rwa [he] at hc
  have hWcenter : W.map q ≤ (center (P.map q)).map (P.map q).subtype := by
    rintro y ⟨w,hw,rfl⟩
    refine ⟨⟨q w,mem_map_of_mem q (hWP hw)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    rintro ⟨y,⟨v,hv,he⟩⟩
    apply Subtype.ext
    change y * q w = q w * y
    rw [←he,←map_mul,←map_mul,hcomm w hw v hv]
  have himage : Nat.card (W.map q) ≤ 16 := by
    have hh := Nat.card_le_card_of_injective (inclusion hWcenter)
      (inclusion_injective hWcenter)
    rw [card_map_of_injective (P.map q).subtype_injective] at hh
    exact hh.trans hbound
  have hkernel : Nat.card (q.ker.subgroupOf W) ≤ 2 := by
    calc
      _ ≤ Nat.card q.ker := Nat.card_le_card_of_injective
        (fun x : q.ker.subgroupOf W => (⟨x.val.val,x.property⟩ : q.ker))
        (fun x y hxy => Subtype.ext (Subtype.ext
          (congrArg (fun z : q.ker => (z : K)) hxy)))
      _ = Nat.card (center K) := congrArg (fun D : Subgroup K => Nat.card D) hker
      _ ≤ 2 := ChapterI.LieMultipliers.G2.fourSourceCenter_card_le_two_of_field e hF
  have hcard : Nat.card W = 64 := by
    have hVH := h.module_le.trans ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
    let a : W ≃* V :=
      (subgroupOfEquivOfLe ((h.ordinary_module_placement K hK).1.trans inf_le_right)).trans
        (subgroupOfEquivOfLe hVH)
    exact (Nat.card_congr a.toEquiv).trans hV
  have hcount : Nat.card (q.ker.subgroupOf W) * Nat.card (W.map q) = Nat.card W := by
    have hh := (q.comp W.subtype).ker.card_mul_index
    rw [index_ker] at hh
    have hr : (q.comp W.subtype).range = W.map q := by
      rw [←MonoidHom.map_range,W.range_subtype]
    rwa [hr] at hh
  have hh := Nat.mul_le_mul hkernel himage
  rw [hcount,hcard] at hh
  omega

/-- With a nontrivial central point, no binary G₂ ordinary row can support
the original module of order sixty-four. -/
theorem ordinary_not_g2_of_module_card
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hV : Nat.card V = 64) (K : Subgroup H) (hK : IsComponent H K)
    (hz : center K ≠ ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) (2^n)) : False := by
  obtain ⟨hn2,_⟩ := h.ordinary_g2_nontrivial_center K hK hz hn hm
  subst n
  exact h.ordinary_not_g2_four_of_module_card hV K hK hm

end CFSG.Quasithin.ChapterC.HypothesisC28
