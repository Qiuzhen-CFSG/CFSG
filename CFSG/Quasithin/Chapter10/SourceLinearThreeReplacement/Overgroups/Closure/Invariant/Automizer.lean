module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.WreathModel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Seed

/-!
# Recovering the complement automizer from the actual wreath quotient

The quotient map XT → S₃ wreath C₂ is injective on P, since its kernel is
a two-group. The specified plane isomorphism identifies its image with the
cubic base E₉. On N_T(P), the quotient map and the conjugation action on P
have the same kernel: the centralizer of the cubic base contains no
nontrivial two-subgroup. Finally T = O₂(X) N_T(P) makes the image of
N_T(P) a full Sylow two-subgroup of the wreath quotient. The two first
isomorphism theorems therefore give the actual Aut_T(P) ≃ D₈.

This supplies the action premise used by the model exclusions in source
10.2.4; no model is inferred from a group-family label.
Source: Aschbacher--Smith, 10.2.4, printed p.747, using 1.3.2--4.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The source wreath quotient forces the actual complement automizer D₈. -/
theorem automizer_equiv_dihedral {X P H : Subgroup G}
    (h : LocalInput 3 (T : Subgroup G) X P H)
    (hp : Nonempty (P ≃* Plane 3))
    (hw : Nonempty (XiQuotient (X ⊔ (T : Subgroup G)) ≃* ParabolicWreath)) :
    Nonempty (automizer (T : Subgroup G) P ≃* DihedralGroup 4) := by
  obtain ⟨eP⟩ := hp
  obtain ⟨e⟩ := hw
  let J := X ⊔ (T : Subgroup G)
  let N := (T : Subgroup G) ⊓ normalizer P
  have hPJ : P ≤ J := (le_sup_right.trans h.complement.le).trans le_sup_left
  have hNJ : N ≤ J := inf_le_left.trans le_sup_right
  let q : J →* WreathModel.W := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let f := q.comp (inclusion hNJ)
  let a := P.normalizerMonoidHom.comp (inclusion (show N ≤ normalizer P from inf_le_right))
  let r := q.comp (inclusion hPJ)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply eq_bot_iff.mpr
    intro p hp
    have hm : inclusion hPJ p ∈ pCore 2 J := hqk ▸ hp
    have hd : Disjoint (J.pCoreIn 2) P :=
      (isPGroup_pCoreIn 2 J).disjoint_of_coprime h.odd_complement.isPGroup (by decide)
    exact Subtype.ext (hd.le_bot ⟨mem_map_of_mem J.subtype hm, p.property⟩)
  have hpc : Nat.card P = 9 := by
    rw [Nat.card_congr eP.toEquiv]
    norm_num [Plane, Nat.card_fun]
  have hpow (p : P) : p ^ 3 = 1 := by
    apply eP.injective
    rw [map_pow, map_one]
    exact (by decide +kernel : ∀ x : Plane 3, x ^ 3 = 1) (eP p)
  have hrC : r.range = WreathModel.cubicBase := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨p,rfl⟩
      rw [WreathModel.mem_cubicBase_iff, ← map_pow, hpow, map_one]
    · rw [WreathModel.cubicBase_card, ← Nat.card_congr (MonoidHom.ofInjective hr).toEquiv, hpc]
  have htwo : IsPGroup 2 f.range :=
    (h.two_group.to_le inf_le_left).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hd : Disjoint f.range WreathModel.cubicBase :=
    htwo.disjoint_of_coprime WreathModel.cubicBase_isPGroup (by decide)
  have he (n : N) (p : P) : r (a n p) = f n * r p * (f n)⁻¹ := by
    change q (inclusion hPJ (a n p)) =
      q (inclusion hNJ n) * q (inclusion hPJ p) * (q (inclusion hNJ n))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hk : a.ker = f.ker := by
    ext n
    change a n = 1 ↔ f n = 1
    constructor
    · intro hn
      have hc : f n ∈ centralizer (r.range : Set WreathModel.W) := by
        apply mem_centralizer_iff.mpr
        rintro _ ⟨p,rfl⟩
        have hh := he n p
        rw [hn] at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
      rw [hrC] at hc
      exact hd.le_bot ⟨⟨n,rfl⟩,WreathModel.centralizer_cubicBase_le hc⟩
    · intro hn
      apply MulEquiv.ext
      intro p
      apply hr
      change r (a n p) = r p
      simpa only [hn, one_mul, inv_one, mul_one] using he n p
  have hcoreT : X.pCoreIn 2 ≤ (T : Subgroup G) := le_sup_left.trans h.normalizer_factor.ge
  have hcoreJ : X.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer h.invariant)
  have hcore : ((X.pCoreIn 2).subgroupOf J).map q = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨x,hx,rfl⟩
    apply MonoidHom.mem_ker.mp
    rw [hqk]
    exact (mem_map_iff_mem J.subtype_injective).mp (hcoreJ hx)
  have hgen : (X.pCoreIn 2).subgroupOf J ⊔ N.subgroupOf J = (T : Subgroup G).subgroupOf J := by
    rw [← subgroupOf_sup (hcoreT.trans le_sup_right) hNJ, ← h.normalizer_factor]
  have hf : f.range = ((T : Subgroup G).subgroupOf J).map q := by
    have hh := congrArg (fun A : Subgroup J => A.map q) hgen
    rw [Subgroup.map_sup, hcore, bot_sup_eq] at hh
    simpa only [f, MonoidHom.range_comp, inclusion_range] using hh
  let S := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).mapSurjective hqs
  have hS : f.range = (S : Subgroup WreathModel.W) := hf
  obtain ⟨d⟩ := WreathModel.sylow_equiv_dihedral S
  exact ⟨((QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivRange f))).trans
        ((MulEquiv.subgroupCongr hS).trans d)⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant
