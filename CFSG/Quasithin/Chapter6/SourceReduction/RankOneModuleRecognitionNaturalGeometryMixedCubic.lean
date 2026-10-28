module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMixedCore
public import Theory.GroupAction.SubgroupPerfectFixedCover

/-!
# Cubic fixed-point lifting in the original mixed amalgam

The original cubic normalizes the right S3 factor and its Sylow intersection.
Every automorphism of S3 is inner, and a cubic preserving its self-normalizing
Sylow two-subgroup is trivial. Thus the original cubic acts trivially on the
specified two-core quotient. Coprime lifting makes its actual centralizer
cover that quotient; the full two-core preserves the natural seed, so these
fixed representatives generate exactly the original right conjugate span.

On the abelian branch, the cubic norm vanishes on the natural layer and on
all its conjugates by fixed representatives. Hence the cubic is fixed-free
on the entire enlarged span, and its commutator with the span is the span.
The orbit congruence gives order one modulo three. Since the elementary
span strictly enlarges the order-sixteen natural layer, its order and the
right core's order are at least 64. The marked right quotient then forces
Sylow order at least 128, or at least 256 in the S3 by S3 case.

The final application retains the same escaping subgroup, full overlap,
quotient markings, core geometry and unitary exclusions. Whole mixed
recognition, S5 parabolic escape, initial 6.1.4–5, omega escape and the
remaining geometry through unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.1–12
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace NaturalMixedCubic
local notation "S3" => Equiv.Perm (Fin 3)

private theorem three_center : center S3 = ⊥ := by
  apply bot_unique
  intro x hx
  exact NormalSymmetricThreePairRank.symmetricThree_center_trivial x (mem_center_iff.mp hx)

private theorem three_sylow_normalizer (S : Sylow 2 S3) :
    normalizer (S : Set S3) = S := by
  have hc : pCore 2 S3 = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
      Function.surjective_id (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
    exact hh.symm.trans MonoidHom.ker_id
  exact SymmetricThreeTwoCore.sylow_self_normalizing
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot) S

private theorem cubic_sylow_action (S : Sylow 2 S3) (b : MulAut S3)
    (hb : b^3=1) (hS : (S : Subgroup S3).map b.toMonoidHom = S) : b=1 := by
  obtain ⟨s,hs₀⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner b
  have hs := hs₀.symm
  have hn : s ∈ normalizer (S : Set S3) :=
    mem_normalizer_iff_map_conj_eq.mpr (hs ▸ hS)
  have hm : s ∈ (S : Subgroup S3) :=
    three_sylow_normalizer S ▸ hn
  have hpow : s^3=1 := MulAut.conj_injective_of_center_eq_bot
    three_center (by rw [map_pow,hs,hb,map_one])
  obtain ⟨k,hk⟩ := S.isPGroup' ⟨s,hm⟩
  have htwo : s^(2^k)=1 := congrArg Subtype.val hk
  have he : s=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime (2^k) 3 from (by decide : Nat.Coprime 2 3).pow_left k)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hpow))
  rw [he,map_one] at hs
  exact hs.symm

private theorem quotient_cubic_sylow_action {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (e : (A ⧸ pCore 2 A) ≃* S3)
    (a : MulAut A) (ha : a^3=1)
    (hS : (S : Subgroup A).map a.toMonoidHom = S) :
    (pCore 2 A).quotientAut a = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let b := (MulAut.congr e) ((pCore 2 A).quotientAut a)
  have hb : b^3=1 := by
    dsimp only [b]
    rw [←map_pow,←map_pow,ha,map_one,map_one]
  have he (x : A) : b (q x) = q (a x) := by
    simp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
      MulEquiv.trans_apply,e.symm_apply_apply,quotientAut_apply_mk]
  have hehom : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext he
  have hSb : ((S.mapSurjective hq : Sylow 2 S3) : Subgroup S3).map b.toMonoidHom =
      (S.mapSurjective hq : Subgroup S3) := by
    change ((S : Subgroup A).map q).map b.toMonoidHom = (S : Subgroup A).map q
    rw [map_map,hehom,←map_map,hS]
  have hone := cubic_sylow_action (S.mapSurjective hq) b hb hSb
  exact (MulAut.congr e).injective (hone.trans (map_one (MulAut.congr e)).symm)

end NaturalMixedCubic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The source cubic acts trivially on the original S3 two-core quotient. -/
theorem natural_mixed_cubic_quotient_trivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K : Subgroup G)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) (hcK : c ∈ normalizer (K : Set G)) :
    ⁅K,zpowers c⁆ ≤ K.pCoreIn 2 := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let a := K.normalizerMonoidHom ⟨c,hcK⟩
  have ha : a^3=1 := by
    rw [←map_pow]
    have hp : (⟨c,hcK⟩ : normalizer (K : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hp,map_one]
  have hcS : c ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    have hh : (T : Subgroup G) ⊓ K =
        ((T : Subgroup G) ⊓ Escape.I (T : Subgroup G) L R) ⊓ K := by
      rw [inf_assoc,inf_eq_right.mpr hKI]
    rw [hh]
    exact inf_normalizer_le_normalizer_inf
      ⟨natural_cubic_normalizes_line_sylow h hnat hcL hcN,hcK⟩
  have hSa : (S : Subgroup K).map a.toMonoidHom = S := by
    apply map_injective K.subtype_injective
    have he : K.subtype.comp a.toMonoidHom = (MulAut.conj c).toMonoidHom.comp K.subtype := by
      ext x
      rfl
    rw [map_map,he,←map_map,hS,subgroupOf_map_subtype]
    exact mem_normalizer_iff_map_conj_eq.mp hcS
  have hq := NaturalMixedCubic.quotient_cubic_sylow_action S e a ha hSa
  have hcQ : ∀ k : K, QuotientGroup.mk' (pCore 2 K) (a k) =
      QuotientGroup.mk' (pCore 2 K) k := by
    intro k
    rw [←quotientAut_apply_mk,hq]
    rfl
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx y hy
  have hQZ := normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hcpre : c ∈ commutatorPreimage (normalizer (K : Set G)) K (K.pCoreIn 2) := by
    apply (mem_commutatorPreimage_iff _ _ _ hQZ c).mpr
    refine ⟨hcK,?_⟩
    intro k hk
    have hh := QuotientGroup.eq_iff_div_mem.mp (hcQ ⟨k,hk⟩)
    have hh' := mem_map_of_mem K.subtype hh
    change c*k*c⁻¹/k ∈ (pCore 2 K).map K.subtype at hh'
    change c*k*c⁻¹*k⁻¹ ∈ (pCore 2 K).map K.subtype
    simpa only [div_eq_mul_inv] using hh'
  have hxpre := zpowers_le.mpr hcpre hx
  exact ((mem_commutatorPreimage_iff _ _ _ hQZ x).mp hxpre).2 y hy

/-- Fixed-point lifting on the literal two-core makes C_K(c) cover the
same specified S3 section. -/
theorem natural_mixed_cubic_fixed_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K : Subgroup G)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) (hcK : c ∈ normalizer (K : Set G)) :
    Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left))) := by
  have hm := natural_mixed_cubic_quotient_trivial h hnat K hKI hTK e hcL hcN hc3 hcK
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hs : Group.IsSolvable (pCore 2 K) := inferInstance
  have hc : Nat.Coprime (Nat.card (zpowers c)) (Nat.card (pCore 2 K)) := by
    rw [Nat.card_zpowers,hc3]
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hj]
    exact (by decide : Nat.Coprime 3 2).pow_right j
  exact e.surjective.comp (centralizer_quotient_surjective_of_solvable_coprime K
    (zpowers c) (pCore 2 K) (zpowers_le.mpr (hcK)) hs hc hm)


private theorem mixed_core_le_sylow (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) : K.pCoreIn 2 ≤ T := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hh := pCoreIn_le_sylow K S
  rw [hS,subgroupOf_map_subtype] at hh
  exact hh.trans inf_le_left

omit [Finite G] in
private theorem mixed_fixed_representative (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) (c : G)
    (hf : Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left))))
    (k : K) : ∃ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G),
      e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left d)) =
        e (QuotientGroup.mk' (pCore 2 K) k) ∧
      (d : G)⁻¹ * (k : G) ∈ K.pCoreIn 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  obtain ⟨d,hd⟩ := hf (q k)
  refine ⟨d,hd,?_⟩
  have hk : (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left) d)⁻¹ * k ∈
      pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change q (_⁻¹*k)=e 1
    rw [map_one,map_mul,map_inv]
    change (q (inclusion inf_le_left d))⁻¹ * q k=1
    rw [show q (inclusion inf_le_left d)=q k from hd,inv_mul_cancel]
  exact mem_map_of_mem K.subtype hk

/-- The cubic-fixed representatives generate exactly the full cover's
conjugate span of the original natural layer. -/
theorem natural_mixed_fixed_span_eq
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) (hcK : c ∈ normalizer (K : Set G)) :
    conjugateSpanBy (layer L R) (K ⊓ centralizer (zpowers c : Set G)) =
      conjugateSpanBy (layer L R) K := by
  have hf := natural_mixed_cubic_fixed_cover h hnat K hKI hTK e hcL hcN hc3 hcK
  have hQV := (mixed_core_le_sylow K hTK).trans
    h.sylow_normalizes_layer
  apply le_antisymm (conjugateSpanBy_mono le_rfl inf_le_left)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  obtain ⟨d,_,hd⟩ := mixed_fixed_representative K e c hf k
  rintro _ ⟨x,hx,rfl⟩
  have hxq := (mem_normalizer_iff.mp (hQV hd) x).mp hx
  have hh := (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy (layer L R)
    (K ⊓ centralizer (zpowers c : Set G)) d.property) _).mp (le_conjugateSpanBy _ _ hxq)
  convert hh using 1
  dsimp
  group

private theorem cubic_fixed_span
    {G : Type*} [Group G] (V C : Subgroup G) (c : G)
    (hcV : c ∈ normalizer (V : Set G)) (hc3 : c^3=1)
    (hCc : C ≤ centralizer (zpowers c : Set G))
    (hfree : ∀ v ∈ V, c*v*c⁻¹=v → v=1)
    [IsElementaryAbelian 2 (conjugateSpanBy V C)] :
    conjugateSpanBy V C ⊓ centralizer (zpowers c : Set G) = ⊥ := by
  let S := conjugateSpanBy V C
  let : CommGroup S := IsMulCommutative.instCommGroup
  have hcC : c ∈ normalizer (C : Set G) := by
    apply Subgroup.centralizer_le_normalizer (C : Set G)
    intro x hx
    exact (hCc hx c (mem_zpowers c)).symm
  have hcS : c ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp hcV,
      mem_normalizer_iff_map_conj_eq.mp hcC]
  let a := S.normalizerMonoidHom ⟨c,hcS⟩
  have ha3 : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hcS⟩ : normalizer (S : Set G))^3=1 := Subtype.ext hc3
    rw [hh,map_one]
  have haaa (x : S) : a (a (a x))=x := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha3 x
  let f : S →* S := {
    toFun x := x * a x * a (a x)
    map_one' := by simp
    map_mul' x y := by simp only [map_mul]; ac_rfl }
  have hfix (x : S) : a (f x)=f x := by
    change a (x*a x*a (a x))=x*a x*a (a x)
    rw [map_mul,map_mul,haaa]
    ac_rfl
  have hvnorm (v : G) (hv : v ∈ V) :
      f ⟨v,le_conjugateSpanBy V C hv⟩=1 := by
    apply Subtype.ext
    apply hfree
    · exact V.mul_mem (V.mul_mem hv ((mem_normalizer_iff.mp hcV v).mp hv))
        ((mem_normalizer_iff.mp hcV _).mp ((mem_normalizer_iff.mp hcV v).mp hv))
    · exact congrArg Subtype.val (hfix ⟨v,le_conjugateSpanBy V C hv⟩)
  have hle : S ≤ f.ker.map S.subtype := by
    apply (closure_le _).mpr
    rintro _ ⟨d,hd,v,hv,rfl⟩
    let b := S.normalizerMonoidHom ⟨d,le_normalizer_conjugateSpanBy V C hd⟩
    have hcd : c*d=d*c := hCc hd c (mem_zpowers c)
    have hab (x : S) : a (b x)=b (a x) := by
      apply Subtype.ext
      change c*(d*(x : G)*d⁻¹)*c⁻¹=d*(c*(x : G)*c⁻¹)*d⁻¹
      calc
        _ = (c*d)*(x : G)*(c*d)⁻¹ := by group
        _ = (d*c)*(x : G)*(d*c)⁻¹ := by rw [hcd]
        _ = _ := by group
    have hfb (x : S) : f (b x)=b (f x) := by
      change b x*a (b x)*a (a (b x))=b (x*a x*a (a x))
      simp only [hab,map_mul]
    refine ⟨b ⟨v,le_conjugateSpanBy V C hv⟩,?_,rfl⟩
    change f (b ⟨v,le_conjugateSpanBy V C hv⟩)=1
    rw [hfb,hvnorm v hv,map_one]
  apply bot_unique
  intro x hx
  have hfx : f ⟨x,hx.1⟩=1 := by
    obtain ⟨y,hy,he⟩ := hle hx.1
    have hyx : y=⟨x,hx.1⟩ := Subtype.ext he
    exact hyx ▸ hy
  have hax : a ⟨x,hx.1⟩=⟨x,hx.1⟩ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 c (mem_zpowers c))
  have hx2 : (⟨x,hx.1⟩ : S)^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 S) _
  change (⟨x,hx.1⟩ : S)*a ⟨x,hx.1⟩*a (a ⟨x,hx.1⟩)=1 at hfx
  rw [hax,hax,←pow_two,hx2,one_mul] at hfx
  exact congrArg Subtype.val hfx

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The original cubic is fixed-free on the entire abelian natural-layer
span of the same S3 cover, not only on its seed and central line. -/
theorem natural_mixed_span_cubic_fixed_eq_bot
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) (hcK : c ∈ normalizer (K : Set G)) :
    conjugateSpanBy (layer L R) K ⊓ centralizer (zpowers c : Set G) = ⊥ := by
  let V := layer L R
  let S := conjugateSpanBy V K
  have hSU : S ≤ Escape.U (T : Subgroup G) L R := by
    have he : conjugateSpanBy V (Escape.I (T : Subgroup G) L R) =
        Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hKI
  let := h.layer_elementary
  let : IsMulCommutative S := le_centralizer_iff_isMulCommutative.mp
    (hSU.trans (hab.trans (centralizer_le hSU)))
  let : IsElementaryAbelian 2 S := conjugateSpanBy_elementary_of_commutative _ _
  have heq := natural_mixed_fixed_span_eq h hnat K hKI hTK e hcL hcN hc3 hcK
  let : IsElementaryAbelian 2
      (conjugateSpanBy V (K ⊓ centralizer (zpowers c : Set G))) := by
    change IsElementaryAbelian 2 (conjugateSpanBy (layer L R)
      (K ⊓ centralizer (zpowers c : Set G)))
    rw [heq]
    infer_instance
  rw [←heq]
  exact cubic_fixed_span V _ c (normalizer_commutator_ge_right R L hcL)
    (hc3 ▸ pow_orderOf_eq_one c) inf_le_right
    (fun _ hv hfix => hnat.cubic_fixed_eq_one hcL hc3 hv hfix)


private theorem fixed_free_cubic_card
    {G : Type*} [Group G] [Finite G] (U : Subgroup G) (c : G)
    (hcU : c ∈ normalizer (U : Set G)) (hc3 : c^3=1)
    (hfree : U ⊓ centralizer (zpowers c : Set G) = ⊥) :
    Nat.card U ≡ 1 [MOD 3] := by
  let a := U.normalizerMonoidHom ⟨c,hcU⟩
  have ha3 : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hcU⟩ : normalizer (U : Set G))^3=1 := Subtype.ext hc3
    rw [hh,map_one]
  let A := zpowers a
  have hp : IsPGroup 3 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one ha3)
  have hfix (x : MulAction.fixedPoints A U) : (x : U)=1 := by
    have hx : a (x : U)=(x : U) := x.property ⟨a,mem_zpowers a⟩
    apply Subtype.ext
    apply mem_bot.mp
    apply (show U ⊓ centralizer (zpowers c : Set G) ≤ ⊥ from hfree.le)
    refine ⟨x.val.property,?_⟩
    have hh := congrArg Subtype.val hx
    change c*(x.val : G)*c⁻¹=(x.val : G) at hh
    intro y hy
    have hc : c ∈ centralizer ({(x.val : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
    exact mem_centralizer_singleton_iff.mp (zpowers_le.mpr hc hy)
  let : Subsingleton (MulAction.fixedPoints A U) :=
    ⟨fun x y => Subtype.ext ((hfix x).trans (hfix y).symm)⟩
  let : Nonempty (MulAction.fixedPoints A U) := ⟨⟨1,fun g => map_one g.val⟩⟩
  have hh := hp.card_modEq_card_fixedPoints U
  simpa only [Nat.card_unique] using hh


/-- The original source cubic fixes no nonidentity element of the enlarged
right span. The actual fixed subgroup of B covers its specified quotient
and generates exactly that span. -/
theorem natural_cubic_amalgam_right_cubic_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    {B : Subgroup G}
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    let U := conjugateSpanBy (layer L R) J
    ∃ c : G, c ∈ L ∧
      c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      c ∈ Escape.H (T : Subgroup G) L R ∧ orderOf c=3 ∧
      c ∈ normalizer (B : Set G) ∧
      ⁅B,zpowers c⁆ ≤ B.pCoreIn 2 ∧
      Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))).comp
        (inclusion (show B ⊓ centralizer (zpowers c : Set G) ≤ B from inf_le_left))) ∧
      conjugateSpanBy (layer L R) (B ⊓ centralizer (zpowers c : Set G)) = U ∧
      U ⊓ centralizer (zpowers c : Set G) = ⊥ ∧ ⁅U,zpowers c⁆ = U ∧
      Nat.card U ≡ 1 [MOD 3] := by
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  have hcB : c ∈ normalizer (B : Set G) := hF.cross 1 ⟨hcL,hcTL⟩
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := hF.S_normalizes 1
  have heq := natural_cubic_amalgam_right_span_eq h hF e
  have hfixed := natural_mixed_span_cubic_fixed_eq_bot h hnat B hBI hTB e hab hcL hcN hc3 hcB
  have hcU : c ∈ normalizer (conjugateSpanBy (layer L R) B : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hcL),
      mem_normalizer_iff_map_conj_eq.mp hcB]
  have hcomm : ⁅conjugateSpanBy (layer L R) B,zpowers c⁆ =
      conjugateSpanBy (layer L R) B := by
    apply commutator_eq_of_fixedPointFree _ _ (zpowers_le.mpr hcU) c (mem_zpowers c)
    intro v hv hcv
    apply mem_bot.mp
    rw [←hfixed]
    refine ⟨hv,?_⟩
    intro x hx
    obtain ⟨m,rfl⟩ := hx
    exact hcv.zpow_left m
  refine ⟨c,hcL,hcTL,hcN,hc3,hcB,
    natural_mixed_cubic_quotient_trivial h hnat B hBI hTB e hcL hcN hc3 hcB,
    natural_mixed_cubic_fixed_cover h hnat B hBI hTB e hcL hcN hc3 hcB,?_,?_,?_,?_⟩
  · rw [heq]
    exact natural_mixed_fixed_span_eq h hnat B hBI hTB e hcL hcN hc3 hcB
  · simpa only [heq] using hfixed
  · simpa only [heq] using hcomm
  · rw [heq]
    exact fixed_free_cubic_card _ c hcU (hc3 ▸ pow_orderOf_eq_one c) hfixed

/-- The cubic orbit congruence rules out order 32 for the elementary right
span. The full right two-core has order at least 64, and the actual Sylow
has order at least 128 (at least 256 in the S3 by S3 quotient case). -/
theorem natural_cubic_amalgam_right_cubic_sizes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    {B : Subgroup G}
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hr : NaturalCubicRightQuotientData T L R B e)
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    let U := conjugateSpanBy (layer L R) J
    64 ≤ Nat.card U ∧ 64 ≤ Nat.card (pCore 2 J) ∧ 128 ≤ Nat.card T ∧
      (Nat.card T = 4 * Nat.card (pCore 2 J) → 256 ≤ Nat.card T) := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  obtain ⟨_,hUE,h32,_,_⟩ :=
    natural_cubic_amalgam_right_elementary_span h hnat hF e hr hBI hab
  let := hUE
  obtain ⟨c,_,_,_,_,_,_,_,_,_,_,hc⟩ :=
    natural_cubic_amalgam_right_cubic_geometry h hnat hF e hBI hab
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2^5 ≤ 2^k from hk ▸ h32)
  have hk6 : 6 ≤ k := by
    have hn : k ≠ 5 := by
      intro he
      change Nat.card U ≡ 1 [MOD 3] at hc
      rw [hk,he] at hc
      norm_num [Nat.ModEq] at hc
    omega
  have h64 : 64 ≤ Nat.card U := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk6
  have hQ64 : 64 ≤ Nat.card (pCore 2 J) := by
    have hUQ := (natural_cubic_amalgam_right_span h hnat hF e hr).2.1
    have hh := card_le_of_le hUQ
    change Nat.card U ≤ Nat.card ((pCore 2 J).map J.subtype) at hh
    rw [card_map_of_injective J.subtype_injective] at hh
    exact h64.trans hh
  refine ⟨h64,hQ64,?_,?_⟩
  swap
  · change Nat.card T = 4 * Nat.card (pCore 2 J) → 256 ≤ Nat.card T
    omega
  rcases natural_cubic_amalgam_right_models_and_sizes hnat hF e hr with hh | hh
  · have he := hh.2
    change Nat.card T = 2 * Nat.card (pCore 2 J) at he
    omega
  · have he := hh.2
    change Nat.card T = 4 * Nat.card (pCore 2 J) at he
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- Cubic fixed-point lifting and fixed-free action on the literal right
span, together with the resulting bounds for the full right core and T. -/
@[expose] def NaturalCubicRightCubicData (T : Sylow 2 G) (L R B : Subgroup G)
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) : Prop :=
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  (∃ c : G, c ∈ L ∧
    c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    c ∈ Escape.H (T : Subgroup G) L R ∧ orderOf c=3 ∧
    c ∈ normalizer (B : Set G) ∧
    ⁅B,zpowers c⁆ ≤ B.pCoreIn 2 ∧
    Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))).comp
      (inclusion (show B ⊓ centralizer (zpowers c : Set G) ≤ B from inf_le_left))) ∧
    conjugateSpanBy (layer L R) (B ⊓ centralizer (zpowers c : Set G)) = U ∧
    U ⊓ centralizer (zpowers c : Set G) = ⊥ ∧ ⁅U,zpowers c⁆ = U ∧
    Nat.card U ≡ 1 [MOD 3]) ∧
    64 ≤ Nat.card U ∧ 64 ≤ Nat.card (pCore 2 J) ∧ 128 ≤ Nat.card T ∧
      (Nat.card T = 4 * Nat.card (pCore 2 J) → 256 ≤ Nat.card T)

/-- The escaping pair retains its original markings and right-core geometry,
with cubic fixed-point lifting and the sharper core and Sylow bounds. -/
@[expose] def NaturalEscapingAmalgamCubicData (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ P ⊔ N.pCoreIn 2 ∧
    B ≤ Escape.I (T : Subgroup G) L R ∧ (¬ B ≤ M) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
    ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G) ∧
    Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) i).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G)))
      ((ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G))) ∧ NaturalUnitaryAmalgamExclusion T L B ∧
    ∀ e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3),
      NaturalCubicRightQuotientData T L R B e ∧
      NaturalCubicRightCoreData T L R B ∧
      NaturalCubicRightCubicData T L R B e ∧
      let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 3)) ∧
        Nat.card T = 2 * Nat.card (pCore 2 J)) ∨
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
        Nat.card T = 4 * Nat.card (pCore 2 J))

variable [Finite G] {T : Sylow 2 G} {L M R P N : Subgroup G}

/-- The same escaping pair has a cubic acting fixed-freely on its enlarged
natural span. No covering kernel, original marking or core constraint is lost. -/
theorem natural_escaping_amalgam_right_cubic
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    (d : NaturalEscapingAmalgamCoreData T L R P N M) :
    NaturalEscapingAmalgamCubicData T L R P N M := by
  obtain ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,hright⟩ := d
  refine ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,fun e => ?_⟩
  obtain ⟨hr,hcore,hmodels⟩ := hright e
  exact ⟨hr,hcore,⟨natural_cubic_amalgam_right_cubic_geometry h hnat hF e hBI hab,
    natural_cubic_amalgam_right_cubic_sizes h hnat hF e hr hBI hab⟩,hmodels⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
