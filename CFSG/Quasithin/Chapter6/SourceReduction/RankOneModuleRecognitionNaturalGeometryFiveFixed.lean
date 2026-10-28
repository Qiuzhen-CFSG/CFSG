module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveGeneration
public import Theory.SpecificGroups.Symmetric.InnerAutomorphisms
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
public import Theory.GroupAction.SubgroupPerfectFixedCover

/-!
# The source cubic on the original S5 quotient and fixed two-core

The cubic in N_L(Z_S) preserves C_T(Z_S), hence the Sylow intersection
T ∩ K of the original invariant cover. Every automorphism of S5 is inner,
and its Sylow two-subgroup is self-normalizing, so a cubic preserving that
Sylow acts trivially. This proves [K,c] ≤ O2(K) with the literal quotient.

Coprime fixed-point lifting then makes C_K(c) surject onto every specified
S5 marking of K/O2(K). If C_{O2(K)}(c) were trivial, this restriction would
be an isomorphism and would lift an elementary even plane, contradicting
generation one on KT. Thus the contained S5 branch has a nontrivial fixed
two-core. Cauchy's theorem supplies an actual fixed involution outside
Z_S, on which the original cubic is fixed-free.

The final application retains the same W/Z_S action, original cover,
parabolics and generation hypothesis. This constrains the remaining S5
branch; it does not eliminate it or assume fixed-core vanishing. S5 escape,
mixed-amalgam recognition, initial 6.1.4–5, omega escape and unconditional
6.1.27 remain with qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`),
using the original cubic and E.1.1–6 generation convention, pp.209–211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixed
local notation "S5" => Equiv.Perm (Fin 5)

private theorem cubic_sylow_action (S : Sylow 2 S5) (b : MulAut S5)
    (hb : b^3=1) (hS : (S : Subgroup S5).map b.toMonoidHom = S) : b=1 := by
  obtain ⟨s,hs⟩ := Equiv.Perm.conj_surjective_of_degree (by decide : 5 ≤ 5) (by decide) b
  have hn : s ∈ normalizer (S : Set S5) :=
    mem_normalizer_iff_map_conj_eq.mpr (hs ▸ hS)
  have hm : s ∈ (S : Subgroup S5) :=
    Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self S ▸ hn
  have hpow : s^3=1 := MulAut.conj_injective_of_center_eq_bot
    Theory.SpecificGroups.SymmetricFive.center_eq_bot (by rw [map_pow,hs,hb,map_one])
  obtain ⟨k,hk⟩ := S.isPGroup' ⟨s,hm⟩
  have htwo : s^(2^k)=1 := congrArg Subtype.val hk
  have he : s=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime (2^k) 3 from (by decide : Nat.Coprime 2 3).pow_left k)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hpow))
  rw [he,map_one] at hs
  exact hs.symm

private theorem quotient_cubic_sylow_action {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (e : (A ⧸ pCore 2 A) ≃* S5)
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
  have hSb : ((S.mapSurjective hq : Sylow 2 S5) : Subgroup S5).map b.toMonoidHom =
      (S.mapSurjective hq : Subgroup S5) := by
    change ((S : Subgroup A).map q).map b.toMonoidHom = (S : Subgroup A).map q
    rw [map_map,hehom,←map_map,hS]
  have hone := cubic_sylow_action (S.mapSurjective hq) b hb hSb
  exact (MulAut.congr e).injective (hone.trans (map_one (MulAut.congr e)).symm)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixed

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The source cubic acts trivially on the original S5 two-core quotient. -/
theorem natural_five_cubic_quotient_trivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K : Subgroup G)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    ⁅K,zpowers c⁆ ≤ K.pCoreIn 2 := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := h.sylow_normalizes_ZS.trans hNK
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
  have ha : a^3=1 := by
    rw [←map_pow]
    have hp : (⟨c,hNK hcN⟩ : normalizer (K : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hp,map_one]
  have hcS : c ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    have hh : (T : Subgroup G) ⊓ K =
        ((T : Subgroup G) ⊓ Escape.I (T : Subgroup G) L R) ⊓ K := by
      rw [inf_assoc,inf_eq_right.mpr hKI]
    rw [hh]
    exact inf_normalizer_le_normalizer_inf
      ⟨natural_cubic_normalizes_line_sylow h hnat hcL hcN,hNK hcN⟩
  have hSa : (S : Subgroup K).map a.toMonoidHom = S := by
    apply map_injective K.subtype_injective
    have he : K.subtype.comp a.toMonoidHom = (MulAut.conj c).toMonoidHom.comp K.subtype := by
      ext x
      rfl
    rw [map_map,he,←map_map,hS,subgroupOf_map_subtype]
    exact mem_normalizer_iff_map_conj_eq.mp hcS
  have hq := NaturalFiveFixed.quotient_cubic_sylow_action S e a ha hSa
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
    refine ⟨hNK hcN,?_⟩
    intro k hk
    have hh := QuotientGroup.eq_iff_div_mem.mp (hcQ ⟨k,hk⟩)
    have hh' := mem_map_of_mem K.subtype hh
    change c*k*c⁻¹/k ∈ (pCore 2 K).map K.subtype at hh'
    change c*k*c⁻¹*k⁻¹ ∈ (pCore 2 K).map K.subtype
    simpa only [div_eq_mul_inv] using hh'
  have hxpre := zpowers_le.mpr hcpre hx
  exact ((mem_commutatorPreimage_iff _ _ _ hQZ x).mp hxpre).2 y hy

/-- Fixed-point lifting on the literal two-core makes C_K(c) cover the
same specified S5 section. -/
theorem natural_five_cubic_fixed_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K : Subgroup G)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left))) := by
  have hm := natural_five_cubic_quotient_trivial h hnat K hKI hNK e hcL hcN hc3
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hs : Group.IsSolvable (pCore 2 K) := inferInstance
  have hc : Nat.Coprime (Nat.card (zpowers c)) (Nat.card (pCore 2 K)) := by
    rw [Nat.card_zpowers,hc3]
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hj]
    exact (by decide : Nat.Coprime 3 2).pow_right j
  exact e.surjective.comp (centralizer_quotient_surjective_of_solvable_coprime K
    (zpowers c) (pCore 2 K) (zpowers_le.mpr (hNK hcN)) hs hc hm)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixed
local notation "S5" => Equiv.Perm (Fin 5)
private def word : Fin 4 → S5 :=
  ![1,Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,Equiv.swap 0 3 * Equiv.swap 1 2]
private def evenFour : Subgroup S5 where
  carrier := Set.range word
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := h i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    have h : ∀ i, (word i)⁻¹=word i := by decide +kernel
    rintro x ⟨i,rfl⟩
    exact ⟨i,(h i).symm⟩
private instance evenFour_elementary : IsElementaryAbelian 2 evenFour where
  is_comm.comm x y := by
    have h : ∀ i j, word i * word j = word j * word i := by decide +kernel
    apply Subtype.ext
    obtain ⟨i,hi⟩ := x.property
    obtain ⟨j,hj⟩ := y.property
    change (x : S5) * y = (y : S5) * x
    rw [←hi,←hj]
    exact h i j
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    have h : ∀ i, (word i)^2=1 := by decide +kernel
    intro x
    apply Subtype.ext
    obtain ⟨i,hi⟩ := x.property
    change (x : S5)^2=1
    rw [←hi]
    exact h i
private theorem evenFour_card : Nat.card evenFour = 4 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word)=4
  rw [←Nat.card_congr (Equiv.ofInjective word hi)]
  simp
private theorem evenFour_even : evenFour ≤ alternatingGroup (Fin 5) := by
  have h : ∀ i, (word i).sign=1 := by decide +kernel
  rintro x ⟨i,rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr (h i)

private theorem fixed_core_ne_bot
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : ChapterE.generationParameter (K ⊔ (T : Subgroup G) : Subgroup G)=1)
    (e : (K ⧸ pCore 2 K) ≃* S5) (c : G)
    (hf : Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left)))) :
    K.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≠ ⊥ := by
  intro hzero
  let C := K ⊓ centralizer (zpowers c : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := q.comp (inclusion (show C ≤ K from inf_le_left))
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hk : inclusion (show C ≤ K from inf_le_left) x ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.injective
      exact hx.trans e.map_one.symm
    have hx0 : (x : G) ∈ K.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) :=
      ⟨mem_map_of_mem K.subtype hk,x.property.2⟩
    rw [hzero,mem_bot] at hx0
    exact mem_bot.mpr (Subtype.ext hx0)
  let b := MulEquiv.ofBijective f ⟨hi,hf⟩
  let u : S5 →* K := (inclusion (show C ≤ K from inf_le_left)).comp b.symm.toMonoidHom
  let A := evenFour.map u
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map u
  have hqu : q.comp u = MonoidHom.id S5 := by
    apply MonoidHom.ext
    intro x
    exact b.apply_symm_apply x
  have hA : A.map q = evenFour := by
    rw [map_map,hqu,map_id]
  exact natural_five_no_even_plane_of_generation_one T K hTK hgen e A
    (hA ▸ evenFour_even) (hA ▸ evenFour_card)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixed

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- In the contained branch, the actual source cubic has a nontrivial
fixed subgroup in the two-core. If it vanished, its full S5 centralizer
would supply the forbidden elementary even plane. -/
theorem natural_five_cubic_fixed_core_nontrivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K : Subgroup G)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hgen : ChapterE.generationParameter (K ⊔ (T : Subgroup G) : Subgroup G)=1)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    K.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≠ ⊥ :=
  NaturalFiveFixed.fixed_core_ne_bot T K (h.sylow_normalizes_ZS.trans hNK) hgen e c
    (natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3)

/-- The fixed-point obstruction on the original cover: the cubic moves
every nonidentity point of Z_S, yet fixes a nonidentity point in O2(N),
and its literal centralizer covers every marking of K/O2(K) by S5. -/
@[expose] def NaturalFiveCubicFixedData
    (T : Sylow 2 G) (L R P N : Subgroup G) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  ∃ c ∈ L,
    c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    c ∈ N ∧ orderOf c=3 ∧
    (∀ z ∈ ZS (T : Subgroup G) L R, c*z*c⁻¹=z → z=1) ∧
    ⁅K,zpowers c⁆ ≤ N.pCoreIn 2 ∧
    N.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≠ ⊥ ∧
    ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
      Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
        (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left)))

/-- Apply the cubic fixed-point calculation to the same invariant S5
cover and its actual H-star generation assumption. -/
theorem natural_five_contained_cubic_fixed_data
    {X : Type*} [Group X]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (P : Subgroup G) (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : P ≤ Escape.I (T : Subgroup G) L R)
    (hc : NaturalInvariantCoverData T P (Escape.I (T : Subgroup G) L R)
      (Escape.H (T : Subgroup G) L R) σ hPI)
    (hd : NaturalFiveContainedParabolicData T P (Escape.H (T : Subgroup G) L R) M) :
    NaturalFiveCubicFixedData T L R P (Escape.H (T : Subgroup G) L R) := by
  obtain ⟨hKI,hNK,hTK,hcore,⟨eK⟩,_⟩ := hc
  obtain ⟨⟨eP⟩,B,_,_,_,_,_,_,hgen⟩ := hd
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  refine ⟨c,hcL,hcTL,hcN,hc3,hcf,?_,?_,?_⟩
  · exact (natural_five_cubic_quotient_trivial h hnat _ hKI hNK
      (eK.trans eP) hcL hcN hc3).trans hcore.le
  · intro hz
    apply natural_five_cubic_fixed_core_nontrivial h hnat _ hKI hNK hgen (eK.trans eP) hcL hcN hc3
    exact (congrArg (fun Q => Q ⊓ centralizer (zpowers c : Set G)) hcore).trans hz
  · intro e
    exact natural_five_cubic_fixed_cover h hnat _ hKI hNK e hcL hcN hc3
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

/-- The obstruction is an actual involution of the original two-core,
fixed by the cubic and lying outside its fixed-free central line. -/
private theorem natural_five_fixed_core_involution
    (Q Z : Subgroup G) (hQ : IsPGroup 2 Q) (c : G)
    (hne : Q ⊓ centralizer (zpowers c : Set G) ≠ ⊥)
    (hfree : ∀ z ∈ Z, c*z*c⁻¹=z → z=1) :
    ∃ t ∈ Q, orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z := by
  let A := Q ⊓ centralizer (zpowers c : Set G)
  have hp : IsPGroup 2 A := hQ.to_le inf_le_left
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hd : 2 ∣ Nat.card A := (hp.dvd_orderOf hu).trans (orderOf_dvd_natCard u)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hd
  have ht2 : orderOf (t : G)=2 := (orderOf_coe t).trans ht
  have hc : c*(t : G)*c⁻¹=t :=
    mul_inv_eq_iff_eq_mul.mpr (t.property.2 c (mem_zpowers c))
  refine ⟨t,t.property.1,ht2,hc,?_⟩
  intro hz
  have ht1 := hfree t hz hc
  rw [ht1,orderOf_one] at ht2
  omega
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The same original W/Z_S witness gives an escaping F.1.1 pair or
an actual fixed-core obstruction in its contained S5 cover. In the latter
case the source cubic fixes an involution of O2(N) outside Z_S, and its
centralizer surjects under every S5 marking of the same K/O2(K). -/
theorem exists_ambient_amalgam_or_five_fixed_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L R P N ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z)) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_no_lift h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno⟩
  have hc := natural_five_contained_cubic_fixed_data (hn ▸ h) (hn ▸ hnat) _ σ hPI hcover hd
  refine ⟨hd,hno,hc,?_⟩
  obtain ⟨c,hcL,_,hcN,hc3,hfree,_,hfixed,_⟩ := hc
  obtain ⟨t,ht,ht2,hct,htZ⟩ := natural_five_fixed_core_involution _ _
    (isPGroup_pCoreIn 2 _) c hfixed hfree
  exact ⟨c,t,hcL,hcN,hc3,ht,ht2,hct,htZ⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
