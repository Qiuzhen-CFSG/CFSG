module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveCoreMovement
public import Theory.GroupAction.PrimeFixedQuotient

/-!
# Cubic orbit covers in the original S5 two-core

A core action commuting with the original cubic has a cubic-fixed
representative: orbit counting lifts it through the full two-group
kernel. The existing natural-layer calculation makes every such
representative centralize the whole span. Thus the cubic fixes no
nonidentity core action.

The core action is elementary, so each cubic norm acts trivially.
Starting with the actual core-moving involution, its three cubic
conjugates generate an invariant subgroup inside the original Sylow.
Their literal action image is an elementary four-group. Its kernel
is the full ambient centralizer of the span, and the norm is retained
in that kernel, rather than set equal to the identity upstairs.

The last theorem consumes the proved even-seed movement alternative.
Its Chapter12 application keeps the same W/Z_S witness and all quotient
markings. This does not establish an elementary ambient lift or S5
parabolic escape. Those steps, initial 6.1.4–5, the exact omega escape
and final 6.1.27 remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.17(4), 6.1.19, pp.672–675
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem fixed_core_action
    {G : Type*} [Group G] [Finite G]
    (Q S : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQS : Q ≤ normalizer (S : Set G))
    (c : G) (hc3 : orderOf c=3)
    (hcQ : c ∈ normalizer (Q : Set G))
    (hcS : c ∈ normalizer (S : Set G))
    (hfix : Q ⊓ centralizer (zpowers c : Set G) ≤ centralizer (S : Set G)) :
    let f := S.normalizerMonoidHom.comp (inclusion hQS)
    ∀ x : Q, Commute (f x) (S.normalizerMonoidHom ⟨c,hcS⟩) → f x=1 := by
  let A := zpowers c
  have hAQ : A ≤ normalizer (Q : Set G) := zpowers_le.mpr hcQ
  have hAS : A ≤ normalizer (S : Set G) := zpowers_le.mpr hcS
  let f := S.normalizerMonoidHom.comp (inclusion hQS)
  let b := S.normalizerMonoidHom.comp (inclusion hAS)
  let : MulDistribMulAction A Q := conjMulDistribMulActionOfLeNormalizer A Q hAQ
  let : MulDistribMulAction A (MulAut S) :=
    MulDistribMulAction.compHom _ (MulAut.conj.comp b)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hc3]; rfl)
  have hk : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨j,hj⟩ := (hQ.to_subgroup f.ker).exists_card_eq
    rw [hj]
    intro hd
    have hh := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at hh
  have heq (a : A) (x : Q) : f (a • x) = a • f x := by
    change f (a • x) = b a * f x * (b a)⁻¹
    rw [←b.map_inv]
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change ((a : G)*(x : G)*(a : G)⁻¹)*(s : G)*
      ((a : G)*(x : G)*(a : G)⁻¹)⁻¹ =
      (a : G)*((x : G)*((a : G)⁻¹*(s : G)*((a : G)⁻¹)⁻¹)*(x : G)⁻¹)*(a : G)⁻¹
    group
  change ∀ x : Q, Commute (f x) (S.normalizerMonoidHom ⟨c,hcS⟩) → f x=1
  intro x hx
  have hfixed : f x ∈ FixedPoints.subgroup A (MulAut S) := by
    intro a
    obtain ⟨m,hm⟩ := a.property
    have hb : b a = (S.normalizerMonoidHom ⟨c,hcS⟩)^m := by
      change S.normalizerMonoidHom (inclusion hAS a) = _
      rw [←map_zpow]
      congr 1
      exact Subtype.ext hm.symm
    change b a * f x * (b a)⁻¹ = f x
    rw [hb,(hx.symm.zpow_left m).eq,mul_inv_cancel_right]
  have hm := f.map_fixedPoints_eq_of_prime_coprime_kernel hA hk heq
  have hi : f x ∈ (FixedPoints.subgroup A Q).map f := by
    rw [hm]
    exact ⟨⟨x,rfl⟩,hfixed⟩
  obtain ⟨y,hy,hyx⟩ := hi
  have hyC : (y : G) ∈ centralizer (zpowers c : Set G) := by
    intro a ha
    have hh := congrArg Subtype.val (hy (⟨a,ha⟩ : A))
    change a*(y : G)*a⁻¹=y at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hcentral := hfix ⟨y.property,hyC⟩
  rw [←hyx]
  apply MulEquiv.ext
  intro s
  apply Subtype.ext
  change (y : G)*(s : G)*(y : G)⁻¹=s
  exact mul_inv_eq_iff_eq_mul.mpr (hcentral s s.property).symm

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

theorem natural_five_cubic_fixed_core_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    ∃ hcS : c ∈ normalizer (conjugateSpanBy (layer L R) K : Set G),
      ∀ k : K, k ∈ pCore 2 K →
        Commute (naturalFiveCoverAction L R K k)
          ((conjugateSpanBy (layer L R) K).normalizerMonoidHom ⟨c,hcS⟩) →
        naturalFiveCoverAction L R K k = 1 := by
  let S := conjugateSpanBy (layer L R) K
  let Q := K.pCoreIn 2
  have hcS : c ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hcL),
      mem_normalizer_iff_map_conj_eq.mp (hNK hcN)]
  have hcQ : c ∈ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K) (hNK hcN)
  have hQN : Q ≤ (Escape.H (T : Subgroup G) L R).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (hKI.trans (Subgroup.centralizer_le_normalizer _)) hNK
  have hf : Q ⊓ centralizer (zpowers c : Set G) ≤ centralizer (S : Set G) :=
    (inf_le_inf_right _ hQN).trans
      (natural_five_fixed_core_centralizes_span h hnat K hKI hNK e hcL hcN hc3)
  have hQS : Q ≤ normalizer (S : Set G) :=
    (pCoreIn_le 2 K).trans (le_normalizer_conjugateSpanBy _ _)
  refine ⟨hcS,?_⟩
  intro k hk hcomm
  exact fixed_core_action Q S (isPGroup_pCoreIn 2 K) hQS c hc3 hcQ hcS hf
    ⟨k,mem_map_of_mem K.subtype hk⟩ hcomm

private theorem card_involution_pair
    {X : Type*} [Group X] (x y : X) (hx : orderOf x=2) (hy : orderOf y=2)
    (hxy : Commute x y) (hne : x ≠ y) :
    Nat.card (zpowers x ⊔ zpowers y : Subgroup X)=4 := by
  classical
  have hout : y ∉ zpowers x := by
    intro hm
    have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hx ▸ pow_orderOf_eq_one x⟩
    rw [hfin.mem_zpowers_iff_mem_range_orderOf,hx] at hm
    obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hm
    have hi2 := Finset.mem_range.mp hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · have he : y=1 := by simpa using hix.symm
      rw [he,orderOf_one] at hy
      omega
    · exact hne (by simpa using hix)
  have hn : y ∈ normalizer (zpowers x : Set X) := by
    apply Subgroup.centralizer_le_normalizer
    intro z hz
    obtain ⟨m,rfl⟩ := hz
    exact (hxy.zpow_left m).eq
  rw [card_sup_zpowers_of_normalizing_involution (zpowers x) y
    (hy ▸ pow_orderOf_eq_one y) hout hn,Nat.card_zpowers,hx]

/-- The cubic norm of every original core element acts trivially on the
whole span. This is an identity modulo the full ambient action kernel. -/
theorem natural_five_core_cubic_norm
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
    ∀ k : K, k ∈ pCore 2 K →
      k*a k*a (a k) ∈ (naturalFiveCoverAction L R K).ker := by
  let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
  let S := conjugateSpanBy (layer L R) K
  let ρ := naturalFiveCoverAction L R K
  obtain ⟨hcS,hfixed⟩ := natural_five_cubic_fixed_core_action h hnat K hKI hNK e hcL hcN hc3
  let b := S.normalizerMonoidHom ⟨c,hcS⟩
  have ha : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hNK hcN⟩ : normalizer (K : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hh,map_one]
  have ha3 (k : K) : a (a (a k))=k := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha k
  have heq (k : K) : ρ (a k)=b*ρ k*b⁻¹ := by
    have hb : b⁻¹=S.normalizerMonoidHom ⟨c⁻¹,(normalizer (S : Set G)).inv_mem hcS⟩ := by
      rw [←map_inv]; rfl
    rw [hb]
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change (c*(k : G)*c⁻¹)*(s : G)*(c*(k : G)*c⁻¹)⁻¹ =
      c*((k : G)*(c⁻¹*(s : G)*(c⁻¹)⁻¹)*(k : G)⁻¹)*c⁻¹
    group
  have hqa (k : K) (hk : k ∈ pCore 2 K) : a k ∈ pCore 2 K :=
    (characteristic_iff_map_le.mp inferInstance a) (mem_map_of_mem a.toMonoidHom hk)
  let A := (pCore 2 K).map ρ
  let : IsElementaryAbelian 2 A :=
    (natural_five_cover_core_action h hnat hE K hKI hNK hKM e hab).2
  have hcomm (x y : K) (hx : x ∈ pCore 2 K) (hy : y ∈ pCore 2 K) :
      ρ x * ρ y = ρ y * ρ x :=
    setLike_mul_comm (s := A) (mem_map_of_mem ρ hx) (mem_map_of_mem ρ hy)
  change ∀ k : K, k ∈ pCore 2 K → k*a k*a (a k) ∈ ρ.ker
  intro k hk
  let v := k*a k*a (a k)
  have hv : v ∈ pCore 2 K :=
    (pCore 2 K).mul_mem ((pCore 2 K).mul_mem hk (hqa k hk)) (hqa (a k) (hqa k hk))
  have hnorm : ρ (a v)=ρ v := by
    dsimp only [v]
    rw [map_mul,map_mul,ha3,map_mul,map_mul,map_mul,map_mul]
    calc
      ρ (a k)*ρ (a (a k))*ρ k = ρ (a k)*(ρ k*ρ (a (a k))) := by
        rw [mul_assoc,hcomm (a (a k)) k (hqa (a k) (hqa k hk)) hk]
      _ = ρ k*ρ (a k)*ρ (a (a k)) := by
        rw [←mul_assoc,hcomm (a k) k (hqa k hk) hk]
  exact hfixed v hv ((mul_inv_eq_iff_eq_mul.mp ((heq v).symm.trans hnorm)).symm)

/-- The three actual cubic conjugates of a moving core involution generate
a cubic-invariant subgroup of the original core. Its literal span-action
image is an elementary four-group; the ambient action kernel is retained. -/
theorem natural_five_core_involution_cubic_orbit
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3)
    (t : K) (ht : t ∈ pCore 2 K) (ht2 : orderOf t=2)
    (htmove : naturalFiveCoverAction L R K t ≠ 1) :
    let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
    let D := (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))
    let ρ := naturalFiveCoverAction L R K
    D ≤ pCore 2 K ∧ D.map a.toMonoidHom=D ∧
      orderOf (a t)=2 ∧ orderOf (a (a t))=2 ∧
      IsElementaryAbelian 2 (D.map ρ) ∧ Nat.card (D.map ρ)=4 ∧
      (D.map K.subtype) ≤ (T : Subgroup G) ∧
      (t*a t*a (a t)) ∈ ρ.ker ∧
      (∀ x : K, x ∈ D → (ρ x=1 ↔
        (x : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G))) := by
  let a := K.normalizerMonoidHom ⟨c,hNK hcN⟩
  let D := (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))
  let ρ := naturalFiveCoverAction L R K
  have hqa (k : K) (hk : k ∈ pCore 2 K) : a k ∈ pCore 2 K :=
    (characteristic_iff_map_le.mp inferInstance a) (mem_map_of_mem a.toMonoidHom hk)
  have hD : D ≤ pCore 2 K :=
    sup_le (sup_le (zpowers_le.mpr ht) (zpowers_le.mpr (hqa t ht)))
      (zpowers_le.mpr (hqa (a t) (hqa t ht)))
  have ha : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hNK hcN⟩ : normalizer (K : Set G))^3=1 :=
      Subtype.ext (hc3 ▸ pow_orderOf_eq_one c)
    rw [hh,map_one]
  have ha3 (k : K) : a (a (a k))=k := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha k
  have hnorm := natural_five_core_cubic_norm h hnat hE K hKI hNK hKM e hab hcL hcN hc3 t ht
  change ρ (t*a t*a (a t))=1 at hnorm
  rw [map_mul,map_mul] at hnorm
  let A := (pCore 2 K).map ρ
  let : IsElementaryAbelian 2 A :=
    (natural_five_cover_core_action h hnat hE K hKI hNK hKM e hab).2
  have hpow (k : K) (hk : k ∈ pCore 2 K) : (ρ k)^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem ρ hk)
  have hx2 : orderOf (ρ t)=2 := orderOf_eq_prime (hpow t ht) htmove
  have hcS := (natural_five_cubic_fixed_core_action h hnat K hKI hNK e hcL hcN hc3).choose
  have hker (k : K) (hk : ρ (a k)=1) : ρ k=1 := by
    have hc : (a k : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G) := by
      change a k ∈ (centralizer (conjugateSpanBy (layer L R) K : Set G)).subgroupOf K
      rw [←naturalFiveCoverAction_ker]
      exact hk
    have hn := normalizer_le_normalizer_centralizer (conjugateSpanBy (layer L R) K) hcS
    have hh := (mem_normalizer_iff.mp hn (k : G)).mpr hc
    change k ∈ ρ.ker
    rw [naturalFiveCoverAction_ker]
    exact hh
  have hyne : ρ (a t) ≠ 1 := fun hy => htmove (hker t hy)
  have hzne : ρ (a (a t)) ≠ 1 := fun hz => hyne (hker (a t) hz)
  have hxy : ρ t ≠ ρ (a t) := by
    intro he
    rw [←he,←pow_two,hpow t ht,one_mul] at hnorm
    exact hzne hnorm
  have hy2 : orderOf (ρ (a t))=2 := orderOf_eq_prime (hpow (a t) (hqa t ht)) hyne
  have hcomm : Commute (ρ t) (ρ (a t)) :=
    setLike_mul_comm (s := A) (mem_map_of_mem ρ ht) (mem_map_of_mem ρ (hqa t ht))
  have hz : ρ (a (a t))=ρ t*ρ (a t) := by
    have hi : (ρ (a (a t)))⁻¹=ρ (a (a t)) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow (a (a t)) (hqa (a t) (hqa t ht)))
    exact ((mul_eq_one_iff_eq_inv.mp hnorm).trans hi).symm
  have hmap : D.map ρ=zpowers (ρ t) ⊔ zpowers (ρ (a t)) := by
    rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,MonoidHom.map_zpowers,hz]
    exact sup_eq_left.mpr (zpowers_le.mpr (mul_mem_sup (mem_zpowers _) (mem_zpowers _)))
  refine ⟨hD,?_,(a.orderOf_eq t).trans ht2,
    (a.orderOf_eq (a t)).trans ((a.orderOf_eq t).trans ht2),?_,?_,?_,?_,?_⟩
  · rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    change (zpowers (a t) ⊔ zpowers (a (a t))) ⊔ zpowers (a (a (a t)))=D
    rw [ha3]
    dsimp only [D]
    ac_rfl
  · exact IsElementaryAbelian.of_injective (inclusion (show D.map ρ ≤ A from map_mono hD)) (inclusion_injective _)
  · rw [hmap]
    exact card_involution_pair _ _ hx2 hy2 hcomm hxy
  · obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K (h.sylow_normalizes_ZS.trans hNK)
    have hh := pCoreIn_le_sylow K P
    rw [hP,subgroupOf_map_subtype] at hh
    exact (map_mono hD).trans (hh.trans inf_le_left)
  · exact natural_five_core_cubic_norm h hnat hE K hKI hNK hKM e hab hcL hcN hc3 t ht
  · intro x _
    change x ∈ ρ.ker ↔ _
    rw [naturalFiveCoverAction_ker]
    rfl


/-- For every original cubic, the actual core-moving involution from the
preceding alternative generates a cubic-invariant two-subgroup in T.
Its action quotient is elementary of order four, with the whole kernel. -/
@[expose] def NaturalFiveCubicCoreData (T : Sylow 2 G) (L R E K : Subgroup G) : Prop :=
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
  ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
    ∃ hcK : c ∈ normalizer (K : Set G),
      let a := K.normalizerMonoidHom ⟨c,hcK⟩
      let ρ := naturalFiveCoverAction L R K
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
      (∃ t : K, (t : G) ∈ E ∧ orderOf t=2 ∧
        q t ∈ alternatingGroup (Fin 5) ∧ q t ≠ 1) ∨
      (∃ t : K, t ∈ pCore 2 K ∧ orderOf t=2 ∧
        ⁅layer L R,zpowers (t : G)⁆ = ZS (T : Subgroup G) L R ∧
        let D := (zpowers t ⊔ zpowers (a t)) ⊔ zpowers (a (a t))
        D ≤ pCore 2 K ∧ D.map a.toMonoidHom=D ∧
        orderOf (a t)=2 ∧ orderOf (a (a t))=2 ∧
        IsElementaryAbelian 2 (D.map ρ) ∧ Nat.card (D.map ρ)=4 ∧
        D.map K.subtype ≤ (T : Subgroup G) ∧
        (t*a t*a (a t)) ∈ ρ.ker ∧
        (∀ x : K, x ∈ D → (ρ x=1 ↔
          (x : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G))))

/-- Apply the cubic orbit construction to the literal full-line movement
provided by the original seed alternative. No commutation of the ambient
orbit generators or disappearance of the centralizer kernel is assumed. -/
theorem natural_five_cubic_core_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (E : Subgroup G) (hcore : NaturalFiveCoreMovementData T L R E K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveCubicCoreData T L R E K := by
  intro e c hcL hcN hc3
  refine ⟨hNK hcN,?_⟩
  rcases (hcore.2.2 e).2 with heven | ⟨t,ht,_,ht2,htcomm⟩
  · exact Or.inl heven
  right
  obtain ⟨t,ht,rfl⟩ := ht
  have ht2 : orderOf t=2 := (Subgroup.orderOf_coe t).symm.trans ht2
  refine ⟨t,ht,ht2,htcomm,?_⟩
  have hm : naturalFiveCoverAction L R K t ≠ 1 := by
    intro htfix
    have htc : (t : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G) := by
      change t ∈ (centralizer (conjugateSpanBy (layer L R) K : Set G)).subgroupOf K
      rw [←naturalFiveCoverAction_ker]
      exact htfix
    have htV := centralizer_le (le_conjugateSpanBy (layer L R) K) htc
    have hz : zpowers (t : G) ≤ centralizer (layer L R : Set G) := zpowers_le.mpr htV
    have hzero : ⁅layer L R,zpowers (t : G)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hz)
    exact h.ZS_ne_bot (htcomm.symm.trans hzero)
  exact natural_five_core_involution_cubic_orbit h hnat hE K hKI hNK hKM e hab
    hcL hcN hc3 t ht ht2 hm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
