module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveSeed

/-!
# The full S5 cover and movement by the original even seed

Let K be the invariant cover and S the span of its conjugates of the
natural layer. Its full two-core centralizes S modulo Z_S. Conversely,
the image of that quotient-action kernel in the specified S5 quotient
is normal. Cubic-fixed representatives realize its action on S, and
fixing Z_S and S/Z_S makes each such operator have square one. The
faithful action on S and O2(S5)=1 therefore identify the kernel exactly.

The even part of the original order-sixteen seed has index two and
order eight. The source global s-value two makes its centralizer in S
equal to the whole seed's centralizer. If it fixed S, the whole seed
would lie in O2(K), contradicting its actual transposition image.
Thus an ambient even seed involution moves S, under every specified
quotient marking. No splitting of the covering extension is used.

The Chapter12 consumer retains the same witness and mixed-size premise.
T-invariant S5 parabolic escape, initial 6.1.4–5, exact omega escape and
final 6.1.27 assembly remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed pp.674–675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The full cover acts on its actual natural-layer span modulo Z_S
with kernel exactly its original two-core. -/
theorem natural_five_span_quotient_kernel
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    commutatorPreimage K (conjugateSpanBy (layer L R) K) (ZS (T : Subgroup G) L R) = K.pCoreIn 2 := by
  let I := Escape.I (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let S := conjugateSpanBy (layer L R) K
  let D := commutatorPreimage K S Z
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hKZ : K ≤ normalizer (Z : Set G) := hKI.trans (Subgroup.centralizer_le_normalizer _)
  have hKD : K ≤ normalizer (D : Set G) := commutatorPreimage_normalized K S Z K
    hKZ K.le_normalizer (le_normalizer_conjugateSpanBy _ _) hKZ
  have hDK : D ≤ K := commutatorPreimage_le _ _ _
  have hQKI : K.pCoreIn 2 ≤ I.pCoreIn 2 := pCoreIn_mono_of_normalizes hKI
    ((Subgroup.centralizer_le_normalizer _).trans hNK)
  obtain ⟨hel,hVS,hSU,hdata⟩ := natural_five_span_action_data h hnat hE K hKI hNK hKM hab
  let := hel
  have hQD : K.pCoreIn 2 ≤ D := le_commutatorPreimage (pCoreIn_le 2 K) (by
    rw [commutator_comm]
    exact (commutator_mono hSU hQKI).trans (natural_escape_core h hnat).2)
  obtain ⟨c,hcL,_,hcN,hc3,_⟩ := natural_four_exists_cubic h hnat
  obtain ⟨hcS,τ,hτi,hτ,_,hτZ,_⟩ := hdata e c hcL hcN hc3
  let D' := D.subgroupOf K
  let J := D'.map q
  let : D'.Normal := normal_subgroupOf_of_le_normalizer hKD
  let : J.Normal := Subgroup.Normal.map inferInstance q hq
  have hdisp (y : J) (s : S) : (τ y.val s / s : S).val ∈ Z := by
    obtain ⟨x,hx,hxy⟩ := y.property
    obtain ⟨d,hd⟩ := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3 (q x)
    let dK : K := inclusion inf_le_left d
    have hdx : (dK * x⁻¹ : K) ∈ q.ker := by
      change q (dK*x⁻¹)=1
      rw [map_mul,map_inv,show q dK=q x from hd,mul_inv_cancel]
    have hdD : (d : G) ∈ D := by
      have hmem := hQD (mem_map_of_mem K.subtype (hqk ▸ hdx))
      have hh := D.mul_mem hmem hx
      change ((d : G) * (x : G)⁻¹) * (x : G) ∈ D at hh
      simpa only [inv_mul_cancel_right] using hh
    rw [coe_div, div_eq_mul_inv]
    rw [←hxy,←hd]
    dsimp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hτ]
    exact (mem_commutatorPreimage_iff K S Z hKZ d).mp hdD |>.2 s s.property
  have hp : IsPGroup 2 J := by
    intro y
    refine ⟨1,?_⟩
    apply Subtype.ext
    change y.val ^ 2=1
    apply hτi
    rw [map_pow,map_one]
    apply MulEquiv.ext
    intro s
    have hf := hτZ y.val (τ y.val s / s) (hdisp y s)
    have hpow (x : S) : x*x=1 := by
      simpa only [pow_two] using
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 S) x
    simp only [div_eq_mul_inv] at hf
    rw [map_mul, map_inv] at hf
    have he := congrArg (fun x : S => x * τ y.val s) hf
    simp only [inv_mul_cancel_right] at he
    have hinv (x : S) : x⁻¹=x := inv_eq_of_mul_eq_one_right (hpow x)
    rw [hinv] at he
    have hh : τ y.val (τ y.val s)=s := by
      calc
        _ = τ y.val s * s * τ y.val s := he
        _ = s * (τ y.val s * τ y.val s) := by ac_rfl
        _ = s := by rw [hpow,mul_one]
    exact hh
  have hJ : J ≤ pCore 2 (Equiv.Perm (Fin 5)) := le_sSup ⟨inferInstance,hp⟩
  rw [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot] at hJ
  apply le_antisymm _ hQD
  intro x hx
  have hxq : q ⟨x,hDK hx⟩=1 := hJ (mem_map_of_mem q (show (⟨x,hDK hx⟩ : K) ∈ D' from hx))
  exact mem_map_of_mem K.subtype (hqk ▸ (show (⟨x,hDK hx⟩ : K) ∈ q.ker from hxq))

/-- The index-two even part of the original elementary seed must move
its actual natural-layer span. In particular it contains an ambient
involution with even marked image which does not centralize that span. -/
theorem natural_five_even_seed_movement
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (E K : Subgroup G) [IsElementaryAbelian 2 E]
    (hs : ChapterE.globalS E = 2) (hcard : Nat.card E = 16)
    (hEK : E ≤ K) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔ K.pCoreIn 2 = K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    let A := E ⊓ ((alternatingGroup (Fin 5)).comap q).map K.subtype
    let S := conjugateSpanBy (layer L R) K
    Nat.card A = 8 ∧ A.relIndex E = 2 ∧
      S ⊓ centralizer (A : Set G) = S ⊓ centralizer (E : Set G) ∧
      ¬ A ≤ centralizer (S : Set G) ∧
      ∃ t : K, (t : G) ∈ A ∧ orderOf t = 2 ∧ q t ∈ alternatingGroup (Fin 5) ∧
        (t : G) ∉ centralizer (S : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let A := E ⊓ ((alternatingGroup (Fin 5)).comap q).map K.subtype
  let S := conjugateSpanBy (layer L R) K
  have hAs : A.subgroupOf E = (alternatingGroup (Fin 5)).comap (q.comp (inclusion hEK)) := by
    ext x
    change ((x : G) ∈ E ∧ (x : G) ∈ ((alternatingGroup (Fin 5)).comap q).map K.subtype) ↔ _
    constructor
    · rintro ⟨_,y,hy,he⟩
      have hyx : y = inclusion hEK x := Subtype.ext he
      change q (inclusion hEK x) ∈ alternatingGroup (Fin 5)
      exact hyx ▸ (show q y ∈ alternatingGroup (Fin 5) from hy)
    · intro hx
      exact ⟨x.property, inclusion hEK x, hx, rfl⟩
  have hdiv : A.relIndex E ∣ 2 := by
    change (A.subgroupOf E).index ∣ 2
    rw [hAs,index_comap]
    simpa only [alternatingGroup.index_eq_two] using
      (alternatingGroup (Fin 5)).relIndex_dvd_index_of_normal (q.comp (inclusion hEK)).range
  obtain ⟨x,hx,_,hxswap⟩ := natural_five_seed_involution E K hEK hNK e hgen
  change (q x).IsSwap at hxswap
  have hxodd : q x ∉ alternatingGroup (Fin 5) := by
    intro he
    have hh := Equiv.Perm.mem_alternatingGroup.mp he
    rw [hxswap.sign_eq] at hh
    exact (by decide : (-1 : ℤˣ) ≠ 1) hh
  have hindex : A.relIndex E = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · have ha := relIndex_eq_one.mp h1 hx
      obtain ⟨y,hy,he⟩ := ha.2
      exact (hxodd ((show y=x from Subtype.ext he) ▸ hy)).elim
    · exact h2
  have hcorank : (ChapterE.subgroupCorank E A : ℕ∞) < ChapterE.globalS E := by
    rw [hs]
    unfold ChapterE.subgroupCorank
    rw [hindex]
    norm_num
  have hS : IsPGroup 2 S :=
    T.isPGroup'.to_le ((natural_five_span_action_data h hnat hE K hKI hNK hKM hab).2.2.1.trans
      (natural_escape_U_le_sylow h hnat))
  have he := ChapterE.centralizer_inf_eq_of_corank_lt_globalS
    (show A ≤ E from inf_le_left) hcorank hS
  have hmove : ¬ A ≤ centralizer (S : Set G) := by
    intro ha
    have hSE : S ≤ centralizer (E : Set G) := by
      have hh : S ≤ S ⊓ centralizer (A : Set G) := le_inf le_rfl (le_centralizer_iff.mp ha)
      rw [he] at hh
      exact hh.trans inf_le_right
    have hEQ : E ≤ K.pCoreIn 2 := by
      rw [←natural_five_span_quotient_kernel h hnat hE K hKI hNK hKM e hab]
      exact le_commutatorPreimage hEK
        ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hSE)).le.trans bot_le)
    obtain ⟨y,hy,he⟩ := hEQ hx
    have hyx : y=x := Subtype.ext he
    have hqx : q x=1 := by
      change e (QuotientGroup.mk' (pCore 2 K) x)=1
      have hxq : QuotientGroup.mk' (pCore 2 K) x = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 K) x).mpr (hyx ▸ hy)
      rw [hxq,map_one]
    exact hxodd (hqx ▸ one_mem _)
  have hAcard : Nat.card A = 8 := by
    have hh := relIndex_mul_card_of_le (show A ≤ E from inf_le_left)
    rw [hindex,hcard] at hh
    omega
  refine ⟨hAcard,hindex,he,hmove,?_⟩
  obtain ⟨t,ht,htC⟩ := SetLike.not_le_iff_exists.mp hmove
  let tK : K := ⟨t,hEK ht.1⟩
  have ht2 : tK^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian t ht.1)
  have ht1 : tK ≠ 1 := fun he => htC (by
    have he' : t=1 := congrArg Subtype.val he
    rw [he']
    exact one_mem _)
  refine ⟨tK,ht,orderOf_eq_prime ht2 ht1,?_,htC⟩
  obtain ⟨y,hy,he⟩ := ht.2
  exact (show y=tK from Subtype.ext he) ▸ hy

/-- Movement of the actual even seed, with the full original two-core
and every specified S5 quotient marking retained. -/
@[expose] def NaturalFiveSeedMovementData (T : Sylow 2 G) (L R E K : Subgroup G) : Prop :=
  let S := conjugateSpanBy (layer L R) K
  commutatorPreimage K S (ZS (T : Subgroup G) L R) = K.pCoreIn 2 ∧
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    let A := E ⊓ ((alternatingGroup (Fin 5)).comap q).map K.subtype
    Nat.card A = 8 ∧ A.relIndex E = 2 ∧
      S ⊓ centralizer (A : Set G) = S ⊓ centralizer (E : Set G) ∧
      ¬ A ≤ centralizer (S : Set G) ∧
      ∃ t : K, (t : G) ∈ A ∧ orderOf t = 2 ∧ q t ∈ alternatingGroup (Fin 5) ∧
        (t : G) ∉ centralizer (S : Set G)

/-- Apply the exact kernel and hyperplane movement to the original
conjugate seed and invariant cover. No elementary lifting premise is added. -/
theorem natural_five_seed_movement_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs₀ : letI := h.layer_elementary; ChapterE.globalS (layer L R) = 2)
    (a : G) (K : Subgroup G)
    (hEK : (layer L R).map (MulAut.conj a).toMonoidHom ≤ K)
    (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5)))
    (hgen : conjugateSpanBy ((layer L R).map (MulAut.conj a).toMonoidHom)
      (Escape.I (T : Subgroup G) L R) ⊔ K.pCoreIn 2 = K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveSeedMovementData T L R ((layer L R).map (MulAut.conj a).toMonoidHom) K := by
  let := h.layer_elementary
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hs : ChapterE.globalS E = 2 := by
    rw [ChapterE.globalS_map_equiv, hs₀]
  have hc : Nat.card E = 16 := by
    rw [card_map_of_injective (MulAut.conj a).injective,hnat.card]
    norm_num
  exact ⟨natural_five_span_quotient_kernel h hnat hE K hKI hNK hKM he.some hab,
    fun e => natural_five_even_seed_movement h hnat hE E K hs hc hEK hKI hNK hKM e hgen hab⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
