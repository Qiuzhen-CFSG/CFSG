module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveMovement

/-!
# The full S5 cover's action kernel and core movement

Let S be the span of the natural layer under the original invariant cover K.
The full two-core acts trivially on Z_S and S/Z_S, so its action on S is
an elementary group of central displacements. The action kernel lies in
O2(K), by the exact quotient-action kernel already established.

The specified map K/O2(K) to S5 descends to the faithful action image.
Cubic-fixed representatives give a section of this descended map, whose
kernel is exactly the elementary two-core of that image. This splits the
action image while retaining the full ambient centralizer kernel.

The even seed's moving involution either has a nonidentity even S5 image,
or lies in the full core. In the latter case a K-conjugate moves the
original natural layer; source centralizer rigidity identifies its entire
commutator with Z_S. The involution remains in the original Sylow.

The Chapter12 application uses the same W/Z_S witness and explicit mixed
size premise. An elementary lift through the remaining ambient kernel,
T-invariant parabolic escape, initial 6.1.4–5, exact omega escape and the
remaining conclusions through 6.1.27 are still obligations of
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.17(4), 6.1.19, printed pp.672–675
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem elementary_displacement_action
    {S : Type*} [Group S] [IsElementaryAbelian 2 S]
    (Z : Subgroup S) (A : Subgroup (MulAut S))
    (hfix : ∀ a ∈ A, ∀ z ∈ Z, a z = z)
    (hmove : ∀ a ∈ A, ∀ s : S, a s / s ∈ Z) :
    IsElementaryAbelian 2 A := by
  have hcalc (a b : A) (s : S) :
      a.val (b.val s) = (b.val s / s) * a.val s := by
    calc
      _ = a.val ((b.val s / s) * s) := by rw [div_mul_cancel]
      _ = (b.val s / s) * a.val s := by rw [map_mul,hfix _ a.property _ (hmove _ b.property s)]
  refine { is_comm.comm := ?_, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro a b
    apply Subtype.ext
    apply MulEquiv.ext
    intro s
    change a.val (b.val s) = b.val (a.val s)
    rw [hcalc,hcalc]
    simp only [div_eq_mul_inv]
    ac_rfl
  · intro a
    apply Subtype.ext
    apply MulEquiv.ext
    intro s
    change a.val (a.val s) = s
    rw [hcalc]
    have hs (x : S) : x*x=1 := by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 S) x
    have hinv : s⁻¹=s := inv_eq_of_mul_eq_one_right (hs s)
    simp only [div_eq_mul_inv,hinv]
    calc
      _ = (a.val s * a.val s) * s := by ac_rfl
      _ = s := by rw [hs,one_mul]

/-- Conjugation by the original cover on its ambient natural-layer span. -/
@[expose] def naturalFiveCoverAction {G : Type*} [Group G]
    (L R K : Subgroup G) : K →* MulAut (conjugateSpanBy (layer L R) K) :=
  (conjugateSpanBy (layer L R) K).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy (layer L R) K))

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

omit [Finite G] in
theorem naturalFiveCoverAction_ker (L R K : Subgroup G) :
    (naturalFiveCoverAction L R K).ker =
      (centralizer (conjugateSpanBy (layer L R) K : Set G)).subgroupOf K := by
  ext k
  change naturalFiveCoverAction L R K k = 1 ↔ _
  constructor
  · intro he x hx
    have hh := congrArg (fun f : MulAut (conjugateSpanBy (layer L R) K) =>
      (f ⟨x,hx⟩ : G)) he
    change (k : G)*x*(k : G)⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hk
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change (k : G)*(s : G)*(k : G)⁻¹=s
    exact mul_inv_eq_iff_eq_mul.mpr (hk s s.property).symm

/-- The full two-core acts through an elementary group of central
displacements on the literal span. Its action kernel is retained. -/
theorem natural_five_cover_core_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let ρ := naturalFiveCoverAction L R K
    ρ.ker ≤ pCore 2 K ∧ IsElementaryAbelian 2 ((pCore 2 K).map ρ) := by
  let S := conjugateSpanBy (layer L R) K
  let Z := ZS (T : Subgroup G) L R
  let ρ := naturalFiveCoverAction L R K
  obtain ⟨hel,_,hSU,_⟩ := natural_five_span_action_data h hnat hE K hKI hNK hKM hab
  let := hel
  have hQKI : K.pCoreIn 2 ≤ (Escape.I (T : Subgroup G) L R).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hKI ((Subgroup.centralizer_le_normalizer _).trans hNK)
  have hcomm : ⁅K.pCoreIn 2,S⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono hSU hQKI).trans (natural_escape_core h hnat).2
  refine ⟨?_,?_⟩
  · intro k hk
    have hc : (k : G) ∈ centralizer (S : Set G) := by
      rw [naturalFiveCoverAction_ker] at hk
      exact hk
    have hd : (k : G) ∈ commutatorPreimage K S Z := by
      apply (mem_commutatorPreimage_iff K S Z
        (hKI.trans (Subgroup.centralizer_le_normalizer _)) k).mpr
      refine ⟨k.property,?_⟩
      intro s hs
      have hh := hc s hs
      rw [commutatorElement_def,←hh,mul_inv_cancel_right,mul_inv_cancel]
      exact Z.one_mem
    rw [natural_five_span_quotient_kernel h hnat hE K hKI hNK hKM e hab] at hd
    obtain ⟨q,hq,he⟩ := hd
    exact (show q=k from Subtype.ext he) ▸ hq
  · apply elementary_displacement_action (Z.subgroupOf S)
    · rintro a ⟨k,hk,rfl⟩ z hz
      apply Subtype.ext
      change (k : G)*(z : G)*(k : G)⁻¹=z
      exact mul_inv_eq_iff_eq_mul.mpr ((hKI k.property) z hz).symm
    · rintro a ⟨k,hk,rfl⟩ s
      change (k : G)*(s : G)*(k : G)⁻¹/(s : G) ∈ Z
      simpa only [div_eq_mul_inv,commutatorElement_def] using
        commutator_le.mp hcomm k (mem_map_of_mem K.subtype hk) s s.property

/-- The faithful action image is a split extension of its elementary
two-core by the specified S5. The section is induced by the actual cubic
centralizer, and the ambient action kernel remains explicit. -/
theorem natural_five_cover_action_split
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
    let ρ := naturalFiveCoverAction L R K
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    ∃ (π : ρ.range →* Equiv.Perm (Fin 5))
      (s : Equiv.Perm (Fin 5) →* ρ.range),
      π.comp ρ.rangeRestrict = q ∧ π.comp s = MonoidHom.id _ ∧
      π.ker = (pCore 2 K).map ρ.rangeRestrict ∧
      π.ker = pCore 2 ρ.range ∧ IsElementaryAbelian 2 π.ker ∧
      (∀ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G),
        s (q (inclusion inf_le_left d)) = ρ.rangeRestrict (inclusion inf_le_left d)) := by
  let ρ := naturalFiveCoverAction L R K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hqk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hρk : ρ.rangeRestrict.ker ≤ q.ker := by
    rw [MonoidHom.ker_rangeRestrict,hqk]
    exact (natural_five_cover_core_action h hnat hE K hKI hNK hKM e hab).1
  let π := ρ.rangeRestrict.liftOfSurjective ρ.rangeRestrict_surjective ⟨q,hρk⟩
  have hπ (k : K) : π (ρ.rangeRestrict k)=q k :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  obtain ⟨τ,_,hτ⟩ := natural_five_span_action_faithful h hnat hE K hKI hNK hKM e hcL hcN hc3
  let C := K ⊓ centralizer (zpowers c : Set G)
  let j : C →* K := inclusion inf_le_left
  have hf := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
  have hτeq (d : C) : τ (q (j d)) = ρ (j d) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact hτ d x
  let s : Equiv.Perm (Fin 5) →* ρ.range := τ.codRestrict ρ.range (by
    intro a
    obtain ⟨d,hd⟩ := hf a
    exact ⟨j d,(hτeq d).symm.trans (congrArg τ hd)⟩)
  have hs (d : C) : s (q (j d)) = ρ.rangeRestrict (j d) := Subtype.ext (hτeq d)
  have hsplit : π.comp s = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro a
    obtain ⟨d,hd⟩ := hf a
    change π (s a)=a
    rw [←hd]
    change π (s (q (j d)))=q (j d)
    rw [hs,hπ]
  have hk : π.ker = (pCore 2 K).map ρ.rangeRestrict := by
    ext a
    obtain ⟨k,rfl⟩ := ρ.rangeRestrict_surjective a
    constructor
    · intro ha
      refine ⟨k,?_,rfl⟩
      rw [←hqk]
      change q k=1
      rw [←hπ]
      exact ha
    · rintro ⟨k',hk',he⟩
      rw [←he]
      change π (ρ.rangeRestrict k')=1
      rw [hπ]
      exact (show k' ∈ q.ker from hqk.symm ▸ hk')
  have helem : IsElementaryAbelian 2 π.ker := by
    have he := (natural_five_cover_core_action h hnat hE K hKI hNK hKM e hab).2
    let := he
    have hm : π.ker.map ρ.range.subtype = (pCore 2 K).map ρ := by
      rw [hk,map_map]
      rfl
    let f : π.ker →* (pCore 2 K).map ρ :=
      (ρ.range.subtype.comp π.ker.subtype).codRestrict _ (by
        intro a
        rw [←hm]
        exact mem_map_of_mem _ a.property)
    apply IsElementaryAbelian.of_injective f
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : (pCore 2 K).map ρ => x.val) hab
  have hπs : Function.Surjective π := by
    intro a
    exact ⟨s a,DFunLike.congr_fun hsplit a⟩
  have hp : π.ker = pCore 2 ρ.range := by
    let := helem
    have hh := π.comap_pCore_of_ker_isPGroup hπs (IsElementaryAbelian.isPGroup 2 π.ker)
    rwa [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot,MonoidHom.comap_bot] at hh
  exact ⟨π,s,MonoidHom.ext hπ,hsplit,hk,hp,helem,hs⟩

omit [Finite G] in
private theorem exists_conjugate_moving_layer
    (V K : Subgroup G) {t : G}
    (ht : t ∉ centralizer (conjugateSpanBy V K : Set G)) :
    ∃ k : K, (k : G)⁻¹*t*k ∉ centralizer (V : Set G) := by
  by_contra! hn
  apply ht
  have hv : conjugateSpanBy V K ≤ centralizer ({t} : Set G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro k
    rintro _ ⟨v,hv,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hn k v hv
    change v*((k : G)⁻¹*t*k)=((k : G)⁻¹*t*k)*v at hh
    have he := congrArg (fun x : G => (k : G)*x*(k : G)⁻¹) hh
    convert he using 1 <;> dsimp <;> group
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hv hx)

/-- An even seed involution either survives in the marked S5 quotient,
or a K-conjugate of it is an actual core involution moving the original
natural layer by the entire central line. -/
theorem natural_five_even_seed_core_movement
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = 2)
    (E K : Subgroup G) [IsElementaryAbelian 2 E]
    (hsE : ChapterE.globalS E = 2) (hcard : Nat.card E = 16)
    (hEK : E ≤ K) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔ K.pCoreIn 2 = K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    (∃ t : K, (t : G) ∈ E ∧ orderOf t = 2 ∧
      q t ∈ alternatingGroup (Fin 5) ∧ q t ≠ 1) ∨
    (∃ t : G, t ∈ K.pCoreIn 2 ∧ t ∈ (T : Subgroup G) ∧ orderOf t = 2 ∧
      ⁅layer L R,zpowers t⁆ = ZS (T : Subgroup G) L R) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  obtain ⟨_,_,_,_,t,ht,ht2,hte,htS⟩ := natural_five_even_seed_movement
    h hnat hE E K hsE hcard hEK hKI hNK hKM e hgen hab
  by_cases hqt : q t=1
  · right
    have htQ : (t : G) ∈ K.pCoreIn 2 := by
      apply mem_map_of_mem K.subtype
      exact (QuotientGroup.eq_one_iff t).mp (e.injective (hqt.trans e.map_one.symm))
    obtain ⟨k,hmove⟩ := exists_conjugate_moving_layer (layer L R) K htS
    let u : G := (k : G)⁻¹*(t : G)*(k : G)
    have huQ : u ∈ K.pCoreIn 2 := by
      have hk := (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
        (K.le_normalizer (K.inv_mem k.property))
      simpa only [u,pCoreIn,inv_inv] using (mem_normalizer_iff.mp hk t).mp htQ
    have hTK := h.sylow_normalizes_ZS.trans hNK
    obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
    have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow K P
      rw [hP,subgroupOf_map_subtype] at hh
      exact hh.trans inf_le_left
    have hu2 : orderOf u=2 := by
      simpa only [u,MulAut.conj_apply,inv_inv] using
        ((MulAut.conj (k : G)⁻¹).orderOf_eq (t : G)).trans
          ((Subgroup.orderOf_coe t).trans ht2)
    have hnon : ⁅layer L R,zpowers u⁆ ≠ ⊥ := by
      intro he
      exact hmove ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
        (mem_zpowers u))
    exact ⟨u,huQ,hQT huQ,hu2,NaturalEscapeGraph.commutator_eq_line h hnat hs
      (T.isPGroup'.to_le (zpowers_le.mpr (hQT huQ)))
      (zpowers_le.mpr (h.sylow_normalizes_layer (hQT huQ)))
      (zpowers_le.mpr (hKI ((pCoreIn_le 2 K) huQ))) hnon⟩
  · exact Or.inl ⟨t,ht.1,ht2,hte,hqt⟩

/-- The full cover's faithful action image and the remaining actual
involution movement, under every original S5 marking. -/
@[expose] def NaturalFiveCoreMovementData (T : Sylow 2 G) (L R E K : Subgroup G) : Prop :=
  let ρ := naturalFiveCoverAction L R K
  ρ.ker ≤ pCore 2 K ∧ IsElementaryAbelian 2 ((pCore 2 K).map ρ) ∧
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    (∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
      ∃ (π : ρ.range →* Equiv.Perm (Fin 5))
        (s : Equiv.Perm (Fin 5) →* ρ.range),
        π.comp ρ.rangeRestrict = q ∧ π.comp s = MonoidHom.id _ ∧
        π.ker = (pCore 2 K).map ρ.rangeRestrict ∧
        π.ker = pCore 2 ρ.range ∧ IsElementaryAbelian 2 π.ker ∧
        (∀ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G),
          s (q (inclusion inf_le_left d)) = ρ.rangeRestrict (inclusion inf_le_left d))) ∧
    ((∃ t : K, (t : G) ∈ E ∧ orderOf t = 2 ∧
        q t ∈ alternatingGroup (Fin 5) ∧ q t ≠ 1) ∨
      (∃ t : G, t ∈ K.pCoreIn 2 ∧ t ∈ (T : Subgroup G) ∧ orderOf t = 2 ∧
        ⁅layer L R,zpowers t⁆ = ZS (T : Subgroup G) L R))

/-- The original conjugate seed supplies both the split action image
and the actual core-displacement alternative, with no lift assumption. -/
theorem natural_five_core_movement_data
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
    NaturalFiveCoreMovementData T L R ((layer L R).map (MulAut.conj a).toMonoidHom) K := by
  let := h.layer_elementary
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hs : ChapterE.globalS E = 2 := by
    rw [ChapterE.globalS_map_equiv, hs₀]
  have hc : Nat.card E = 16 := by
    rw [card_map_of_injective (MulAut.conj a).injective,hnat.card]
    norm_num
  have hcore := natural_five_cover_core_action h hnat hE K hKI hNK hKM he.some hab
  refine ⟨hcore.1,hcore.2,?_⟩
  intro e
  exact ⟨fun c hcL hcN hc3 => natural_five_cover_action_split h hnat hE K hKI hNK hKM e hab hcL hcN hc3,
    natural_five_even_seed_core_movement h hnat hE hs₀ E K hs hc hEK hKI hNK hKM e hgen hab⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
