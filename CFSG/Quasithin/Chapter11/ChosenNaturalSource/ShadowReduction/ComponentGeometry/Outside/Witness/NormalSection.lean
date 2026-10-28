module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Equal
public import CFSG.Quasithin.ChapterE.Section03.NormalSectionContainment

/-!
# Rank-one weak closure in the normal R₁O²(H) carrier

Restrict the conjugate family of V to a subgroup Y normalized by H.
The weak closure in a Sylow subgroup of H is then the original weak
closure in its intersection with Y. For a rank-one E-member, every
conjugate of the intersection of its elementary generator with its
two-core stays in Y. Centralizer rigidity therefore puts its two-residual
in C_G(C₁(T intersect Y,V)). E-generation gives the required containment
of H from the two original weak-closure bounds on that intersection.

Apply this argument to the already constructed normal subgroup
R₁O²(H). Its actual Sylow witness identifies T intersect R₁O²(H) with R₁.
The proved equality-row theorem n(H)=1 and the original 11.2.2 clauses
now contradict H escaping M. This also proves the generation-one bound
for the literal smaller carrier under those same ambient source clauses.
No general descent assertion for generation parameters is used.

The OddKernelNormalizer input remains with
qt-d-1222-natural-odd-kernel-normalizer. Earlier geometry, the G₂ weak-closure
clauses, the linear fixed space, 11.3.2 and Kz=K retain
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison.
Final discharge belongs to qt-d-1222-shadow-components. The universal
strict-component 11.4.4 argument remains with this witness task.

Source: Aschbacher--Smith, E.1.4, E.3.6, E.3.17--19 and 11.5.1,
printed pp.210,231--235,778--779 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.NormalSection
variable {G : Type*} [Group G] [Finite G]

private theorem core_corank_eq_one {K : Type*} [Group K] [Finite K]
    (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ 1)
    (hn : ¬ A ≤ pCore 2 K) : subgroupCorank A (A ⊓ pCore 2 K) = 1 := by
  have hle := SourceContainment.core_corank_le A hr
  have hpos : subgroupCorank A (A ⊓ pCore 2 K) ≠ 0 := by
    intro hz
    have hi : (A ⊓ pCore 2 K).relIndex A = 1 := by
      rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
        ← subgroupCorank_eq_quotient_finrank, hz, pow_zero]
    exact hn ((Subgroup.relIndex_eq_one.mp hi).trans inf_le_right)
  omega

private theorem normalClosure_centralizes {V R Y : Subgroup G} [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hs : (1 : ℕ∞) < globalS V)
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ R)
    (hAY : A.map f ≤ Y) (hNY : f.range ≤ normalizer (Y : Set G))
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ 1)
    (hn : ¬ A ≤ pCore 2 K) :
    (normalClosure (A : Set K)).map f ≤ centralizer (weakCentralizer V (R ⊓ Y) 1 : Set G) := by
  have hi := core_corank_eq_one A hr hn
  have hconj (k : K) :
      A.map (f.comp (MulAut.conj k).toMonoidHom) ≤
        centralizer (weakCentralizer V (R ⊓ Y) 1 : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    let B := (A ⊓ pCore 2 K).map f'
    let W := V.map (MulAut.conj (f k * g)).toMonoidHom
    let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hBW : B ≤ W := by
      change B ≤ V.map (MulAut.conj (f k * g)).toMonoidHom
      rw [← he]
      exact map_mono inf_le_left
    have hBR : B ≤ R ⊓ Y := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨hcore (mem_map_of_mem f
        ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)), ?_⟩
      have hnY := hNY (show f k ∈ f.range from ⟨k,rfl⟩)
      have haY := hAY (mem_map_of_mem f ha.1)
      change f' a ∈ Y
      simpa only [f', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_inv] using
        (Subgroup.mem_normalizer_iff.mp hnY (f a)).mp haY
    have hb : subgroupCorank W B = 1 := by
      change subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom) B = 1
      rw [← he]
      change Nat.log 2 (((A ⊓ pCore 2 K).map f').relIndex (A.map f')) = 1
      rw [relIndex_map_map_of_injective _ _ hinj]
      exact hi
    have hgamma : B ∈ gamma V (R ⊓ Y) 1 := by
      refine ⟨⟨f k * g, hBW, ?_⟩, hBR⟩
      change B.relIndex W = 2 ^ 1
      rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
        ← subgroupCorank_eq_quotient_finrank, hb]
    have hCB : weakCentralizer V (R ⊓ Y) 1 ≤ centralizer (B : Set G) :=
      inf_le_right.trans (centralizer_le (gamma_le_weakClosure hgamma))
    have hbs : (subgroupCorank W B : ℕ∞) < globalS W := by
      rw [hb, show globalS W = globalS V from globalS_map_equiv _ _]
      exact hs
    have hc := centralizer_inf_eq_of_corank_lt_globalS
      (E := weakCentralizer V (R ⊓ Y) 1) hBW hbs (hR.to_inf_left).to_inf_left
    apply le_centralizer_iff.mpr
    rw [he]
    exact (le_inf le_rfl hCB).trans (hc.le.trans inf_le_right)
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)

/-- Rank-one E-generation in a normalized section uses its literal Sylow intersection. -/
theorem le_of_isEGenerated {V M H Y : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hgen : IsEGeneratedAt 1 S)
    (hHY : H ≤ normalizer (Y : Set G))
    (hNM : normalizer (indexedWeakClosure V
      ((S : Subgroup H).map H.subtype ⊓ Y) 0 : Set G) ≤ M)
    (hC : centralizer (weakCentralizer V
      ((S : Subgroup H).map H.subtype ⊓ Y) 1 : Set G) ≤ M)
    (hs : (1 : ℕ∞) < globalS V) : H ≤ M := by
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, hi⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV) (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let Ψ : Set (Subgroup G) := {A | A ∈ Ω ∧ A ≤ Y}
  let ΩH := ChiefOrbit.restrictedFamily H Ψ
  have hΩH : IsElementaryFamily ΩH := by
    constructor
    · intro A hA
      exact (ChiefOrbit.restrictedFamily_elementary H hΩ).1 A hA.1
    · intro g A hA
      have he : (A.map (MulAut.conj g).toMonoidHom).map H.subtype =
          (A.map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
        rw [map_map,map_map]; rfl
      change (A.map (MulAut.conj g).toMonoidHom).map H.subtype ∈ Ψ
      rw [he]
      refine ⟨hΩ.2 g _ hA.1,?_⟩
      exact (map_mono hA.2).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hHY g.property))
  let Sg := (S : Subgroup H).map H.subtype
  have hSM : Sg ≤ M := by
    apply le_trans ?_ hNM
    apply le_trans ?_ (normalizer_le_weakClosure_normalizer V (Sg ⊓ Y) 0)
    exact (le_inf Sg.le_normalizer ((map_subtype_le _).trans hHY)).trans
      inf_normalizer_le_normalizer_inf
  have hSMH : (S : Subgroup H) ≤ M.subgroupOf H := map_le_iff_le_comap.mp hSM
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype =
      indexedWeakClosure V (Sg ⊓ Y) 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily Sg H (map_subtype_le _) Ψ
    have hsub : Sg.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rw [hsub] at he
    rw [he]
    change sSup {A | (A ∈ Ω ∧ A ≤ Y) ∧ A ≤ Sg} = sSup {A | A ∈ Ω ∧ A ≤ Sg ⊓ Y}
    congr 1
    ext A
    simp only [Set.mem_ofPred_eq,le_inf_iff]
    tauto
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
    exact hNM
  have hE : eFamilySubgroup 1 (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA := A.property.1
    have hAS : A.val.map H.subtype ≤ Sg := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V Sg (A.val.map H.subtype)).mp ⟨hA.1, hAS⟩
    let AK := A.val.subgroupOf K
    let _ : IsElementaryAbelian 2 A.val := hK.1.1
    let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    let f := H.subtype.comp K.subtype
    have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
    have heA : AK.map f = V.map (MulAut.conj g).toMonoidHom := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hAg
    have hAY : AK.map f ≤ Y := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hA.2
    have hNY : f.range ≤ normalizer (Y : Set G) := by
      rintro x ⟨k,rfl⟩
      exact hHY k.val.property
    have hcore : (pCore 2 K).map f ≤ Sg := by
      obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
      have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
      rw [hU, subgroupOf_map_subtype] at hcu
      change (pCore 2 K).map (H.subtype.comp K.subtype) ≤ Sg
      rw [← map_map]
      exact map_mono (hcu.trans inf_le_left)
    have hNC := normalClosure_centralizes (S.2.map H.subtype) hs AK f hf g heA
      hcore hAY hNY (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK)
      (ValuesEvenClassical.Sp4Lower.member_not_le_core hK.1)
    have hRC := (map_mono hK.1.residual_le_normalClosure).trans hNC
    apply hK.1.le_of_residual_le hSMH
    rintro x ⟨k, hk, rfl⟩
    exact hC (hRC (mem_map_of_mem f hk))
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)


/-- Parameter-one specialization with the actual normalized carrier. -/
theorem le_of_parameter_eq_one {V M H Y : Subgroup G} [IsElementaryAbelian 2 V]
    (S : Sylow 2 H) (hn : generationParameter H = 1)
    (hHY : H ≤ normalizer (Y : Set G))
    (hN : normalizer (indexedWeakClosure V
      ((S : Subgroup H).map H.subtype ⊓ Y) 0 : Set G) ≤ M)
    (hC : centralizer (weakCentralizer V
      ((S : Subgroup H).map H.subtype ⊓ Y) 1 : Set G) ≤ M)
    (hs : (1 : ℕ∞) < globalS V) : H ≤ M := by
  have hg := isEGenerated_generationParameter_of_pos (G := H) (by omega)
  rw [hn] at hg
  exact le_of_isEGenerated S (hg S) hHY hN hC hs

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The constructed normal carrier has exactly R₁ as its intersection with T. -/
theorem radical_carrier_sylow_intersection
    (hSyl : Chapter1.IsSylowIn 2 E.R₁
      (E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype)) :
    (T : Subgroup G) ⊓ (E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype) = E.R₁ := by
  exact (Chapter1.isSylowIn_iff.mp hSyl).2.2 _ T.isPGroup'.to_inf_left
    (le_inf (LocalGeometry.localRadical_le_sylow _) le_sup_left) inf_le_right

/-- Apply rank-one generation to H and its normal R₁O²(H) carrier.
The centralizer and normalizer bounds are the literal preceding 11.2.2 clauses. -/
theorem radical_carrier_impossible
    (hTH : (T : Subgroup G) ≤ E.H)
    (hSyl : Chapter1.IsSylowIn 2 E.R₁
      (E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype))
    (hn : generationParameter E.H = 1) (hout : ¬ E.H ≤ E.M)
    (hs : (1 : ℕ∞) < @globalS G _ V D.elementary)
    (hC : centralizer (weakCentralizer V E.R₁ 1 : Set G) ≤ E.M)
    (hN : normalizer (indexedWeakClosure V E.R₁ 0 : Set G) ≤ E.M) : False := by
  let J := E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype
  let := D.elementary
  have hJH : J ≤ E.H := sup_le
    ((LocalGeometry.localRadical_le_sylow _).trans hTH) (map_subtype_le _)
  let : (J.subgroupOf E.H).Normal := radical_carrier_normal E hTH
  have hHJ : E.H ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hJH).mp inferInstance
  have hR : ((T.subtype hTH : Subgroup E.H).map E.H.subtype) ⊓ J = E.R₁ := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
    exact radical_carrier_sylow_intersection E hSyl
  apply hout
  apply le_of_parameter_eq_one (V := V) (T.subtype hTH) hn hHJ
  · simpa only [hR] using hN
  · simpa only [hR] using hC
  · exact hs

variable (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The equality row of original 11.5.1, using the already constructed
carrier and the earlier source weak-closure clauses on R₁. -/
theorem ofFlag_equal_impossible
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hs : (1 : ℕ∞) < @globalS G _ V D.elementary)
    (hC : centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G)) :
    False := by
  obtain ⟨J,hJ,_,_,hn,_,_,hSyl,_⟩ :=
    Generation.ofFlag_equal_selected_generation_one S f X z H h he hK hNT hlinear h1132 hcontrol
  exact radical_carrier_impossible (ofFlag S f X z J) hJ.1.1.2 hSyl hn hJ.1.2 hs hC hN

/-- In the equality row, the literal smaller carrier has generation one
under the original G₂ weak-closure clauses. The normal-section argument
proves the necessary exclusion directly; no monotonicity of n is assumed. -/
theorem ofFlag_equal_carrier_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (halt : SelectedResidualAlternative (ofFlag S f X z H))
    (hs : (1 : ℕ∞) < @globalS G _ V D.elementary)
    (hC : centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G)) :
    generationParameter ((ofFlag S f X z H).R₁ ⊔ (pResidual 2 H).map H.subtype : Subgroup G) = 1 := by
  have hcarrier := equal_selected_radical_carrier (ofFlag S f X z H) h he
    (f.invariant 0) hK (ofFlag_equal_quotient_center S f X z H hK) hH hHz halt
  have hn := Generation.ofFlag_equal_generation_eq_one S f X z H h he hK
    hlinear h1132 hcontrol hH hHz
  exact (radical_carrier_impossible (ofFlag S f X z H) hH.1.1.2
    hcarrier.2.2.1 hn hH.1.2 hs hC hN).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.NormalSection
