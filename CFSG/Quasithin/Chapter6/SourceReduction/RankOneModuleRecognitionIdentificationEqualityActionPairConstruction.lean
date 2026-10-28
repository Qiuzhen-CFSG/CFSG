module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelExclusions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionPairContract
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupTheory.EmbeddedCenterMap
public import Mathlib.Data.Fintype.Perm
public import Theory.GroupTheory.SylowKernelCore

/-!
# The canonical equality pair and its extraspecial core

The natural action identifies H/O₂(H) with S₃. Two conjugate layer images
generate this quotient. Since O₂(H) normalizes both lifted layers, their
join is normal in H and equals the normal closure K of the actual layer.
The earlier two-conjugate theorem then supplies Q₈ * Q₈ and the S₃ quotient.
All centers, residuals and intersections are transported along the literal
subtype embeddings to K and its embedded core P.

The plane normal closure U lies in O₂(H) and in K, hence in O₂(K). Its
central involution lies in the order-two center of P, identifying that
center with the distinguished line. No extension splitting is asserted.

Source: Aschbacher–Smith, Proposition 6.2.13, printed p.687 (PDF p.704),
through the application of 6.2.6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension

attribute [local instance] fintypePerm

private theorem symmetricThree_pair (a : Equiv.Perm (Fin 3)) (ha : a^2 = 1) (ha1 : a ≠ 1) :
    ∃ t : Equiv.Perm (Fin 3),
      let b := t*a*t⁻¹
      ¬ Commute a b ∧ (a*b)^3 = 1 ∧ a*b ≠ 1 ∧
      ∀ d, d = 1 ∨ d = a ∨ d = b ∨ d = a*b ∨ d = b*a ∨ d = a*b*a := by
  have h : ∀ a : Equiv.Perm (Fin 3), a^2 = 1 → a ≠ 1 →
      ∃ t : Equiv.Perm (Fin 3),
        ¬ (a * (t*a*t⁻¹) = (t*a*t⁻¹) * a) ∧ (a*(t*a*t⁻¹))^3 = 1 ∧
        a*(t*a*t⁻¹) ≠ 1 ∧ ∀ d,
        d = 1 ∨ d = a ∨ d = t*a*t⁻¹ ∨ d = a*(t*a*t⁻¹) ∨
        d = (t*a*t⁻¹)*a ∨ d = a*(t*a*t⁻¹)*a := by decide +kernel
  exact h a ha ha1

private theorem pair_image_conjugate {H B : Type*} [Group H] [Group B]
    (V : Subgroup H) (f : H →* B) (g : H) :
    (V.map (MulAut.conj g).toMonoidHom).map f =
      (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext v
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

private theorem pair_image_commute {H B : Type*} [Group H] [Group B]
    (V W : Subgroup H) (f : H →* B) (hn : V ≤ normalizer (W : Set H))
    (hc : Nat.card (W.map f) = 2)
    {a b : B} (ha : a ∈ V.map f) (hb : b ∈ W.map f) : Commute a b := by
  apply Commute.symm
  apply normalizer_le_centralizer_of_card_two _ hc ?_ b hb
  obtain ⟨v, hv, rfl⟩ := ha
  exact W.le_normalizer_map f (mem_map_of_mem _ (hn hv))

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The natural actor is the actual symmetric-three quotient. -/
theorem LocalAnalysis.equality_actor_symmetricThree
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nonempty (EqualityActor z ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e, _⟩ := A.equality_natural_action h611 hnatural hz horder hTH hbranch
  exact ⟨(Subgroup.topEquiv.symm.trans e).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree⟩

/-- Two actual conjugate layers generate the canonical normal closure. -/
theorem LocalAnalysis.equality_canonical_pair
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ g : G, g ∈ centralizer ({z} : Set G) ∧ g ∉ M ∧
      (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype =
        layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom ∧
      (layer L R ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
        (layer L R) = 2 ∧
      ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 ∧
      ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let V := layer L R
  let VH := V.subgroupOf H
  let Q := pCore 2 H
  let q : H →* EqualityActor z := QuotientGroup.mk' Q
  obtain ⟨e⟩ := A.equality_actor_symmetricThree h611 hnatural hz horder hTH hbranch
  let f : H →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hVH : V ≤ H := layer_le_involution_centralizer h611 hz
  have hcard : Nat.card (VH.map f) = 2 := by
    rw [← map_map, card_map_of_injective e.injective]
    exact A.equalityActorImage_card h611 hnatural hz
  obtain ⟨aH, haH, _⟩ := (Nat.card_eq_two_iff' (1 : VH.map f)).mp hcard
  let a : Equiv.Perm (Fin 3) := aH
  have ha : a ∈ VH.map f := aH.property
  have ha1 : a ≠ 1 := fun he => haH (Subtype.ext he)
  have ha2 : a^2 = 1 := by
    have hh := pow_card_eq_one' (x := aH)
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  obtain ⟨t, hnc, hpow, hne, henum⟩ := symmetricThree_pair a ha2 ha1
  obtain ⟨g, hg⟩ := hf t
  let W := V.map (MulAut.conj (g : G)).toMonoidHom
  let WH := VH.map (MulAut.conj g).toMonoidHom
  let J := VH ⊔ WH
  have hWH : WH = W.subgroupOf H := Subgroup.conj_smul_subgroupOf hVH g
  have hWHmap : WH.map H.subtype = W := by
    rw [hWH, map_subgroupOf_eq_of_le]
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hVH hv)) (H.inv_mem g.property)
  have hJmap : J.map H.subtype = V ⊔ W := by
    rw [Subgroup.map_sup, hWHmap, map_subgroupOf_eq_of_le hVH]
  have hWcard : Nat.card (WH.map f) = 2 := by
    rw [pair_image_conjugate, card_map_of_injective (MulAut.conj (f g)).injective, hcard]
  have hb : t*a*t⁻¹ ∈ WH.map f := by
    rw [pair_image_conjugate, hg]
    exact mem_map_of_mem _ ha
  have hnonleftH : ¬ VH ≤ normalizer (WH : Set H) :=
    fun hh => hnc (pair_image_commute VH WH f hh hWcard ha hb)
  have hnonrightH : ¬ WH ≤ normalizer (VH : Set H) :=
    fun hh => hnc (pair_image_commute WH VH f hh hcard hb ha).symm
  have hnonleft : ¬ V ≤ normalizer (W : Set G) := by
    intro hh
    apply hnonleftH
    rw [hWH]
    exact (subgroupOf_mono H hh).trans (W.le_normalizer_comap H.subtype)
  have hnonright : ¬ W ≤ normalizer (V : Set G) := by
    intro hh
    apply hnonrightH
    rw [hWH]
    exact (subgroupOf_mono H hh).trans (V.le_normalizer_comap H.subtype)
  have himage : J.map f = ⊤ := by
    apply top_unique
    intro d _
    have hja := map_mono (f := f) (show VH ≤ J from le_sup_left) ha
    have hjb := map_mono (f := f) (show WH ≤ J from le_sup_right) hb
    rcases henum d with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hja
    · exact hjb
    · exact mul_mem hja hjb
    · exact mul_mem hjb hja
    · exact mul_mem (mul_mem hja hjb) hja
  have hQJ : Q ≤ normalizer (J : Set H) := by
    apply le_trans (le_inf ?_ ?_) (VH.normalizer_inf_normalizer_le_normalizer_sup WH)
    · intro x hx
      exact V.le_normalizer_comap H.subtype
        (A.equalityCoreH_normalizes_layer h611 hz (mem_map_of_mem H.subtype hx))
    · rw [hWH]
      intro x hx
      exact W.le_normalizer_comap H.subtype
        (A.equalityCoreH_normalizes_conjugate h611 hz g g.property (mem_map_of_mem H.subtype hx))
  have hJQ : J ⊔ Q = ⊤ := by
    have hjq : J.map q = ⊤ := by
      apply (map_injective (f := e.toMonoidHom) e.injective)
      rw [Subgroup.map_top_of_surjective _ e.surjective, map_map]
      exact himage
    have hh := congrArg (comap q) hjq
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  let : J.Normal := normalizer_eq_top_iff.mp (top_unique (hJQ ▸ sup_le J.le_normalizer hQJ))
  have hKJ : equalityLayerClosure L R z = J := by
    apply le_antisymm (normalClosure_le_normal (show VH ≤ J from le_sup_left))
    apply sup_le (show VH ≤ equalityLayerClosure L R z from le_normalClosure)
    rintro _ ⟨v, hv, rfl⟩
    exact (inferInstance : (equalityLayerClosure L R z).Normal).conj_mem v (le_normalClosure hv) g
  have hgM : (g : G) ∉ M := by
    intro hm
    have hnorm : (g : G) ∈ normalizer (V : Set G) := by
      have hh : (g : G) ∈ H ⊓ M := ⟨g.property, hm⟩
      rw [← A.layer_normalizer] at hh
      exact hh.2
    have hW : W = V := mem_normalizer_iff_map_conj_eq.mp hnorm
    exact hnonleft (hW ▸ V.le_normalizer)
  have hn : ¬ IsPGroup 2 (V ⊔ W : Subgroup G) := by
    intro hp
    have hpJ : IsPGroup 2 J := by
      have hh := hp.comap_subtype (K := H)
      rwa [← hJmap, comap_map_eq_self_of_injective H.subtype_injective] at hh
    have hpS := hpJ.map f
    rw [himage] at hpS
    have hs : IsPGroup 2 (Equiv.Perm (Fin 3)) := hpS.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := hs.exists_orderOf_dvd_pow (a*(t*a*t⁻¹))
    rw [orderOf_eq_prime_iff.mpr ⟨hpow, hne⟩] at hk
    have hh := Nat.prime_three.dvd_of_dvd_pow hk
    norm_num at hh
  exact ⟨g, g.property, hgM, by rw [hKJ]; exact hJmap,
    A.equality_pair_normalizer_relIndex h611 hnatural hz g g.property hnonleft,
    A.equality_pair_normalizer_relIndex_right h611 hnatural hz g g.property hnonright, hn⟩

/-- The normal closure of the plane lies in the core of the canonical pair. -/
theorem LocalAnalysis.equalityClosure_le_equalityCore
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    equalityClosure (T : Subgroup G) L R z ≤ equalityCore L R z := by
  let H := centralizer ({z} : Set G)
  let U := equalityClosure (T : Subgroup G) L R z
  have hUQ : U ≤ pCore 2 H := by
    intro u hu
    have hh := A.closure_le_core (show (u : G) ∈ sourceClosure (T : Subgroup G) L R z from
      ⟨u, hu, rfl⟩)
    obtain ⟨v, hv, he⟩ := hh
    exact (Subtype.ext he : v = u) ▸ hv
  have hUK : U ≤ equalityLayerClosure L R z := by
    apply normalClosure_le_normal
    exact (subgroupOf_mono H ((ZS_le_sourceClosure_intersection h611 hz).trans inf_le_right)).trans
      le_normalClosure
  exact le_pCoreIn_of_normalizes (pCore_isPGroup.to_le hUQ) hUK
    (by rw [normalizer_eq_top]; exact le_top)

/-- The actual plane and central involution lie in the canonical core. -/
theorem LocalAnalysis.equalityPlane_le_equalityCore
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    equalityPlane (T : Subgroup G) L R z ≤ equalityCore L R z :=
  (sourceEight_contains _).trans (A.equalityClosure_le_equalityCore h611 hz)

/-- The center of the extraspecial core is the distinguished involution line. -/
theorem LocalAnalysis.equalityCore_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hd : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    coreCenter (equalityCore L R z) = equalityLine z := by
  have hline : equalityLine z ≤ equalityCore L R z :=
    (subgroupOf_mono _ (zpowers_le.mpr hz)).trans (A.equalityPlane_le_equalityCore h611 hz)
  have hle : equalityLine z ≤ coreCenter (equalityCore L R z) := by
    intro x hx
    refine ⟨⟨x, hline hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (equalityLine_le_center z hx) y)
  have hc : Nat.card (coreCenter (equalityCore L R z)) = 2 := by
    rw [coreCenter, card_map_of_injective (equalityCore L R z).subtype_injective]
    exact hd.some.center_card
  have hl : Nat.card (equalityLine z) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show zpowers z ≤ centralizer ({z} : Set G) from
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (Commute.refl z).eq))).toEquiv,
      Nat.card_zpowers, horder]
  exact (eq_of_le_of_card_ge hle (by rw [hc, hl])).symm

/-- The two-conjugate theorem supplies the intrinsic pair, its core and its residual. -/
theorem LocalAnalysis.equality_canonical_pair_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    (∃ g : G, g ∈ centralizer ({z} : Set G) ∧ g ∉ M ∧
      (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype =
        layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom ∧
      (layer L R ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
        (layer L R) = 2 ∧
      ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 ∧
      layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom =
        (coreCenter (equalityCore L R z)).map (centralizer ({z} : Set G)).subtype) ∧
    Nonempty (((equalityLayerClosure L R z) ⧸ pCore 2 (equalityLayerClosure L R z))
      ≃* Equiv.Perm (Fin 3)) ∧
    Nonempty (QuaternionCentralProductData (equalityCore L R z)) ∧
    pCore 2 (equalityLayerClosure L R z) ≤ pResidual 2 (equalityLayerClosure L R z) := by
  obtain ⟨g, hg, hgM, hjoin, hl, hr, hn⟩ :=
    A.equality_canonical_pair h611 hnatural hz horder hTH hbranch
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let J := layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom
  obtain ⟨⟨d⟩, ⟨e⟩, hres, hinter⟩ := A.non_two_pair g hl hr hn
  let ek : K ≃* J := (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hjoin)
  have hcore : (pCore 2 K).map ek.toMonoidHom = pCore 2 J := pCore_map_iso 2 ek
  let ep : pCore 2 K ≃* pCore 2 J := (ek.subgroupMap _).trans (MulEquiv.subgroupCongr hcore)
  let eP : pCore 2 K ≃* equalityCore L R z :=
    (pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective
  have hd : Nonempty (QuaternionCentralProductData (equalityCore L R z)) :=
    ⟨d.map (ep.symm.trans eP)⟩
  have hPmap : (equalityCore L R z).map H.subtype = J.pCoreIn 2 := by
    rw [equalityCore, map_pCoreIn_of_injective 2 K H.subtype H.subtype_injective, hjoin]
  have hcenter : (coreCenter (equalityCore L R z)).map H.subtype =
      ((center (pCore 2 J)).map (pCore 2 J).subtype).map J.subtype := by
    rw [coreCenter, map_embeddedCenter _ _ H.subtype_injective,
      hPmap, map_embeddedCenter _ _ J.subtype_injective]
    rfl
  refine ⟨⟨g, hg, hgM, hjoin, hl, hr, hinter.trans hcenter.symm⟩,
    ⟨(QuotientGroup.congr _ _ ek hcore).trans e⟩, hd, ?_⟩
  apply (map_le_map_iff_of_injective (f := ek.toMonoidHom) ek.injective).mp
  rw [hcore, map_pResidual_of_surjective 2 ek.toMonoidHom ek.surjective]
  exact hres

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
