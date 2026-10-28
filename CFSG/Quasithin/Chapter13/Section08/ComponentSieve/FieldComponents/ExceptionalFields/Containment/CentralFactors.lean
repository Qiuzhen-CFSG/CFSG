module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.Construction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.BorelAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.MarkedNine

/-!
# The two exceptional central factors in the PSL₂(4) branch

This proves the contradiction in the explicit reduced noncontainment branch
of Aschbacher–Smith 13.8.20 (combined manuscript of 1 March 2004, printed
p.955). The actual Borel and PSL₂(4) ≃ A₅ comparison place the constructed
relative centralizer in L₁*. Noncontainment makes its residual lift nontrivial;
the noncentral Borel makes that lift proper. The genuine marked E₉ action
then identifies it with L₀ or X = L₁,+, retaining both coordinates of
K*L₁* = K* × L_C*.

The Sylow arrangement supplies O₂(H)-normalization of L₀. Its centralization
therefore puts K in N_G(L₀) ≤ M, a contradiction. For X, the Borel calculation
and [L₀,t] ≤ O₂(L₀) make t* inner. Relative normality kills the inversion
error, and correction by an element of K* constructs the inverter in
C_{H*}(K*). Thus every clause of external-X alternative (a) holds, contrary
to its failure; the actor calculation also contradicts alternative (b).

The reduced triple-cover premises retain the actual quotient
L₁/O₂(L₁) ≃ C₃ × C₃ and its prescribed cubic residuals. The parent supplies
these markings, the standing/Borel data and failure of (a); this module
proves their PSL₂(4) contradiction without asserting the separate reduction
or unitary exclusion. Compare Notation 13.2.1 and 13.2.2(3),(9), printed
pp.877–878, and the two-perfect formulation in 13.7.5(7), printed p.938.
-/

open Subgroup
open scoped commutatorElement
open Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
open CFSG.Quasithin.Chapter13.Section08
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors

/-- The L₀ case: the Sylow arrangement supplies O₂(H)-normalization.
Only the source bound N_G(L₀) ≤ M is used. -/
public theorem exclude_zero_factor {G : Type*} [Group G] (H K C M T : Subgroup G)
    (hKH : K ≤ H) (hCH : C ≤ H) (hKM : ¬ K ≤ M)
    (hC : IsPPerfect 2 C) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (hTC : T ≤ normalizer (C : Set G))
    (hNM : normalizer (C : Set G) ≤ M)
    (hstar : Source.starImage H K ≤ centralizer (Source.starImage H C : Set (Source.Hstar H))) :
    False := by
  have hQ : Source.QH H ≤ T := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  exact ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting.central_factor_exclusion
    H K C M hKH hCH hKM hC (hQ.trans hTC) hNM hstar

variable {G : Type*} [Group G]

/-- The literal external-X alternative on printed p.954. -/
@[expose] public def ExternalXAlternative (H K X : Subgroup G) : Prop :=
  X ≤ H ∧ ¬ X ≤ K ∧
    Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
    (X.subgroupOf H).Normal ∧
    ∃ c ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹

/-- Derive every external-X clause from centralization, an inner actor and
the actual inversion modulo O₂(X). The source case discharges innerness by
its separate A₄ Borel calculation. -/
public theorem external_X_of_inner_action
    (H K L₁ X T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (hH : H = K ⊔ L₁ ⊔ T) (hX : X ≤ L₁)
    (hpX : IsPPerfect 2 X) (hL₁X : L₁ ≤ normalizer (X : Set G))
    (hTX : T ≤ normalizer (X : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hXC : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hne : Source.starImage H X ≠ ⊥) (t : H)
    (hinner : (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) t) :
      MulAut (Source.starImage H K)) ∈ MulAut.innerSubgroup (Source.starImage H K))
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2) :
    ExternalXAlternative H K X := by
  have hKH : K ≤ H := by rw [hH]; exact le_sup_left.trans le_sup_left
  have hL₁H : L₁ ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_left
  have hXH := hX.trans hL₁H
  have hQ : Source.QH H ≤ T := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  have hKX := Lifting.normalizes_of_star_centralizing H K X hKH hXH hpX
    (hQ.trans hTX) (le_centralizer_iff.mp hXC)
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hH]
    exact sup_le (sup_le hKX hL₁X) hTX
  obtain ⟨hout, hn, hc⟩ := external_configuration_of_star_inversion H K L₁ X T eK
    hH hX hpX hL₁X hTX S hS hXC hne (QuotientGroup.mk' (pCore 2 H) t)
    hinner (star_inverts_of_core_error H X hXH hHX t hinv)
  exact ⟨hXH, hout, hXC, hn, hc⟩

private theorem disjoint_five (K : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 5)) :
    Disjoint K (centralizer (K : Set G)) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hz : eK ⟨x, hx.1⟩ ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨k, rfl⟩ := eK.surjective a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp hx.2) k k.property)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact congrArg Subtype.val (eK.injective (hz.trans eK.map_one.symm))

private theorem borel_not_centralizing (K : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 5)) (P : Sylow 2 K) :
    ¬ borel K P ≤ centralizer (K : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite K := Finite.of_equiv (alternatingGroup (Fin 5)) eK.symm.toEquiv
  intro hc
  have hbot : borel K P = ⊥ := le_bot_iff.mp
    ((le_inf (map_subtype_le _) hc).trans (disjoint_iff_inf_le.mp (disjoint_five K eK)))
  have hP : (P : Subgroup K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h : x.val ∈ borel K P := mem_map.mpr ⟨x, le_normalizer hx, rfl⟩
    rw [hbot, mem_bot] at h
    exact Subtype.ext h
  exact P.ne_bot_of_dvd_card (by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]) hP

private theorem centralizer_ne_bot_of_noncontainment
    (H K D : Subgroup G) [(K.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hDH : D ≤ H) (hK : IsPPerfect 2 K) (hD : IsPPerfect 2 D)
    (hne : ¬ D ≤ K)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    starCentralizer H K D ≠ ⊥ := by
  intro hbot
  apply hne
  apply le_of_star_le H K D hKH hDH hK hD
  intro d hd
  have hi := linear_two_four_inner_action H K D hDH hD hF eK ⟨d, hd⟩
  have hmem : d ∈ Source.starImage H K ⊔
      centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
    rw [← MulAut.conjNormal_comap_innerSubgroup]
    exact hi
  obtain ⟨k, hk, c, hc, hkc⟩ := mem_sup_of_normal_left.mp hmem
  have hcj : c ∈ Source.starImage H K ⊔ Source.starImage H D := by
    have he : c = k⁻¹ * d := by rw [← hkc]; group
    rw [he]
    exact (Source.starImage H K ⊔ Source.starImage H D).mul_mem
      (mem_sup_left ((Source.starImage H K).inv_mem hk)) (mem_sup_right hd)
  have hc1 : c = 1 := by
    have : c ∈ starCentralizer H K D := ⟨hcj, hc⟩
    rwa [hbot, mem_bot] at this
  simpa only [← hkc, hc1, mul_one] using hk

private theorem core_le_sylow_of_normalizes (H D T : Subgroup G)
    (hDH : D ≤ H) (hTH : T ≤ H) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (hTD : T ≤ normalizer (D : Set G)) : D.pCoreIn 2 ≤ T := by
  have hTQ : T ≤ normalizer (D.pCoreIn 2 : Set G) :=
    hTD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hT : IsPGroup 2 T := hS ▸ S.isPGroup'.map H.subtype
  have hJ : IsPGroup 2 (D.pCoreIn 2 ⊔ T : Subgroup G) :=
    (isPGroup_pCoreIn 2 D).to_sup_of_normal_left' hT hTQ
  have hJH : D.pCoreIn 2 ⊔ T ≤ H := sup_le ((pCoreIn_le 2 D).trans hDH) hTH
  have hSle : (S : Subgroup H) ≤ (D.pCoreIn 2 ⊔ T).subgroupOf H := by
    intro s hs
    exact mem_sup_right (hS ▸ mem_map.mpr ⟨s, hs, rfl⟩)
  have he := S.is_maximal' (hJ.of_equiv (subgroupOfEquivOfLe hJH).symm) hSle
  have he' := congrArg (Subgroup.map H.subtype) he
  rw [map_subgroupOf_eq_of_le hJH, hS] at he'
  exact le_sup_left.trans_eq he'

private theorem star_sup (H A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
  unfold Source.starImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem marked_quotient_action (D A B T : Subgroup G)
    (e : D ⧸ pCore 2 D ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hgen : A ⊔ B = D) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hQT : D.pCoreIn 2 ≤ T)
    (hTA : T ≤ normalizer (A : Set G)) (hTB : T ≤ normalizer (B : Set G))
    (t : normalizer (D : Set G))
    (hcomm : ⁅A, zpowers t.val⁆ ≤ A.pCoreIn 2)
    (hinv : ∀ b ∈ B, t.val * b * t.val⁻¹ * b ∈ B.pCoreIn 2) :
    (∀ a : D, a.val ∈ A →
      QuotientGroup.mk' (pCore 2 D) (D.normalizerMonoidHom t a) =
        QuotientGroup.mk' (pCore 2 D) a) ∧
    (∀ b : D, b.val ∈ B →
      QuotientGroup.mk' (pCore 2 D) (D.normalizerMonoidHom t b) =
        (QuotientGroup.mk' (pCore 2 D) b)⁻¹) := by
  have hAD : A ≤ D := le_sup_left.trans_eq hgen
  have hBD : B ≤ D := le_sup_right.trans_eq hgen
  obtain ⟨hnA, hnB⟩ := MarkedNine.marked_normal D A B e hgen hA hB
    (hQT.trans hTA) (hQT.trans hTB)
  let := hnA
  let := hnB
  have hcA : A.pCoreIn 2 ≤ D.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hAD (le_normalizer_of_normal_subgroupOf hAD)
  have hcB : B.pCoreIn 2 ≤ D.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hBD (le_normalizer_of_normal_subgroupOf hBD)
  constructor
  · intro a ha
    apply (QuotientGroup.eq_iff_div_mem).mpr
    have hc : t.val * a.val * t.val⁻¹ * a.val⁻¹ ∈ D.pCoreIn 2 := by
      apply hcA
      have hx := (A.pCoreIn 2).inv_mem
        (hcomm (commutator_mem_commutator ha (mem_zpowers t.val)))
      simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc] using hx
    obtain ⟨z, hz, he⟩ := hc
    have he' : z = D.normalizerMonoidHom t a / a := Subtype.ext (by
      simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        normalizerMonoidHom_apply_apply_coe]
      exact he)
    exact he' ▸ hz
  · intro b hb
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨z, hz, he⟩ := hcB (hinv b.val hb)
    have he' : z = D.normalizerMonoidHom t b * b := Subtype.ext he
    exact he' ▸ hz

private theorem normalizes_borel_of_sylow_marking (K T : Subgroup G) [K.Normal]
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = T ⊓ K) :
    T ≤ normalizer (borel K P : Set G) := by
  let R := (P : Subgroup K).map K.subtype
  have hRK : R ≤ K := map_subtype_le _
  have hRsub : R.subgroupOf K = (P : Subgroup K) := by
    exact comap_map_eq_self_of_injective K.subtype_injective _
  have hB : borel K P = normalizer (R : Set G) ⊓ K := by
    change (normalizer ((P : Subgroup K) : Set K)).map K.subtype = _
    rw [← hRsub, ← subgroupOf_normalizer_eq hRK, subgroupOf_map_subtype]
  have hTR : T ≤ normalizer (R : Set G) := by
    rw [show R = T ⊓ K from hP]
    exact (le_inf le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  rw [hB]
  exact (le_inf (hTR.trans le_normalizer) le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf

/-- Construct and identify the central factor from the actual Borel and the
marked elementary-nine quotient. In particular, nontriviality and properness
are proved, not included among the inputs. Both coordinates of the resulting
internal direct product are marked by their original embedded subgroups. -/
public theorem linear_two_four_marked_factors [Finite G]
    (H K L₁ L₀ X T : Subgroup G)
    [(K.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hL₁H : L₁ ≤ H) (hTH : T ≤ H)
    (hK : IsPPerfect 2 K) (h₁ : IsPPerfect 2 L₁)
    (h₀ : IsPPerfect 2 L₀) (hX : IsPPerfect 2 X)
    (hgen : L₀ ⊔ X = L₁) (hne : ¬ L₁ ≤ K)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hT₀ : T ≤ normalizer (L₀ : Set G)) (hTX : T ≤ normalizer (X : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H L₁)
    (hDN : Source.starImage H L₁ ≤
      normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H)))
    (e₉ : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hc₀ : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (hcX : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (t : H) (ht : t.val ∈ T)
    (hcomm : ⁅L₀, zpowers t.val⁆ ≤ L₀.pCoreIn 2)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2) :
    let C := centralFactor H K L₁
    (C = L₀ ∨ C = X) ∧ IsPPerfect 2 C ∧ T ≤ normalizer (C : Set G) ∧
      Source.starImage H C = starCentralizer H K L₁ ∧
      Source.starImage H C ≠ ⊥ ∧ C ≠ L₁ ∧
      ∃ e : (Source.starImage H K ⊔ Source.starImage H L₁ : Subgroup (Source.Hstar H)) ≃*
          Source.starImage H K × Source.starImage H C,
        ((Source.starImage H K).subgroupOf (Source.starImage H K ⊔ Source.starImage H L₁)).map
          e.toMonoidHom = (⊤ : Subgroup (Source.starImage H K)).prod ⊥ ∧
        ((Source.starImage H C).subgroupOf (Source.starImage H K ⊔ Source.starImage H L₁)).map
          e.toMonoidHom = (⊥ : Subgroup (Source.starImage H K)).prod ⊤ := by
  dsimp only
  have hTD : T ≤ normalizer (L₁ : Set G) := by
    rw [← hgen]
    exact (le_inf hT₀ hTX).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQT := core_le_sylow_of_normalizes H L₁ T hL₁H hTH S hS hTD
  let tn : normalizer (L₁ : Set G) := ⟨t.val, hTD ht⟩
  obtain ⟨hfix, hinvert⟩ := marked_quotient_action L₁ L₀ X T e₉ hgen h₀ hX
    hQT hT₀ hTX tn hcomm hinv
  have himage := linear_two_four_borel_centralFactor_starImage H K L₁ hL₁H h₁ hF eK P hBD hDN
  have hstarne := centralizer_ne_bot_of_noncontainment H K L₁ hKH hL₁H hK h₁ hne hF eK
  have hCne : centralFactor H K L₁ ≠ ⊥ := by
    intro he
    apply hstarne
    rw [← himage, he]
    simp [Source.starImage]
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hproper : centralFactor H K L₁ ≠ L₁ := by
    intro he
    have hDC : Source.starImage H L₁ ≤
        centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
      rw [← he, himage]
      exact inf_le_right
    exact borel_not_centralizing _ (eK.trans e₅) P (hBD.trans hDC)
  have hcases := MarkedNine.centralFactor_eq_L0_or_X H K L₁ L₀ X T e₉ hgen
    hL₁H hTH h₁ h₀ hX (hQT.trans hT₀) (hQT.trans hTX) hQT hTD hc₀ hcX
    tn ht hfix hinvert hCne hproper
  refine ⟨hcases, centralFactor_isPPerfect H K L₁,
    centralFactor_T_invariant H K L₁ T hL₁H hTH hTD, himage,
    himage ▸ hstarne, hproper, ?_⟩
  obtain ⟨e, heK, heC, _⟩ := linear_two_four_centralizer_product H K L₁ hL₁H h₁ hF eK
  rw [himage]
  exact ⟨e, heK, heC⟩

/-- After the L₀ normalizer exclusion, reduced noncontainment would force
all clauses of external-X alternative (a), and would make the prescribed
actor inner. Thus either the failure of (a) or the outer-action clause of (b)
excludes this branch. The source marking X = L₁,+ is carried by the two
cubic quotient images and the fixing/inverting action, not by a family tag. -/
public theorem linear_two_four_external_X_and_inner [Finite G]
    (H K L₁ L₀ X T M : Subgroup G)
    [(K.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    (hH : H = K ⊔ L₁ ⊔ T) (hKM : ¬ K ≤ M)
    (hNM : normalizer (L₀ : Set G) ≤ M)
    (hK : IsPPerfect 2 K) (h₁ : IsPPerfect 2 L₁)
    (h₀ : IsPPerfect 2 L₀) (hX : IsPPerfect 2 X)
    (hgen : L₀ ⊔ X = L₁) (hne : ¬ L₁ ≤ K)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hT₀ : T ≤ normalizer (L₀ : Set G)) (hTX : T ≤ normalizer (X : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hP : (P : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H T ⊓ Source.starImage H K)
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H L₁)
    (hDN : Source.starImage H L₁ ≤
      normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H)))
    (e₉ : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hc₀ : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (hcX : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (t : H) (ht : t.val ∈ T)
    (hcomm : ⁅L₀, zpowers t.val⁆ ≤ L₀.pCoreIn 2)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2) :
    ExternalXAlternative H K X ∧
      (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) t) :
        MulAut (Source.starImage H K)) ∈ MulAut.innerSubgroup (Source.starImage H K) := by
  have hKH : K ≤ H := by rw [hH]; exact le_sup_left.trans le_sup_left
  have hL₁H : L₁ ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_left
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right
  have h₀le : L₀ ≤ L₁ := le_sup_left.trans_eq hgen
  have hXle : X ≤ L₁ := le_sup_right.trans_eq hgen
  obtain ⟨hcases, _, _, himage, hstarne, _, _⟩ := linear_two_four_marked_factors
    H K L₁ L₀ X T hKH hL₁H hTH hK h₁ h₀ hX hgen hne S hS hT₀ hTX
    hF eK P hBD hDN e₉ hc₀ hcX t ht hcomm hinv
  have hcentral : Source.starImage H (centralFactor H K L₁) ≤
      centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
    rw [himage]
    exact inf_le_right
  rcases hcases with hzero | hplus
  · rw [hzero] at hcentral
    exact (exclude_zero_factor H K L₀ M T hKH (h₀le.trans hL₁H) hKM h₀ S hS
      hT₀ hNM (le_centralizer_iff.mp hcentral)).elim
  · rw [hplus] at hcentral hstarne
    have hXimage : (Source.starImage H X).map
        (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H K)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, MulAut.conjNormal_ker_eq_centralizer]
      exact hcentral
    have h₀image := linear_two_four_borel_action H K L₁ hL₁H h₁ hF eK P hBD hDN
    rw [← hgen, star_sup H L₀ X (h₀le.trans hL₁H) (hXle.trans hL₁H),
      Subgroup.map_sup, hXimage, sup_bot_eq] at h₀image
    have htB := normalizes_borel_of_sylow_marking (Source.starImage H K)
      (Source.starImage H T) P hP
      (mem_map.mpr ⟨t, ht, rfl⟩)
    have hinner := linear_two_four_L₀_actor_inner H K L₀ (h₀le.trans hL₁H)
      hF eK P t h₀image htB hcomm
    have hTD : T ≤ normalizer (L₁ : Set G) := by
      rw [← hgen]
      exact (le_inf hT₀ hTX).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hQT := core_le_sylow_of_normalizes H L₁ T hL₁H hTH S hS hTD
    obtain ⟨_, hnX⟩ := MarkedNine.marked_normal L₁ L₀ X e₉ hgen h₀ hX
      (hQT.trans hT₀) (hQT.trans hTX)
    let := hnX
    obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    exact ⟨external_X_of_inner_action H K L₁ X T (eK.trans e₅) hH hXle hX
      (le_normalizer_of_normal_subgroupOf hXle) hTX S hS hcentral hstarne t hinner hinv,
      hinner⟩


/-- The PSL₂(4) contradiction in the explicit reduced triple-cover branch
of 13.8.20. The E₉ quotient, its marked cubic residuals, the Borel placement,
and the source commutator/inversion data are the reduced premises. The
preceding theorem constructs the central factor and all external-X clauses.
The outer-action clause is retained from alternative (b); the constructed
external-X configuration already contradicts the failure of alternative (a). -/
public theorem linear_two_four_noncontainment_contradiction [Finite G]
    (H K L₁ L₀ X T M : Subgroup G)
    [(K.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    (hH : H = K ⊔ L₁ ⊔ T) (hKM : ¬ K ≤ M)
    (hNM : normalizer (L₀ : Set G) ≤ M)
    (hK : IsPPerfect 2 K) (h₁ : IsPPerfect 2 L₁)
    (h₀ : IsPPerfect 2 L₀) (hX : IsPPerfect 2 X)
    (hgen : L₀ ⊔ X = L₁) (hne : ¬ L₁ ≤ K)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hT₀ : T ≤ normalizer (L₀ : Set G)) (hTX : T ≤ normalizer (X : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hP : (P : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H T ⊓ Source.starImage H K)
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H L₁)
    (hDN : Source.starImage H L₁ ≤
      normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H)))
    (e₉ : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
    (hc₀ : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (hcX : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3)
    (t : H) (ht : t.val ∈ T)
    (hcomm : ⁅L₀, zpowers t.val⁆ ≤ L₀.pCoreIn 2)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2)
    (_houter : (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) t) :
      MulAut (Source.starImage H K)) ∉ MulAut.innerSubgroup (Source.starImage H K))
    (hfailure : ¬ ExternalXAlternative H K X) : False := by
  exact hfailure (linear_two_four_external_X_and_inner H K L₁ L₀ X T M hH hKM hNM
    hK h₁ h₀ hX hgen hne S hS hT₀ hTX hF eK P hP hBD hDN e₉ hc₀ hcX
    t ht hcomm hinv).1


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors
