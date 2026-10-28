module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Core
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Thompson
public import Theory.Frattini.BinarySquares

/-!
# The Frattini and residual-commutator steps of the temporary action

The elementary image of the original Sylow subgroup on V kills squares,
and hence the Frattini subgroup of ⟨τ,Q⟩. Commutation modulo Q makes the
marked centralizer factor normalize this generated subgroup. Its characteristic
Frattini subgroup then centralizes the whole conjugate span U.

Separately, normality of Y and the two-core Q places [Y,Q] in O₂(Y).
The identity O₂(Y) = C_Y(V) therefore propagates to centralization of U.
Every local application uses the original lineV and the temporaryCore;
no equality with the original lineQ is imposed. The source action hypotheses
and the marked centralizer-span witness remain explicit.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
variable {G K : Type*} [Group G] [Group K]

/-- Propagation from the seed to its conjugate span. -/
theorem centralizes_span (V C N : Subgroup G)
    (hN : C ≤ normalizer (N : Set G)) (hV : N ≤ centralizer (V : Set G)) :
    N ≤ centralizer (conjugateSpanBy V C : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨c, hc, v, hv, rfl⟩ n hn
  have hn' : c⁻¹ * n * c ∈ N := by
    simpa only [inv_inv, SetLike.mem_coe] using (hN (C.inv_mem hc) n).mp hn
  have he := congrArg (MulAut.conj c) (hV hn' v hv)
  change n * (c * v * c⁻¹) = (c * v * c⁻¹) * n
  simp only [map_mul, MulAut.conj_apply] at he
  convert he.symm using 1 <;> group

/-- Commutation modulo the normal core normalizes the subgroup generated with it. -/
theorem normalizes_join (Q C : Subgroup G) (t : G)
    (hCQ : C ≤ normalizer (Q : Set G))
    (hct : ∀ c ∈ C, ⁅c, t⁆ ∈ Q) :
    C ≤ normalizer ((zpowers t ⊔ Q : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro c hc x hx
  have ht : c * t * c⁻¹ ∈ zpowers t ⊔ Q := by
    have h := (zpowers t ⊔ Q).mul_mem (mem_sup_right (hct c hc))
      (mem_sup_left (mem_zpowers t))
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using h
  have hmap : zpowers t ⊔ Q ≤ (zpowers t ⊔ Q).comap (MulAut.conj c).toMonoidHom := by
    refine sup_le (zpowers_le.mpr ht) ?_
    intro q hq
    exact mem_sup_right ((hCQ hc q).mp hq)
  exact hmap hx

/-- The elementary image of the original Sylow action kills the Frattini subgroup. -/
theorem frattini_centralizes_seed [Finite G] (S P V : Subgroup G)
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hSV : S ≤ normalizer (V : Set G))
    (hel : IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion hSV)).range) :
    (frattini P).map P.subtype ≤ centralizer (V : Set G) := by
  let a := V.normalizerMonoidHom.comp (inclusion hSV)
  let _ : IsElementaryAbelian 2 a.range := hel
  rw [map_le_iff_le_comap, (hS.to_le hPS).frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨p, rfl⟩ v hv
  let s : S := ⟨p, hPS p.property⟩
  have hsq : a (s ^ 2) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (A := a.range) (a s) ⟨s, rfl⟩
  have he := congrArg (fun b : MulAut V => (b ⟨v, hv⟩ : G)) hsq
  change (p : G) ^ 2 * v * ((p : G) ^ 2)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The marked centralizer factor propagates the Frattini centralization to all of U. -/
theorem frattini_centralizes_span [Finite G] (S V C Q U : Subgroup G)
    (t : G) (hS : IsPGroup 2 S) (htS : t ∈ S) (hQS : Q ≤ S)
    (hSV : S ≤ normalizer (V : Set G))
    (hel : IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion hSV)).range)
    (hCQ : C ≤ normalizer (Q : Set G))
    (hct : ∀ c ∈ C, ⁅c, t⁆ ∈ Q)
    (hU : U = conjugateSpanBy V C) :
    (frattini (zpowers t ⊔ Q : Subgroup G)).map (zpowers t ⊔ Q).subtype ≤
      centralizer (U : Set G) := by
  let P := zpowers t ⊔ Q
  have hCP : C ≤ normalizer (P : Set G) := normalizes_join Q C t hCQ hct
  have hCF : C ≤ normalizer ((frattini P).map P.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro c hc _ ⟨p, hp, rfl⟩
    let a := P.normalizerMonoidHom ⟨c, hCP hc⟩
    exact ⟨a p, characteristic_iff_le_comap.mp (inferInstance :
      (frattini P).Characteristic) a hp, rfl⟩
  rw [hU]
  exact centralizes_span V C _ hCF (frattini_centralizes_seed S P V hS
    (sup_le (zpowers_le.mpr htS) hQS) hSV hel)

/-- Killing Φ(P) forces trivial Frattini in its faithful image. -/
theorem frattini_image_eq_bot [Finite G] (P : Subgroup G) (hP : IsPGroup 2 P)
    (f : G →* K) (hker : (frattini P).map P.subtype ≤ f.ker) :
    frattini (P.map f) = ⊥ := by
  let _ : Finite (P.map f) := Set.Finite.to_subtype ((Set.toFinite (P : Set G)).image f)
  rw [(hP.map f).frattini_eq_closure_squares]
  apply le_bot_iff.mp
  apply (closure_le _).mpr
  rintro _ ⟨⟨_, p, hp, rfl⟩, rfl⟩
  apply Subtype.ext
  change (f p) ^ 2 = 1
  rw [← map_pow]
  apply hker
  let _ : Fact (IsPGroup 2 P) := ⟨hP⟩
  exact mem_map_of_mem P.subtype
    (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨p, hp⟩ : P))

/-- The faithful image of the generated two-group is elementary abelian. -/
theorem faithful_join_elementary [Finite G] (S V C Q U : Subgroup G)
    (t : G) (hS : IsPGroup 2 S) (htS : t ∈ S) (hQS : Q ≤ S)
    (hSV : S ≤ normalizer (V : Set G))
    (hel : IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion hSV)).range)
    (hCQ : C ≤ normalizer (Q : Set G)) (hct : ∀ c ∈ C, ⁅c, t⁆ ∈ Q)
    (hU : U = conjugateSpanBy V C) (f : G →* K)
    (hker : f.ker = centralizer (U : Set G)) :
    IsElementaryAbelian 2 ((zpowers t ⊔ Q).map f) := by
  let P := zpowers t ⊔ Q
  have hP : IsPGroup 2 P := hS.to_le (sup_le (zpowers_le.mpr htS) hQS)
  let _ : Finite (P.map f) := Set.Finite.to_subtype ((Set.toFinite (P : Set G)).image f)
  let _ : Fact (IsPGroup 2 (P.map f)) := ⟨hP.map f⟩
  apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
  apply frattini_image_eq_bot P hP f
  rw [hker]
  exact frattini_centralizes_span S V C Q U t hS htS hQS hSV hel hCQ hct hU

/-- Simultaneous normalization preserves the actual commutator subgroup. -/
theorem normalizes_commutator (C Y Q : Subgroup G)
    (hY : C ≤ normalizer (Y : Set G)) (hQ : C ≤ normalizer (Q : Set G)) :
    C ≤ normalizer ((⁅Y, Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro c hc x hx
  let a := (MulAut.conj c).toMonoidHom
  have hmY : Y.map a ≤ Y := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hY hc v).mp hv
  have hmQ : Q.map a ≤ Q := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hQ hc v).mp hv
  have hm : (⁅Y, Q⁆).map a ≤ ⁅Y, Q⁆ := by
    rw [map_commutator]
    exact commutator_mono hmY hmQ
  exact hm (mem_map_of_mem a hx)

/-- A normal two-core has two-group commutator with the normal residual. -/
theorem commutator_le_residual_core (H Y Q : Subgroup G)
    (hYH : Y ≤ H) (hQH : Q ≤ H)
    (hY : H ≤ normalizer (Y : Set G)) (hQ : H ≤ normalizer (Q : Set G))
    (hp : IsPGroup 2 Q) : ⁅Y, Q⁆ ≤ Y.pCoreIn 2 := by
  have hCQ : ⁅Y, Q⁆ ≤ Q := le_normalizer_iff_commutator_le_right.mp (hYH.trans hQ)
  have hCY : ⁅Y, Q⁆ ≤ Y := le_normalizer_iff_commutator_le_left.mp (hQH.trans hY)
  exact le_pCoreIn_of_normalizes (hp.to_le hCQ) hCY (normalizer_commutator_ge_left Y Q)

/-- A normal commutator subgroup lying in the seed centralizer fixes the full span. -/
theorem commutator_centralizes_span (V Y Q C U : Subgroup G)
    (hn : C ≤ normalizer ((⁅Y, Q⁆ : Subgroup G) : Set G))
    (hc : ⁅Y, Q⁆ ≤ Y.pCoreIn 2)
    (hcore : Y.pCoreIn 2 ≤ centralizer (V : Set G))
    (hU : U = conjugateSpanBy V C) :
    ⁅Y, Q⁆ ≤ centralizer (U : Set G) := by
  rw [hU]
  exact centralizes_span V C _ hn (hc.trans hcore)

/-- Killing the actual commutator gives commuting action images. -/
theorem image_commutes (Y Q U : Subgroup G) (f : G →* K)
    (hker : f.ker = centralizer (U : Set G))
    (hc : ⁅Y, Q⁆ ≤ centralizer (U : Set G)) :
    Y.map f ≤ centralizer (Q.map f : Set K) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr (hker.symm ▸ hc)

/-- Source Frattini step with the original span and the literal temporary core. -/
theorem temporary_frattini_centralizes_lineV [Finite G]
    (T V E : Subgroup G) [IsMulCommutative V] (hEV : E ≤ V)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (t : G) (ht : t ∈ lineT T E)
    (hTV : lineT T E ≤ normalizer (V : Set G))
    (hel : IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion hTV)).range)
    (hct : ∀ c ∈ temporaryCentralizer T V E, ⁅c, t⁆ ∈ temporaryCore T V E)
    (hspan : lineV V E = conjugateSpanBy V (temporaryCentralizer T V E)) :
    (frattini (zpowers t ⊔ temporaryCore T V E : Subgroup G)).map
      (zpowers t ⊔ temporaryCore T V E).subtype ≤ centralizer (lineV V E : Set G) := by
  have hp : IsPGroup 2 (lineT T E) := hP ▸ P.isPGroup'.map (lineNormalizer E).subtype
  have hn := (normal_subgroupOf_iff_le_normalizer (temporaryCore_le T V E)).mp
    (temporaryCore_normal T V E)
  exact frattini_centralizes_span (lineT T E) V (temporaryCentralizer T V E)
    (temporaryCore T V E) (lineV V E) t hp ht
    (temporaryCore_le_lineT T V E hEV P hP) hTV hel (inf_le_left.trans hn) hct hspan

/-- Source commutator step, retaining the relative normality and original residual. -/
theorem temporary_commutator_centralizes_lineV [Finite G]
    (Y T V E : Subgroup G) [IsMulCommutative V] (hEV : E ≤ V)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hYH : lineY Y E ≤ temporaryLineNormalizer T V E)
    (hY : temporaryLineNormalizer T V E ≤ normalizer (lineY Y E : Set G))
    (hcore : (lineY Y E).pCoreIn 2 ≤ centralizer (V : Set G)) :
    ⁅lineY Y E, temporaryCore T V E⁆ ≤ centralizer (lineV V E : Set G) := by
  have hQ := (normal_subgroupOf_iff_le_normalizer (temporaryCore_le T V E)).mp
    (temporaryCore_normal T V E)
  exact commutator_centralizes_span V (lineY Y E) (temporaryCore T V E)
    (temporaryLineNormalizer T V E) (lineV V E)
    (normalizes_commutator _ _ _ hY hQ)
    (commutator_le_residual_core _ _ _ hYH (temporaryCore_le T V E) hY hQ
      (temporaryCore_isPGroup T V E)) hcore
    (lineV_eq_temporary_span T V E hEV P hP)

/-- The Frattini centralization in the ambient group descends to its actual local action. -/
theorem local_frattini_image_eq_bot [Finite G] (H U P : Subgroup G)
    (hPH : P ≤ H) (hp : IsPGroup 2 P)
    (f : H →* K) (hker : f.ker = centralizer (U.subgroupOf H : Set H))
    (hc : (frattini P).map P.subtype ≤ centralizer (U : Set G)) :
    frattini ((P.subgroupOf H).map f) = ⊥ := by
  apply frattini_image_eq_bot (P.subgroupOf H) (hp.comap_subtype) f
  rw [hker]
  rintro _ ⟨p, hpF, rfl⟩ u hu
  let e := subgroupOfEquivOfLe hPH
  have he : e p ∈ frattini P :=
    frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective hpF
  have h := hc (mem_map_of_mem P.subtype he) (u : G) hu
  exact Subtype.ext h

/-- Trivial Frattini in the literal faithful local image of ⟨τ,Q⟩. -/
theorem temporary_frattini_image_eq_bot [Finite G]
    (T V E : Subgroup G) [IsMulCommutative V] (hEV : E ≤ V)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (t : G) (ht : t ∈ lineT T E)
    (hTV : lineT T E ≤ normalizer (V : Set G))
    (hel : IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion hTV)).range)
    (hct : ∀ c ∈ temporaryCentralizer T V E, ⁅c, t⁆ ∈ temporaryCore T V E)
    (hspan : lineV V E = conjugateSpanBy V (temporaryCentralizer T V E))
    (f : temporaryLineNormalizer T V E →* K)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E))) :
    frattini (((zpowers t ⊔ temporaryCore T V E).subgroupOf
      (temporaryLineNormalizer T V E)).map f) = ⊥ := by
  have hp : IsPGroup 2 (lineT T E) := hP ▸ P.isPGroup'.map (lineNormalizer E).subtype
  have hPS : zpowers t ⊔ temporaryCore T V E ≤ lineT T E :=
    sup_le (zpowers_le.mpr ht) (temporaryCore_le_lineT T V E hEV P hP)
  exact local_frattini_image_eq_bot (temporaryLineNormalizer T V E) (lineV V E)
    (zpowers t ⊔ temporaryCore T V E) (hPS.trans (lineT_le_temporary T V E hEV))
    (hp.to_le hPS) f hker
    (temporary_frattini_centralizes_lineV T V E hEV P hP t ht hTV hel hct hspan)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
