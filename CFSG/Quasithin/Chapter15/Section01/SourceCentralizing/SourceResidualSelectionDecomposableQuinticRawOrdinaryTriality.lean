module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2Local
-- Reuse only the native, record-free factor nonshortness and quasisimple-core lemmas.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Triality

/-! Higher-field triality is excluded on the original ordinary component.
One actual Sylow-compatible marking transports both native parabolic residuals
into the same local family. Their nonshort PSL2 cores have degrees 3n and n;
proved raw placement and native generation contradict original escape. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Triality.Standard Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]

private theorem raw_triality_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (n : ℕ) (hn : 0 < n) (e : L ≃* BinaryCarrier n hn) :
    (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple (centralizer (Z1 : Set G)) := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  let ec : L.subgroupOf (centralizer (Z1 : Set G)) ≃* L := subgroupOfEquivOfLe hLG
  let f := ec.trans e
  have hR : 2 ≤ primeRank 3 (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv 3 f]
    let E := ElementaryNine.subgroup (binaryParameters n hn) rfl
    let : IsElementaryAbelian 3 E := ElementaryNine.subgroup_elementary _ _
    exact IsElementaryAbelian.primeRank_ge_of_card E (ElementaryNine.card_subgroup _ _)
  have hZtwo : IsPGroup 2 (center L) := by
    rw [hcenter]
    exact pCore_isPGroup
  have hZ := hZtwo.of_equiv (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (L.subgroupOf (centralizer (Z1 : Set G))))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

private theorem raw_triality_marked_embedding
    {S L : Subgroup G} (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (n : ℕ) (hn : 0 < n) (e : L ≃* BinaryCarrier n hn) :
    ∃ f : BinaryCarrier n hn →* G, Function.Injective f ∧ f.range = L ∧
      (unipotent (binaryParameters n hn)).map f = S ⊓ L := by
  obtain ⟨Q,hQ⟩ := hSylL
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := binaryParameters n hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) (unipotentSylow P rfl) R
  let c := MulAut.conj g
  let f := L.subtype.comp (e.symm.toMonoidHom.comp c.toMonoidHom)
  refine ⟨f,L.subtype_injective.comp (e.symm.injective.comp c.injective), ?_, ?_⟩
  · rw [MonoidHom.range_comp,(e.symm.toMonoidHom.comp c.toMonoidHom).range_eq_top_of_surjective
      (e.symm.surjective.comp c.surjective),←MonoidHom.range_eq_map,range_subtype]
  · have hc : (unipotent P).map c.toMonoidHom = (R : Subgroup (Carrier P)) := by
      change ((g • unipotentSylow P rfl : Sylow 2 (Carrier P)) : Subgroup (Carrier P)) = _
      rw [hg]
    change (unipotent P).map (L.subtype.comp (e.symm.toMonoidHom.comp c.toMonoidHom)) = _
    rw [←map_map,←map_map,hc]
    change (((Q : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom).map
      L.subtype = _
    have hi : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [map_map (Q : Subgroup L) e.symm.toMonoidHom e.toMonoidHom,hi,map_id]
    exact hQ

omit [Finite G] in
private theorem raw_triality_embedded_invariant
    {S L : Subgroup G}
    {C : Type*} [Group C] (f : C →* G) (hf : Function.Injective f)
    (hr : f.range = L) (U X : Subgroup C) (hU : U.map f = (S ⊓ L))
    (hn : S ≤ normalizer (L : Set G))
    (hinv : ∀ a : MulAut C, U.map a.toMonoidHom = U → X.map a.toMonoidHom = X) :
    S ≤ normalizer (X.map f : Set G) := by
  let e : C ≃* L := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hSL : S ≤ normalizer ((S ⊓ L) : Set G) :=
    (le_inf S.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  intro x hx
  let a : MulAut C := MulAut.congr e.symm (L.normalizerMonoidHom ⟨x,hn hx⟩)
  have he : f.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp f := by
    ext y
    change (e (e.symm (L.normalizerMonoidHom ⟨x,hn hx⟩ (e y))) : G) = _
    rw [e.apply_symm_apply]
    rfl
  have hUa : U.map a.toMonoidHom = U := by
    apply map_injective hf
    rw [map_map,he,←map_map,hU]
    exact mem_normalizer_iff_map_conj_eq.mp (hSL hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (X.map f).map (MulAut.conj x).toMonoidHom = X.map f
  rw [map_map,←he,←map_map,hinv a hUa]

private theorem raw_triality_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (n : ℕ) (hn : 1 < n) (e : L ≃* BinaryCarrier n (Nat.zero_lt_of_lt hn)) :
    ∃ B K : Node → Subgroup G,
      (∀ a, B a ≤ L) ∧
      (∀ a, ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (B a : Set G)) ∧
      (∀ a, (solvableResidual (B a)).map (B a).subtype = K a) ∧
      (∀ a, K a ∈ Chapter1.LIn (centralizer (Z1 : Set G))
        ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) ∧
      (∀ a, generalizedFitting (K a) = pCore 2 (K a)) ∧
      (∀ a, ¬ChapterC.IsShort (K a)) ∧
      (∀ a, ClassicalGroup.IsPSL (K a ⧸ pCore 2 (K a))
        2 (2 ^ (n * (match a with | .arms => 3 | .central => 1)))) ∧
      K .arms ⊔ K .central = L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let P := binaryParameters n (Nat.zero_lt_of_lt hn)
  have hq : 4 ≤ P.q := by
    change 2^2 ≤ 2^n
    exact Nat.pow_le_pow_right (by decide) hn
  have hnL : S ≤ normalizer (L : Set G) := (show S ≤ centralizer (Z1 : Set G) from inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp
      (raw_triality_normal hG T h hZ hZne hLG hL hcenter n (Nat.zero_lt_of_lt hn) e))
  obtain ⟨f,hf,hr,hU⟩ := raw_triality_marked_embedding hSylL n (Nat.zero_lt_of_lt hn) e
  let B := fun a => (parabolic P a).map f
  let K := fun a => (localFactor P a).map f
  have hnB (a : Node) : S ≤ normalizer (B a : Set G) :=
    raw_triality_embedded_invariant f hf hr (unipotent P) (parabolic P a) hU hnL
      (parabolic_map_eq_of_unipotent_invariant P rfl a)
  have hnK (a : Node) : S ≤ normalizer (K a : Set G) :=
    raw_triality_embedded_invariant f hf hr (unipotent P) (localFactor P a) hU hnL
      (localFactor_map_eq_of_unipotent_invariant P rfl a)
  have hKL (a : Node) : K a ≤ L := hr ▸ map_le_range f _
  have hBL (a : Node) : B a ≤ L := hr ▸ map_le_range f _
  let ek (a : Node) : localFactor P a ≃* K a :=
    (localFactor P a).equivMapOfInjective f hf
  let eq (a : Node) : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃*
      (K a ⧸ pCore 2 (K a)) := QuotientGroup.congr _ _ (ek a) (pCore_map_iso 2 (ek a))
  have hfit (a : Node) : generalizedFitting (K a) = pCore 2 (K a) := by
    rw [←map_generalizedFitting_equiv (ek a),←pCore_map_iso 2 (ek a),
      localFactor_generalizedFitting P rfl a]
  have hshort (a : Node) : ¬ ChapterC.IsShort (K a) := fun hs =>
    CaseIComponentData.triality_factor_not_short P rfl (by omega) a (hs.of_mulEquiv (ek a).symm)
  have hfamily (a : Node) : K a ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := by
    let := localFactor_isPerfect P rfl (by omega) a
    let := CaseIComponentData.triality_factor_quasisimple n hn a
    let : Group.IsPerfect (K a) :=
      Group.IsPerfect.ofSurjective (f := (ek a).toMonoidHom) (ek a).surjective
    let : IsQuasisimple (K a ⧸ pCore 2 (K a)) := IsQuasisimple.of_mulEquiv (eq a)
    apply Chapter1.mem_LIn_of_normalized_perfect hSylG
      ((hKL a).trans hLG) (hnK a)
    have hcore : (K a).pCoreIn 2 = (radical P a).map f := by
      change (pCore 2 (K a)).map (K a).subtype = _
      rw [←pCore_map_iso 2 (ek a),map_map]
      change (pCore 2 (localFactor P a)).map (f.comp (localFactor P a).subtype) = _
      rw [←map_map,localFactor_twoCore_map P rfl a]
    rw [hcore]
    intro hb
    have hz : radical P a = ⊥ := (map_eq_bot_iff_of_injective _ hf).mp hb
    apply radical_not_elementary P rfl a
    rw [hz]
    refine { exponent_dvd_p := ?_ }
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun _ => Subsingleton.elim _ _)
  refine ⟨B,K,hBL,hnB,?_,hfamily,hfit,hshort,?_,?_⟩
  · intro a
    let eb := (parabolic P a).equivMapOfInjective f hf
    have he : (B a).subtype.comp eb.toMonoidHom = f.comp (parabolic P a).subtype := rfl
    rw [←map_solvableResidual_eq eb.toMonoidHom eb.surjective,map_map,he,←map_map,
      parabolic_solvableResidual_map P rfl (by omega) a]
  · intro a
    cases a with
    | arms =>
      refine ⟨ExtensionField P,inferInstance,inferInstance,?_,
        ⟨(eq .arms).symm.trans (localFactorArmsQuotientEquivPSL2 P rfl)⟩⟩
      rw [card_extensionField]
      exact (pow_mul 2 n 3).symm
    | central =>
      refine ⟨GaloisField 2 n,inferInstance,inferInstance,?_,
        ⟨(eq .central).symm.trans (localFactorCentralQuotientEquivPSL2 P rfl)⟩⟩
      rw [GaloisField.card 2 n (Nat.ne_of_gt (Nat.zero_lt_of_lt hn)),mul_one]
  · change (localFactor P .arms).map f ⊔ (localFactor P .central).map f = L
    rw [←Subgroup.map_sup,localFactor_sup_eq_top P rfl,←MonoidHom.range_eq_map,hr]

/-- Exclude higher-field triality on the same original ordinary component,
using its two literal parabolic residuals and their nonshort rank-one cores. -/
theorem PreparedChosenModule.raw_ordinary_not_higherTriality
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (n : ℕ) (hn : 1 < n) :
    ¬IsTrialityGroupAt (2^n) L := by
  rintro ⟨Q,hQ,⟨e⟩⟩
  have heQ := Q.eq_binaryParameters_of_q_eq n (Nat.zero_lt_of_lt hn) hQ
  have em : L ≃* BinaryCarrier n (Nat.zero_lt_of_lt hn) := by
    rw [heQ] at e
    exact e
  obtain ⟨B,K,_,_,_,hfamily,hfit,hshort,hquot,hgen⟩ :=
    raw_triality_residuals hG T h hZ hZne hLG hL hcenter hSylG hSylL n hn em
  have hi (a : Node) : K a ≤ centralizer (Z1 : Set G) ⊓ Mc := by
    cases a with
    | arms =>
      exact h.raw_nonshort_pslTwo_le_marked hG T hempty hM hJ hu hZ hZne
        (hfamily .arms) (hfit .arms) (hshort .arms) (n*3) (by omega) (hquot .arms)
    | central =>
      exact h.raw_nonshort_pslTwo_le_marked hG T hempty hM hJ hu hZ hZne
        (hfamily .central) (hfit .central) (hshort .central) (n*1) (by omega) (hquot .central)
  exact hout (hgen ▸ sup_le (hi .arms) (hi .central))

end CFSG.Quasithin.Chapter15.Section01
