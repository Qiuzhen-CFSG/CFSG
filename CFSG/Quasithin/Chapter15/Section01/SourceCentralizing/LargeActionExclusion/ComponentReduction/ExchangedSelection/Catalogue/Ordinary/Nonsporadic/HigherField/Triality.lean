module
public import Theory.SpecificGroups.Triality.ParabolicResiduals
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.InitialReduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.SpecificGroups.Triality.ElementaryNine

/-!
# The two nonblock residuals of an original higher-field triality component

The actual binary triality marking supplies two proper, S-invariant parabolics
containing the marked Sylow subgroup. Their literal solvable residuals belong
to L(G₁,S), have generalized Fitting subgroup equal to their two-core, and have
quotients PSL₂(2³ⁿ) and PSL₂(2ⁿ). The residuals generate the original component.
Their core commutators are the full, non-elementary root radicals, so neither
is a short group. Consequently one of these actual residuals escapes M_Z.

The construction first proves normality of the original component from its
cubic rank, then aligns one Sylow subgroup and transports both parabolics along
the same embedding. Local-family membership uses normality in K join S, not
ambient componenthood of K. The final application retains the original marker,
Z₁, row and prime, before exchanged-component selection.

This supplies the triality input to the higher-field argument of
Aschbacher--Smith 15.1.20(3), printed p.1096. The nonblock containment theorem
for arbitrary K in L(G₁,S) remains with qt-e-1515-constrained-source-catalogue;
the present construction does not assume that theorem or assert the resulting
triality exclusion. Its eventual application stays with
qt-e-15122-ordinary-pre-exclusion. Original 15.1.14 remains an explicit source
premise in the marker consumer, for discharge by
qt-e-15122-pre-exclusion-catalogue.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Triality.Standard Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem triality_factor_not_short (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) : ¬ ChapterC.IsShort (localFactor P a) := by
  intro hs
  let := hs.elementary
  let f := (ChapterC.blockU (localFactor P a)).equivMapOfInjective
    (localFactor P a).subtype (localFactor P a).subtype_injective
  have he := IsElementaryAbelian.of_surjective (p := 2) f.toMonoidHom f.surjective
  change IsElementaryAbelian 2
    ((⁅pCore 2 (localFactor P a), (⊤ : Subgroup (localFactor P a))⁆).map
      (localFactor P a).subtype) at he
  rw [localFactor_core_commutator_map P hp hq a] at he
  exact radical_not_elementary P hp a he

private theorem triality_factor_quasisimple (n : ℕ) (hn : 1 < n) (a : Node) :
    IsQuasisimple (localFactor (binaryParameters n (Nat.zero_lt_of_lt hn)) a ⧸
      pCore 2 (localFactor (binaryParameters n (Nat.zero_lt_of_lt hn)) a)) := by
  let P := binaryParameters n (Nat.zero_lt_of_lt hn)
  have hq : 4 ≤ P.q := by
    change 2^2 ≤ 2^n
    exact Nat.pow_le_pow_right (by decide) hn
  let := localFactor_isPerfect P rfl (by omega) a
  let : IsSimpleGroup (localFactor P a ⧸ pCore 2 (localFactor P a)) := by
    cases a with
    | arms =>
      let : IsSimpleGroup PSL(2,ExtensionField P) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [card_extensionField]
          exact hq.trans (Nat.le_self_pow (by decide) _))
      exact (localFactorArmsQuotientEquivPSL2 P rfl).isSimpleGroup
    | central =>
      let : IsSimpleGroup PSL(2,GaloisField P.prime P.exponent) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card P.prime P.exponent (Nat.ne_of_gt P.exponent_pos)]
          exact hq)
      exact (localFactorCentralQuotientEquivPSL2 P rfl).isSimpleGroup
  have hz : center (localFactor P a ⧸ pCore 2 (localFactor P a)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center (localFactor P a ⧸ pCore 2 (localFactor P a))) inferInstance with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- The original ordinary component is normal in G₁ for every binary triality parameter. -/
theorem PreExclusionSource.triality_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 0 < n) (e : d.L ≃* BinaryCarrier n hn) :
    (d.L.subgroupOf d.G1).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let ec : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let f := ec.trans e
  have hR : 2 ≤ primeRank 3 (d.L.subgroupOf d.G1) := by
    rw [primeRank_equiv 3 f]
    let E := ElementaryNine.subgroup (binaryParameters n hn) rfl
    let : IsElementaryAbelian 3 E := ElementaryNine.subgroup_elementary _ _
    exact IsElementaryAbelian.primeRank_ge_of_card E (ElementaryNine.card_subgroup _ _)
  have hZ := (s.ordinary hL).center_two.of_equiv
    (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

private theorem normalized_perfect_mem_localFamily
    (s : d.PreExclusionSource h.normalized p) (K : Subgroup G)
    (hKG : K ≤ d.G1) (hn : d.S ≤ normalizer (K : Set G))
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hcore : K.pCoreIn 2 ≠ ⊥) : K ∈ Chapter1.LIn d.G1 d.S := by
  let H := K ⊔ d.S
  have hKH : K ≤ H := le_sup_left
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hn)
  let e := subgroupOfEquivOfLe hKH
  let : Group.IsPerfect (K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hq
    let := hN
    let : Group.IsNilpotent ((K.subgroupOf H) ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hcomp := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : (K.subgroupOf H).Normal).isSubnormal hp
  have hc : K.pCoreIn 2 ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans hKH)
    ((sup_le K.le_normalizer hn).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  exact ⟨hKG,Chapter1.mem_L_of_cComponent
    (fun he => hcore (bot_unique (he ▸ hc)))
    (s.centralizer_sylow.restrict le_sup_right (sup_le hKG d.S_le_G1)) hKH hcomp⟩

/-- The two actual full parabolics and their residuals inside the original component. -/
structure OrdinaryTrialityResiduals (d : CaseIComponentData T M Mc V) (n : ℕ) where
  parabolic : Node → Subgroup G
  factor : Node → Subgroup G
  parabolic_le : ∀ a, parabolic a ≤ d.L
  parabolic_proper : ∀ a, parabolic a ≠ d.L
  factor_le : ∀ a, factor a ≤ parabolic a
  sylow_le : ∀ a, d.SL ≤ factor a
  normalized : ∀ a, d.S ≤ normalizer (parabolic a : Set G)
  residual : ∀ a, (solvableResidual (parabolic a)).map (parabolic a).subtype = factor a
  family : ∀ a, factor a ∈ Chapter1.LIn d.G1 d.S
  fitting : ∀ a, generalizedFitting (factor a) = pCore 2 (factor a)
  not_short : ∀ a, ¬ ChapterC.IsShort (factor a)
  quotient : ∀ a, ClassicalGroup.IsPSL (factor a ⧸ pCore 2 (factor a))
    2 (2 ^ (n * (match a with | .arms => 3 | .central => 1)))
  generated : factor .arms ⊔ factor .central = d.L

private theorem triality_marked_embedding
    (s : d.PreExclusionSource h.normalized p)
    (n : ℕ) (hn : 0 < n) (e : d.L ≃* BinaryCarrier n hn) :
    ∃ f : BinaryCarrier n hn →* G, Function.Injective f ∧ f.range = d.L ∧
      (unipotent (binaryParameters n hn)).map f = d.SL := by
  obtain ⟨Q,hQ⟩ := s.component_sylow
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := binaryParameters n hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) (unipotentSylow P rfl) R
  let c := MulAut.conj g
  let f := d.L.subtype.comp (e.symm.toMonoidHom.comp c.toMonoidHom)
  refine ⟨f,d.L.subtype_injective.comp (e.symm.injective.comp c.injective), ?_, ?_⟩
  · rw [MonoidHom.range_comp,(e.symm.toMonoidHom.comp c.toMonoidHom).range_eq_top_of_surjective
      (e.symm.surjective.comp c.surjective),←MonoidHom.range_eq_map,range_subtype]
  · have hc : (unipotent P).map c.toMonoidHom = (R : Subgroup (Carrier P)) := by
      change ((g • unipotentSylow P rfl : Sylow 2 (Carrier P)) : Subgroup (Carrier P)) = _
      rw [hg]
    change (unipotent P).map (d.L.subtype.comp (e.symm.toMonoidHom.comp c.toMonoidHom)) = _
    rw [←map_map,←map_map,hc]
    change (((Q : Subgroup d.L).map e.toMonoidHom).map e.symm.toMonoidHom).map
      d.L.subtype = _
    have hi : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id d.L := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [map_map (Q : Subgroup d.L) e.symm.toMonoidHom e.toMonoidHom,hi,map_id]
    exact hQ

private theorem triality_embedded_invariant
    {C : Type*} [Group C] (f : C →* G) (hf : Function.Injective f)
    (hr : f.range = d.L) (U X : Subgroup C) (hU : U.map f = d.SL)
    (hn : d.S ≤ normalizer (d.L : Set G))
    (hinv : ∀ a : MulAut C, U.map a.toMonoidHom = U → X.map a.toMonoidHom = X) :
    d.S ≤ normalizer (X.map f : Set G) := by
  let e : C ≃* d.L := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  have hSL : d.S ≤ normalizer (d.SL : Set G) :=
    (le_inf d.S.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  intro x hx
  let a : MulAut C := MulAut.congr e.symm (d.L.normalizerMonoidHom ⟨x,hn hx⟩)
  have he : f.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp f := by
    ext y
    change (e (e.symm (d.L.normalizerMonoidHom ⟨x,hn hx⟩ (e y))) : G) = _
    rw [e.apply_symm_apply]
    rfl
  have hUa : U.map a.toMonoidHom = U := by
    apply map_injective hf
    rw [map_map,he,←map_map,hU]
    exact mem_normalizer_iff_map_conj_eq.mp (hSL hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (X.map f).map (MulAut.conj x).toMonoidHom = X.map f
  rw [map_map,←he,←map_map,hinv a hUa]

/-- Construct the two generating nonblock residuals from the actual triality marking. -/
theorem PreExclusionSource.triality_residuals
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 1 < n)
    (e : d.L ≃* BinaryCarrier n (Nat.zero_lt_of_lt hn)) :
    Nonempty (d.OrdinaryTrialityResiduals n) := by
  let P := binaryParameters n (Nat.zero_lt_of_lt hn)
  have hq : 4 ≤ P.q := by
    change 2^2 ≤ 2^n
    exact Nat.pow_le_pow_right (by decide) hn
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.triality_normal (h := h) hG hL n (Nat.zero_lt_of_lt hn) e))
  obtain ⟨f,hf,hr,hU⟩ := triality_marked_embedding (h := h) s n (Nat.zero_lt_of_lt hn) e
  let B := fun a => (parabolic P a).map f
  let K := fun a => (localFactor P a).map f
  have hnB (a : Node) : d.S ≤ normalizer (B a : Set G) :=
    triality_embedded_invariant f hf hr (unipotent P) (parabolic P a) hU hnL
      (parabolic_map_eq_of_unipotent_invariant P rfl a)
  have hnK (a : Node) : d.S ≤ normalizer (K a : Set G) :=
    triality_embedded_invariant f hf hr (unipotent P) (localFactor P a) hU hnL
      (localFactor_map_eq_of_unipotent_invariant P rfl a)
  have hKL (a : Node) : K a ≤ d.L := hr ▸ map_le_range f _
  have hBL (a : Node) : B a ≤ d.L := hr ▸ map_le_range f _
  have hproper (a : Node) : B a ≠ d.L := by
    intro he
    apply parabolic_ne_top_binary P rfl a
    apply map_injective hf
    rw [←MonoidHom.range_eq_map,hr]
    exact he
  let ek (a : Node) : localFactor P a ≃* K a :=
    (localFactor P a).equivMapOfInjective f hf
  let eq (a : Node) : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃*
      (K a ⧸ pCore 2 (K a)) := QuotientGroup.congr _ _ (ek a) (pCore_map_iso 2 (ek a))
  have hfit (a : Node) : generalizedFitting (K a) = pCore 2 (K a) := by
    rw [←map_generalizedFitting_equiv (ek a),←pCore_map_iso 2 (ek a),
      localFactor_generalizedFitting P rfl a]
  have hshort (a : Node) : ¬ ChapterC.IsShort (K a) := fun hs =>
    triality_factor_not_short P rfl (by omega) a (hs.of_mulEquiv (ek a).symm)
  have hfamily (a : Node) : K a ∈ Chapter1.LIn d.G1 d.S := by
    let := localFactor_isPerfect P rfl (by omega) a
    let := triality_factor_quasisimple n hn a
    let : Group.IsPerfect (K a) :=
      Group.IsPerfect.ofSurjective (f := (ek a).toMonoidHom) (ek a).surjective
    let : IsQuasisimple (K a ⧸ pCore 2 (K a)) := IsQuasisimple.of_mulEquiv (eq a)
    apply normalized_perfect_mem_localFamily (h := h) s (K a)
      ((hKL a).trans d.L_component.1) (hnK a)
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
  have hKB (a : Node) : K a ≤ B a := map_mono (localFactor_le_parabolic P a)
  have hSK (a : Node) : d.SL ≤ K a := by
    rw [←hU]
    exact map_mono (unipotentSylow_le_localFactor P rfl a)
  refine ⟨⟨B,K,hBL,hproper,hKB,hSK,hnB,?_,hfamily,hfit,hshort,?_,?_⟩⟩
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
  · change (localFactor P .arms).map f ⊔ (localFactor P .central).map f = d.L
    rw [←Subgroup.map_sup,localFactor_sup_eq_top P rfl,←MonoidHom.range_eq_map,hr]

/-- At least one literal parabolic residual escapes M_Z. All local-family,
characteristic-two, nonblock and rank-one-model premises are proved here. -/
theorem PreExclusionSource.triality_escaping_nonblock
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 1 < n) (hm : IsTrialityGroupAt (2^n) d.L) :
    ∃ P K : Subgroup G, P ≤ d.L ∧ d.S ≤ normalizer (P : Set G) ∧
      (solvableResidual P).map P.subtype = K ∧
      K ∈ Chapter1.LIn d.G1 d.S ∧ generalizedFitting K = pCore 2 K ∧
      ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
      ∃ m : ℕ, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^m) := by
  obtain ⟨Q,hQ,⟨e⟩⟩ := hm
  have heQ := Q.eq_binaryParameters_of_q_eq n (Nat.zero_lt_of_lt hn) hQ
  have em : d.L ≃* BinaryCarrier n (Nat.zero_lt_of_lt hn) := by
    rw [heQ] at e
    exact e
  obtain ⟨r⟩ := s.triality_residuals (h := h) hG hL n hn em
  have hout : ∃ a, ¬ r.factor a ≤ d.MZ := by
    by_contra! hall
    exact d.L_not_le_MZ (r.generated ▸ sup_le (hall .arms) (hall .central))
  obtain ⟨a,ha⟩ := hout
  refine ⟨r.parabolic a,r.factor a,r.parabolic_le a,r.normalized a,r.residual a,
    r.family a,r.fitting a,r.not_short a,ha,?_⟩
  cases a with
  | arms => exact ⟨n * 3, by omega, r.quotient .arms⟩
  | central => exact ⟨n * 1, by omega, r.quotient .central⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the escaping triality residual at the same
component, Z₁, row and prime, before exchanged-component selection. -/
theorem PreparedChosenModule.source_preExclusion_triality_escaping_nonblock
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → ∀ n : ℕ, 1 < n →
        Triality.Standard.IsTrialityGroupAt (2^n) d.L →
        ∃ P K : Subgroup G, P ≤ d.L ∧ d.S ≤ normalizer (P : Set G) ∧
          (solvableResidual P).map P.subtype = K ∧
          K ∈ Chapter1.LIn d.G1 d.S ∧ generalizedFitting K = pCore 2 K ∧
          ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
          ∃ m : ℕ, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^m)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn hm =>
    s.triality_escaping_nonblock (h := h) hG hL n hn hm⟩

end CFSG.Quasithin.Chapter15.Section01
