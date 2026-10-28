module
public import Theory.SpecificGroups.G2.ParabolicResiduals
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupTheory.EquivariantParabolicLift
public import Theory.GroupTheory.SolvableResidual.PrimeTo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.InitialReduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect

/-!
# The two original higher-field G₂ parabolic residuals, including central covers

Align the actual component Sylow with the positive-root Sylow in its G₂
quotient. Cubic rank makes the component normal in G₁. Every automorphism
preserving that Sylow fixes both root parabolics, so their full preimages
are S-invariant. Their solvable residuals have characteristic two, actual
PSL₂ quotients and nonzero core triple commutators; hence they are nonblocks.
Normality in K join S places each residual in L(G₁,S). Perfectness lifts
their generation through the central two-kernel, so one escapes M_Z.

Both the simple higher-field row and the central G₂(4) row are covered by
the literal quotient construction. No ambient componenthood of the residual,
exchanged-source hypothesis or noncentrality premise is assumed.
Source: Aschbacher--Smith 15.1.20(3), printed p.1096. The remaining general
nonblock exclusion is owned by qt-e-1515-constrained-source-catalogue;
its application and the exceptional-family assembly remain with
qt-e-15122-ordinary-pre-exclusion. The marker consumer retains original
15.1.14 for discharge by qt-e-15122-pre-exclusion-catalogue.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.HigherFieldResiduals
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Cubic rank makes the actual G₂ component normal, including central two-covers. -/
theorem PreExclusionSource.g2_quotient_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (d.L ⧸ pCore 2 d.L) ≃* Model F) :
    (d.L.subgroupOf d.G1).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let ec : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  have hR : 2 ≤ primeRank 3 (d.L.subgroupOf d.G1) := by
    rw [primeRank_equiv 3 ec]
    have hr : 2 ≤ primeRank 3 (d.L ⧸ pCore 2 d.L) := by
      rw [primeRank_equiv 3 e]
      exact EvenThreeRank.two_le_primeRank
    exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hZ := (s.ordinary hL).center_two.of_equiv (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

/-- The literal full parabolics and nonblock residuals, with one common marking. -/
structure OrdinaryG2Residuals (d : CaseIComponentData T M Mc V) (q : ℕ) where
  parabolic : Fin 2 → Subgroup G
  factor : Fin 2 → Subgroup G
  parabolic_le : ∀ i, parabolic i ≤ d.L
  parabolic_proper : ∀ i, parabolic i ≠ d.L
  sylow_le : ∀ i, d.SL ≤ parabolic i
  normalized : ∀ i, d.S ≤ normalizer (parabolic i : Set G)
  residual : ∀ i, (solvableResidual (parabolic i)).map (parabolic i).subtype = factor i
  family : ∀ i, factor i ∈ Chapter1.LIn d.G1 d.S
  fitting : ∀ i, generalizedFitting (factor i) = pCore 2 (factor i)
  not_short : ∀ i, ¬ ChapterC.IsShort (factor i)
  quotient : ∀ i, ClassicalGroup.IsPSL (factor i ⧸ pCore 2 (factor i)) 2 q
  generated : factor 0 ⊔ factor 1 = d.L

/-- Construct both residuals through the actual two-core quotient, retaining its central kernel. -/
theorem PreExclusionSource.g2_quotient_residuals
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Model F) :
    Nonempty (d.OrdinaryG2Residuals (Nat.card F)) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.g2_quotient_normal (h := h) hG hL e))
  obtain ⟨Q,hQ⟩ := s.component_sylow
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U₀ := Q.mapSurjective hq₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) U₀ (sylow (F := F))
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  have hsur : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 q.ker := hker ▸ pCore_isPGroup
  have hc : q.ker ≤ center d.L := by rw [hker,←(s.ordinary hL).center_eq]
  have hU : (Q : Subgroup d.L).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Model F) => (U : Subgroup (Model F))) hg
    change ((Q : Subgroup d.L).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  let α : d.S →* MulAut (Model F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 d.L)).comp (d.L.normalizerMonoidHom.comp (inclusion hnL)))
  have heq (a : d.S) (l : d.L) :
      q (d.L.normalizerMonoidHom (inclusion hnL a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnSL : d.S ≤ normalizer (d.SL : Set G) :=
    (le_inf d.S.le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : d.S) : unipotent.map (α a).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant d.L q hnL α heq hnSL a
    rw [←hQL,hU] at hh
    exact hh
  let P₀ := fun i : Fin 2 => (parabolicAt (F := F) i).comap q
  let B := fun i : Fin 2 => (P₀ i).map d.L.subtype
  let K := fun i : Fin 2 => (solvableResidual (B i)).map (B i).subtype
  let R := fun i : Fin 2 => solvableResidual (P₀ i)
  let ek (i : Fin 2) : R i ≃* K i :=
    (((P₀ i).equivMapOfInjective d.L.subtype d.L.subtype_injective).solvableResidualEquiv).trans
      ((solvableResidual (B i)).equivMapOfInjective (B i).subtype (B i).subtype_injective)
  have hBL (i : Fin 2) : B i ≤ d.L := map_subtype_le _
  have hnB (i : Fin 2) : d.S ≤ normalizer (B i : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨l,hl,rfl⟩ := hx
    let a₀ : d.S := ⟨a,ha⟩
    refine ⟨d.L.normalizerMonoidHom (inclusion hnL a₀) l,?_,rfl⟩
    change q (d.L.normalizerMonoidHom (inclusion hnL a₀) l) ∈ parabolicAt i
    rw [heq]
    exact parabolicAt_invariant (α a₀) (hUi a₀) i ▸ mem_map_of_mem (α a₀).toMonoidHom hl
  have hnK (i : Fin 2) : d.S ≤ normalizer (K i : Set G) :=
    (hnB i).trans (normalizer_le_normalizer_characteristic_image (B i) (solvableResidual (B i)))
  have hKL (i : Fin 2) : K i ≤ d.L := (map_subtype_le _).trans (hBL i)
  let eq (i : Fin 2) : (K i ⧸ pCore 2 (K i)) ≃* PSL(2,F) :=
    (QuotientGroup.congr _ _ (ek i).symm (pCore_map_iso 2 (ek i).symm)).trans
      (preimageResidualCoreQuotientEquivPSL q hsur (by omega) hk i)
  have htriple (i : Fin 2) :
      ⁅⁅pCore 2 (K i), (⊤ : Subgroup (K i))⁆, pCore 2 (K i)⁆ ≠ ⊥ := by
    intro hh
    have hm := congrArg (Subgroup.map (ek i).symm.toMonoidHom) hh
    rw [map_commutator,map_commutator,pCore_map_iso,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ek i).symm.surjective,Subgroup.map_bot] at hm
    exact preimage_residual_core_triple q hsur (by omega) hk i hm
  have hfit (i : Fin 2) : generalizedFitting (K i) = pCore 2 (K i) := by
    rw [←map_generalizedFitting_equiv (ek i),←pCore_map_iso 2 (ek i)]
    congr 1
    exact preimage_residual_generalizedFitting q hsur (by omega) hk i
  have hfamily (i : Fin 2) : K i ∈ Chapter1.LIn d.G1 d.S := by
    let : Group.IsPerfect (K i) :=
      Group.IsPerfect.ofSurjective (f := (ek i).toMonoidHom) (ek i).surjective
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq
    let : IsSimpleGroup (K i ⧸ pCore 2 (K i)) := (eq i).isSimpleGroup
    have hz : center (K i ⧸ pCore 2 (K i)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (center (K i ⧸ pCore 2 (K i))) inferInstance with hh | hh
      · exact hh
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
    let : IsQuasisimple (K i ⧸ pCore 2 (K i)) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    apply Chapter1.mem_LIn_of_normalized_perfect s.centralizer_sylow
      ((hKL i).trans d.L_component.1) (hnK i)
    intro hh
    have hb : pCore 2 (K i) = ⊥ := (map_eq_bot_iff_of_injective _ (K i).subtype_injective).mp hh
    exact htriple i (by rw [hb,commutator_bot_left,commutator_bot_left])
  refine ⟨⟨B,K,hBL,?_,?_,hnB,(fun _ => rfl),hfamily,hfit,?_,?_,?_⟩⟩
  · intro i hb
    have hh : P₀ i = ⊤ := by
      apply map_injective d.L.subtype_injective
      rw [←MonoidHom.range_eq_map,range_subtype]
      exact hb
    have hm := congrArg (Subgroup.map q) hh
    rw [map_comap_eq_self_of_surjective hsur,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsur] at hm
    exact (parabolicAt_isCoatom (F := F) i).ne_top hm
  · intro i
    rw [←hQ]
    apply map_mono
    intro x hx
    exact unipotent_le_parabolicAt i (hU ▸ mem_map_of_mem q hx)
  · intro i hs
    exact htriple i (commutator_eq_bot_iff_le_centralizer.mpr hs.central)
  · intro i
    exact ⟨F,inferInstance,inferInstance,rfl,⟨eq i⟩⟩
  · have hm := congrArg (Subgroup.map d.L.subtype)
      (preimage_residuals_generate q hsur (by omega) hc)
    rw [Subgroup.map_sup,map_embedded_solvableResidual_of_hom,
      map_embedded_solvableResidual_of_hom,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm

/-- The higher-field G₂ quotient forces a nonblock local residual outside M_Z. -/
theorem PreExclusionSource.g2_escaping_nonblock_of_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 1 < n) (hm : IsG2At (d.L ⧸ pCore 2 d.L) (2^n)) :
    ∃ P K : Subgroup G, P < d.L ∧ d.SL ≤ P ∧ d.S ≤ normalizer (P : Set G) ∧
      (solvableResidual P).map P.subtype = K ∧
      K ∈ Chapter1.LIn d.G1 d.S ∧ generalizedFitting K = pCore 2 K ∧
      ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    change 2^2 ≤ 2^n
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  obtain ⟨r⟩ := s.g2_quotient_residuals (h := h) hG hL hq e
  have hout : ∃ i, ¬ r.factor i ≤ d.MZ := by
    by_contra! hall
    exact d.L_not_le_MZ (r.generated ▸ sup_le (hall 0) (hall 1))
  obtain ⟨i,hi⟩ := hout
  exact ⟨r.parabolic i,r.factor i,lt_of_le_of_ne (r.parabolic_le i) (r.parabolic_proper i),
    r.sylow_le i,r.normalized i,r.residual i,r.family i,r.fitting i,r.not_short i,hi,hF ▸ r.quotient i⟩

private theorem g2_quotient_of_model
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 1 < n) (hm : IsG2At d.L (2^n)) :
    IsG2At (d.L ⧸ pCore 2 d.L) (2^n) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  let : IsSimpleGroup (Model F) := isSimple hq
  let : Group.IsPerfect (Model F) := isPerfect hq
  have hz : center (Model F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Model F)) inferInstance with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
  have hcore : pCore 2 d.L = ⊥ := by
    rw [←(s.ordinary hL).center_eq]
    apply bot_unique
    intro x hx
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨x,hx⟩).property)
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e⟩⟩

/-- Both source G₂ rows feed the same construction, including every retained central G₂(4) cover. -/
theorem PreExclusionSource.g2_escaping_nonblock
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (n : ℕ) (hn : 1 < n)
    (hm : IsG2At d.L (2^n) ∨ IsG2At (d.L ⧸ pCore 2 d.L) (2^n)) :
    ∃ P K : Subgroup G, P < d.L ∧ d.SL ≤ P ∧ d.S ≤ normalizer (P : Set G) ∧
      (solvableResidual P).map P.subtype = K ∧
      K ∈ Chapter1.LIn d.G1 d.S ∧ generalizedFitting K = pCore 2 K ∧
      ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := by
  apply s.g2_escaping_nonblock_of_quotient (h := h) hG hL n hn
  exact hm.elim (g2_quotient_of_model (h := h) s hL n hn) id

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies an escaping G₂ residual at the same component,
Z₁, row and prime, including the retained central-cover branch. -/
theorem PreparedChosenModule.source_preExclusion_g2_escaping_nonblock
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
        (IsG2At d.L (2^n) ∨ IsG2At (d.L ⧸ pCore 2 d.L) (2^n)) →
        ∃ P K : Subgroup G, P < d.L ∧ d.SL ≤ P ∧ d.S ≤ normalizer (P : Set G) ∧
          (solvableResidual P).map P.subtype = K ∧
          K ∈ Chapter1.LIn d.G1 d.S ∧ generalizedFitting K = pCore 2 K ∧
          ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn hm =>
    s.g2_escaping_nonblock (h := h) hG hL n hn hm⟩

end CFSG.Quasithin.Chapter15.Section01
