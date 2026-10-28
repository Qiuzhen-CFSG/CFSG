module
public import Theory.SpecificGroups.ReeF4.ParabolicResiduals
public import Theory.SpecificGroups.ReeF4.CubicRank
public import Theory.GroupTheory.EquivariantParabolicLift
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.InitialReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalClassification
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.CubicOrder
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect

/-!
# The original Ree parabolics and escaping linear residual

Cubic rank makes the marked ordinary Ree component normal in G₁. Align its
Sylow intersection with the actual positive subgroup, then transport both
full root parabolics and their solvable residuals through that same marking.
The two-power automorphisms induced by S preserve both parabolics. The
residuals belong to the literal family L(G₁,S), have F* = O₂ and actual
Suzuki and PSL₂ quotients, and generate the original component.

The full original local FF catalogue forces every escaping constrained
member to have order divisible by three. Hence the three-free Suzuki
residual lies in M_Z, and generation makes the nonblock linear residual
escape M_Z. No ambient C-component hypothesis is imposed on either residual.
The final consumer retains the original Z₁, row, prime and d before selection.

Source: Aschbacher--Smith 15.1.20(3), printed p.1096, using the earlier
15.1.20(2) FF argument, printed pp.1094--1095, and F.1.12, pp.263--264.
The remaining rank-one nonblock contradiction belongs to
qt-e-1515-constrained-source-catalogue; its final discharge and original
15.1.14 remain with qt-e-15122-pre-exclusion-catalogue. This construction
and the Ordinary20/22 assembly remain with qt-e-15122-ordinary-pre-exclusion.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open ReeF4 ReeF4.LargeLocalSeeds ReeF4.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Cubic rank makes the actual Ree component normal in its centralizer. -/
theorem PreExclusionSource.ree_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (m : ℕ) (e : d.L ≃* ReeF4.Model m) :
    (d.L.subgroupOf d.G1).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let ec : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  have hR : 2 ≤ primeRank 3 (d.L.subgroupOf d.G1) := by
    rw [primeRank_equiv 3 (ec.trans e)]
    exact CubicRank.model m
  have hZ := (s.ordinary hL).center_two.of_equiv (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

/-- The two full Ree parabolics and their literal residuals at the original marking. -/
structure OrdinaryReeResiduals (d : CaseIComponentData T M Mc V) (m : ℕ) where
  parabolic : Side → Subgroup G
  factor : Side → Subgroup G
  parabolic_lt : ∀ a, parabolic a < d.L
  sylow_le : ∀ a, d.SL ≤ parabolic a
  normalized : ∀ a, d.S ≤ normalizer (parabolic a : Set G)
  residual : ∀ a, (solvableResidual (parabolic a)).map (parabolic a).subtype = factor a
  family : ∀ a, factor a ∈ Chapter1.LIn d.G1 d.S
  fitting : ∀ a, generalizedFitting (factor a) = pCore 2 (factor a)
  quasisimple : ∀ a, IsQuasisimple (factor a ⧸ pCore 2 (factor a))
  suzuki_quotient : Nonempty ((factor .suzuki ⧸ pCore 2 (factor .suzuki)) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
  linear_quotient : ClassicalGroup.IsPSL (factor .linear ⧸ pCore 2 (factor .linear)) 2 (2^(2*m+1))
  suzuki_three_free : ¬ 3 ∣ Nat.card (factor .suzuki)
  linear_not_short : ¬ ChapterC.IsShort (factor .linear)
  generated : factor .suzuki ⊔ factor .linear = d.L

private theorem ree_sylow_marking
    (s : d.PreExclusionSource h.normalized p) (m : ℕ) (e : d.L ≃* ReeF4.Model m) :
    ∃ e' : d.L ≃* ReeF4.Model m,
      (d.SL.subgroupOf d.L).map e'.toMonoidHom = Parabolics.unipotent m := by
  obtain ⟨Q,hQ⟩ := s.component_sylow
  have hQL : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent] at hU
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ReeF4.Model m) Q' U
  refine ⟨e.trans (MulAut.conj g),?_⟩
  rw [←hQL]
  change (Q : Subgroup d.L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [←map_map]
  change (Q' : Subgroup (ReeF4.Model m)).map (MulAut.conj g).toMonoidHom = _
  rw [←hU,←hg,Sylow.coe_subgroup_smul,pointwise_smul_def]
  rfl

/-- Construct both residuals and their exact Suzuki and PSL₂ quotients. -/
theorem PreExclusionSource.ree_residuals
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (m : ℕ) (hm : 1 ≤ m) (model : Chapter1.Section02.LocalModels.IsReeF4At d.L m) :
    Nonempty (d.OrdinaryReeResiduals m) := by
  obtain ⟨D,⟨e₀⟩⟩ := model
  obtain ⟨e,he⟩ := ree_sylow_marking (h := h) s m (e₀.trans D.modelEquiv)
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.ree_normal (h := h) hG hL m e))
  let f := d.L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp e.symm.injective
  have hr : f.range = d.L := by rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
    ←MonoidHom.range_eq_map,range_subtype]
  have hU : (Parabolics.unipotent m).map f = d.SL := by
    rw [←he,map_map]
    have hh : f.comp e.toMonoidHom = d.L.subtype := by ext x; simp [f]
    rw [hh,map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
  let B := fun a => (Parabolics.parabolic m a).map f
  let K := fun a => (localFactor m a).map f
  let α : d.S →* MulAut (ReeF4.Model m) := (MulAut.congr e).toMonoidHom.comp
    (d.L.normalizerMonoidHom.comp (inclusion hnL))
  have heq (a : d.S) (l : d.L) :
      e (d.L.normalizerMonoidHom (inclusion hnL a) l) = α a (e l) := by simp [α]
  have hnSL : d.S ≤ normalizer (d.SL : Set G) :=
    (le_inf d.S.le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : d.S) : (Parabolics.unipotent m).map (α a).toMonoidHom = Parabolics.unipotent m := by
    have hh := EquivariantLift.map_invariant d.L e.toMonoidHom hnL α heq hnSL a
    rwa [he] at hh
  have hpow (a : d.S) : ∃ n : ℕ, α a ^ (2^n) = 1 := by
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le d.S_le_T) a
    exact ⟨n,by rw [←map_pow,hn,map_one]⟩
  have hBi (a : Side) (t : d.S) :
      (Parabolics.parabolic m a).map (α t).toMonoidHom = Parabolics.parabolic m a := by
    have hi : ∀ x, x ∈ ConverseParabolics.unipotent m ↔ α t x ∈ ConverseParabolics.unipotent m := by
      rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent]
      intro x
      have hx := (mem_map_iff_mem (f := (α t).toMonoidHom) (α t).injective
        (K := Parabolics.unipotent m) (x := x)).symm
      rw [hUi t] at hx
      exact hx
    have hh := ConverseParabolics.parabolic_invariant_of_twoPower hm (α t) (hpow t) hi a
    rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hh
    ext x
    rw [mem_map_equiv]
    simpa only [MulEquiv.apply_symm_apply] using hh ((α t).symm x)
  have hBn (a : Side) : d.S ≤ normalizer (B a : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let t₀ : d.S := ⟨t,ht⟩
    refine ⟨α t₀ y,hBi a t₀ ▸ mem_map_of_mem (α t₀).toMonoidHom hy,?_⟩
    change (e.symm (e (d.L.normalizerMonoidHom (inclusion hnL t₀) (e.symm y))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hres (a : Side) : (solvableResidual (B a)).map (B a).subtype = K a := by
    rw [←map_embedded_solvableResidual_of_hom,parabolic_solvableResidual_map hm a]
  have hKn (a : Side) : d.S ≤ normalizer (K a : Set G) := by
    rw [←hres a]
    exact (hBn a).trans (normalizer_le_normalizer_characteristic_image (B a) (solvableResidual (B a)))
  have hKL (a : Side) : K a ≤ d.L := hr ▸ map_le_range f _
  let ek (a : Side) : localFactor m a ≃* K a := (localFactor m a).equivMapOfInjective f hf
  let eq (a : Side) := QuotientGroup.congr _ _ (ek a) (pCore_map_iso 2 (ek a))
  have hq (a : Side) : IsQuasisimple (K a ⧸ pCore 2 (K a)) := by
    let := localFactor_quotient_quasisimple hm a
    exact IsQuasisimple.of_mulEquiv (eq a)
  have hfit (a : Side) : generalizedFitting (K a) = pCore 2 (K a) := by
    rw [←map_generalizedFitting_equiv (ek a),←pCore_map_iso 2 (ek a),localFactor_generalizedFitting hm a]
  have hfamily (a : Side) : K a ∈ Chapter1.LIn d.G1 d.S := by
    let := OuterLocal.localFactor_perfect hm a
    let : Group.IsPerfect (K a) := Group.IsPerfect.ofSurjective (f := (ek a).toMonoidHom) (ek a).surjective
    let := hq a
    apply Chapter1.mem_LIn_of_normalized_perfect s.centralizer_sylow
      ((hKL a).trans d.L_component.1) (hKn a)
    intro hz
    have hz' : pCore 2 (K a) = ⊥ := (map_eq_bot_iff_of_injective _ (K a).subtype_injective).mp hz
    have hh := congrArg (Subgroup.map (ek a).symm.toMonoidHom) hz'
    rw [pCore_map_iso,Subgroup.map_bot] at hh
    exact localFactor_core_ne_bot hm a hh
  refine ⟨⟨B,K,?_,?_,hBn,hres,hfamily,hfit,hq,
    ⟨(eq .suzuki).symm.trans (suzukiLocalQuotientEquiv m)⟩,
    ⟨CoefficientField m,inferInstance,inferInstance,field_card m,
      ⟨(eq .linear).symm.trans (linearLocalQuotientEquiv m)⟩⟩,?_,?_,?_⟩⟩
  · intro a
    apply lt_of_le_of_ne (hr ▸ map_le_range f _)
    intro hz
    apply parabolic_ne_top hm a
    apply map_injective hf
    rw [←MonoidHom.range_eq_map,hr]
    exact hz
  · intro a
    rw [←hU]
    exact map_mono ((unipotent_le_borel m).trans (borel_le_parabolic m a))
  · rw [←Nat.card_congr (ek .suzuki).toEquiv]
    exact suzukiLocalFactor_three_free hm
  · intro hs
    have hs' := hs.of_mulEquiv (ek .linear).symm
    exact linearLocalFactor_core_triple hm (commutator_eq_bot_iff_le_centralizer.mpr hs'.central)
  · change (localFactor m .suzuki).map f ⊔ (localFactor m .linear).map f = d.L
    rw [←Subgroup.map_sup,localFactor_sup_eq_top,←MonoidHom.range_eq_map,hr]

/-- The Suzuki residual is contained in M_Z under the original hypotheses:
every escaping local FF group has a cubic, while this residual is three-free. -/
theorem OrdinaryReeResiduals.suzuki_le_MZ {m : ℕ} (r : d.OrdinaryReeResiduals m)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : r.factor .suzuki ≤ d.MZ := by
  by_contra hout
  obtain ⟨a,ha⟩ := d.localFamily_catalogue hG hempty hM hJ hu h
    (r.family .suzuki) (r.quasisimple .suzuki) hout (r.fitting .suzuki)
  let K := r.factor .suzuki
  let H := K ⊔ d.normalizerSylow K
  let q := QuotientGroup.mk' (centralizer (d.normalizerModule K : Set H))
  have hd := ha.three_dvd.trans
    (card_dvd_of_surjective (q.subgroupMap (K.subgroupOf H))
      (q.subgroupMap_surjective (K.subgroupOf H)))
  rw [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).toEquiv] at hd
  exact r.suzuki_three_free hd

/-- The original higher-field Ree marking supplies an escaping nonblock PSL₂ residual. -/
theorem PreExclusionSource.ree_escaping_nonblock
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (m : ℕ) (hm : 1 ≤ m) (model : Chapter1.Section02.LocalModels.IsReeF4At d.L m) :
    ∃ P K : Subgroup G, P < d.L ∧ d.SL ≤ P ∧ d.S ≤ normalizer (P : Set G) ∧
      (solvableResidual P).map P.subtype = K ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
      generalizedFitting K = pCore 2 K ∧ ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^(2*m+1)) := by
  obtain ⟨r⟩ := s.ree_residuals (h := h) hG hL m hm model
  have hout : ¬ r.factor .linear ≤ d.MZ := by
    intro hlin
    exact d.L_not_le_MZ (r.generated ▸ sup_le (r.suzuki_le_MZ hG hempty hM hJ hu h) hlin)
  exact ⟨r.parabolic .linear,r.factor .linear,r.parabolic_lt .linear,r.sylow_le .linear,
    r.normalized .linear,r.residual .linear,r.family .linear,r.fitting .linear,
    r.linear_not_short,hout,r.linear_quotient⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct the original marker and its escaping Ree residual at the same d,
Z₁, row and prime, before exchanged-component selection. -/
theorem PreparedChosenModule.source_preExclusion_ree_escaping_nonblock
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → ∀ k : ℕ, 1 ≤ k →
        Chapter1.Section02.LocalModels.IsReeF4At d.L k →
        ∃ P K : Subgroup G, P < d.L ∧ d.SL ≤ P ∧ d.S ≤ normalizer (P : Set G) ∧
          (solvableResidual P).map P.subtype = K ∧ K ∈ Chapter1.LIn d.G1 d.S ∧
          generalizedFitting K = pCore 2 K ∧ ¬ ChapterC.IsShort K ∧ ¬ K ≤ d.MZ ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^(2*k+1))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL k hk hm =>
    s.ree_escaping_nonblock (h := h) hG hempty hM hJ hu hL k hk hm⟩

end CFSG.Quasithin.Chapter15.Section01
