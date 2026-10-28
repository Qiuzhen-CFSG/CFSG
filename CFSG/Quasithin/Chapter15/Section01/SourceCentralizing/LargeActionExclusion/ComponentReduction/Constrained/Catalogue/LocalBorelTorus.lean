module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalBorelPrime
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowOddFixer

/-!
# The original prime determines an escaping natural torus

For a natural L₂(2ⁿ) block K in the fixed family L(G₁,S), its Borel lies
in M and is two-perfect. Its action on V therefore has order dividing the
original prime p. When p is odd, S∩K centralizes V. Also V lies in J(S),
so it normalizes K without imposing S-normalization of K.

Lift the full torus of order 2ⁿ−1 inside the literal Borel. A nontrivial
kernel on V would give an odd subgroup fixed by V as well as the full
Sylow subgroup. The full-cover Sylow-fixer theorem would make V centralize
K, placing K in M_Z. Thus the torus action is faithful, so 2ⁿ−1=p.
At the two source primes, an escaping natural member therefore has p=3
and n=2. All natural blocks at p=5 lie in M_Z.

The full local-family group and intersection rows are assembled at p=5,
retaining both binary parabolics under their same quotient marking and
both small central-cover outcomes. The extra block assertions of
15.1.20(2b) retain their genuine ambient C-component condition in the
existing selected catalogue. The original-marker application retains the
fixed G₁,M_Z,S,Q₁ and Thompson commutator; the exchanged application
retains the cubic marker and either plane size.

The cubic field-four lower Borel containment remains unproved for general
local members. No M_Z orbit invariance or ambient C-componenthood is
inferred here. Original 15.1.14 and whole-core A₆ reconstruction keep their
independent producers and final assembly owners.

Source: Aschbacher--Smith 15.1.16--20, printed pp.1092--1095, and the
natural-cover centralizer argument in 15.1.21(i), printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem natural_torus (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    ∃ D : Subgroup G, D ≤ d.localSylowBorel K ∧ Odd (Nat.card D) ∧
      Nat.card D = 2 ^ n - 1 := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have he : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hB : (normalizer (P : Set K)).map K.subtype = d.localSylowBorel K := by
    rw [d.localSylowBorel_eq,←he]
    rfl
  obtain ⟨D,hD,ho,hc⟩ := hb.exists_odd_borel_torus P
  refine ⟨D.map K.subtype,(map_mono hD).trans_eq hB,?_,?_⟩
  · rwa [card_map_of_injective K.subtype_injective]
  · rwa [card_map_of_injective K.subtype_injective]

private theorem marked_borel_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {B : Subgroup G} (hBC : B ≤ M ⊓ d.G1) (hp : IsPPerfect 2 B) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A) (f : B →* A),
      Nat.card f.range ∣ p ∧ ∀ b : B, f b = 1 ↔ (b : G) ∈ centralizer (V : Set G) := by
  let C := M ⊓ d.G1
  let N := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : N.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' N
  let B0 := B.subgroupOf C
  have hB0 : IsPPerfect 2 B0 := hp.of_surjective
    (subgroupOfEquivOfLe hBC).symm.toMonoidHom (subgroupOfEquivOfLe hBC).symm.surjective
  have hR : B0.map q ≤ pResidual 2 (C ⧸ N) :=
    (map_mono (le_pResidual_of_isPPerfect B0 hB0)).trans
      (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N)).le
  let f := q.comp (inclusion hBC)
  have hf : f.range = B0.map q := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion hBC b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
  refine ⟨C ⧸ N,inferInstance,inferInstance,f,?_,?_⟩
  · rw [hf,←s.residual_card]
    exact card_dvd_of_le hR
  · intro b
    change q (inclusion hBC b) = 1 ↔ _
    exact (QuotientGroup.eq_one_iff (inclusion hBC b)).trans
      (and_iff_right (hBC b.property).1)

/-- The original marked residual is faithful on the entire natural torus
whenever the local member escapes M_Z. -/
theorem PreExclusionSource.localFamily_linearTwo_torus_eq_prime
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) : 2 ^ n - 1 = p := by
  let B := d.localSylowBorel K
  have hBC : B ≤ M ⊓ d.G1 :=
    le_inf (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
      (inf_le_left.trans hK.1)
  obtain ⟨A,_,_,f,hfp,hfc⟩ := marked_borel_action (h := h) s hBC
    (d.localFamily_linearTwo_borel_twoPerfect hK hb)
  have hfr : IsPGroup p f.range := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hfp)
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hPB : (P : Subgroup K).map K.subtype ≤ B := by
    rw [hP]
    exact le_inf inf_le_right (d.S ⊓ K).le_normalizer
  let P0 := ((P : Subgroup K).map K.subtype).subgroupOf B
  have hp0 : IsPGroup 2 P0 := (P.isPGroup'.map K.subtype).comap_subtype
  have hcop : Nat.Coprime 2 p := Nat.coprime_primes Nat.prime_two s.prime_prime |>.mpr hp2.symm
  have hdis := IsPGroup.disjoint_of_coprime (hp0.map f) hfr hcop
  have hPV : (P : Subgroup K).map K.subtype ≤ centralizer (V : Set G) := by
    intro x hx
    apply (hfc ⟨x,hPB hx⟩).mp
    exact disjoint_def.mp hdis (mem_map_of_mem f (show (⟨x,hPB hx⟩ : B) ∈ P0 from hx))
      ⟨⟨x,hPB hx⟩,rfl⟩
  have hVJ : V ≤ elementaryAbelianMaxJ d.S := by
    have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
    rw [he,hfull]
    intro v hv
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp
      ((source_centralizing_baumann_control hG T hM hJ).1 hv)).1
  have hVN : V ≤ normalizer (K : Set G) := hVJ.trans
    (d.localFamily_thompson_normalizes h hM.1.2 hu hK hq hout hb.2.1.fitting)
  obtain ⟨D,hDB,hDo,hDc⟩ := natural_torus d hK hb
  let g := f.comp (inclusion hDB)
  have hgi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    by_contra hne
    let E := g.ker.map D.subtype
    have hEK : E ≤ K := (map_subtype_le _).trans (hDB.trans inf_le_left)
    have hEo : Odd (Nat.card E) := by
      rw [card_map_of_injective D.subtype_injective]
      exact hDo.of_dvd_nat (card_subgroup_dvd_card g.ker)
    have hEne : E ≠ ⊥ := fun he => hne ((map_eq_bot_iff_of_injective _ D.subtype_injective).mp he)
    have hEV : E ≤ centralizer (V : Set G) := by
      rintro x ⟨y,hy,rfl⟩
      exact (hfc (inclusion hDB y)).mp hy
    have hKV := IsL2EvenBlock.centralizes_of_sylow_odd_fixed K V E hb P hVN hPV hEK hEo hEne hEV
    rw [hfull] at hKV
    exact hout (le_inf hK.1 (hKV.trans (localModule_centralizer_le_partner T M hu)))
  have hd : Nat.card D ∣ p := by
    have he := Nat.card_congr (MonoidHom.ofInjective hgi).toEquiv
    rw [he]
    exact (card_dvd_of_le (show g.range ≤ f.range from by
      rintro x ⟨y,rfl⟩
      exact ⟨inclusion hDB y,rfl⟩)).trans hfp
  rw [hDc] at hd
  apply (Nat.dvd_prime s.prime_prime).mp hd |>.resolve_left
  have hn : 1 < n := hb.1
  have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ n)
  norm_num at hh
  omega


/-- The only remaining escaping natural row is the original cubic field-four
row; in particular the earlier prime-five branch needs no exchanged selection. -/
theorem PreExclusionSource.localFamily_linearTwo_small_field
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) : p = 3 ∧ n = 2 := by
  have he := s.localFamily_linearTwo_torus_eq_prime (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hn := hb.1
  have hlt : n < 3 := by
    by_contra hno
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ n)
    norm_num at hh
    omega
  have hn2 : n = 2 := by omega
  subst n
  norm_num at he
  exact ⟨he.symm,rfl⟩

/-- At the original prime five, every natural local block is already in M_Z.
The subgroup need not be an ambient C-component. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ_five
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) : K ≤ d.MZ := by
  by_contra hout
  have he := s.localFamily_linearTwo_small_field (h := h) (Or.inr rfl)
    hG hM hJ hu hfull hK hq hout hb
  omega

/-- The Borel-containment obligation is discharged at the original prime five. -/
theorem PreExclusionSource.localFamily_linearTwo_borel_le_MZ_five
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) : d.localSylowBorel K ≤ d.MZ :=
  inf_le_left.trans (s.localFamily_linearTwo_le_MZ_five (h := h)
    hG hM hJ hu hfull hK hq hb)

/-- The group and intersection clauses of original 15.1.20(2) on the
whole local family, including the full natural Borel equality. The extra
block assertions in (2b) belong to its additional ambient C-component case. -/
inductive LocalConstrainedSourceRows (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop
  | naturalTwo (n : ℕ) (block : IsL2EvenBlock K n)
      (borel : d.MZ ⊓ K = d.localSylowBorel K)
  | alternatingFive (block : IsAlternatingBlock K 5)
      (borel : d.MZ ⊓ K = d.localSylowBorel K)
      (centralizing : d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G))
  | small (model : LocalSmallCentralModel (K ⧸ centralPreimage (pCore 2 K)))
      (equiv : (K ⧸ centralPreimage (pCore 2 K)) ≃*
        (d.normalizerImage K ⧸ center (d.normalizerImage K)))
      (marking : ∀ k : K, equiv (QuotientGroup.mk' (centralPreimage (pCore 2 K)) k) =
        QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K k))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (imageEquiv : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (equiv : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (marking : ∀ k : K, equiv (QuotientGroup.mk' (pCore 2 K) k) =
        imageEquiv (d.toNormalizerImage K k))
      (marked_parabolic : d.MZ ⊓ K < K ∧ LocalLinearParabolic equiv (d.MZ ⊓ K))
      (selected_parabolic : M ⊓ K < K ∧ LocalLinearParabolic equiv (M ⊓ K))

/-- The general local-family group and parabolic rows have their full
source conclusions at prime five. The natural case is excluded using
the original marker, without any later exchanged component. -/
theorem PreExclusionSource.localFamily_constrained_source_rows_five
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K := by
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    exact (hout (s.localFamily_linearTwo_le_MZ_five (h := h) hG hM hJ hu hfull hK hq hb)).elim
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

/-- The later exchanged application keeps its original cubic marker and
both plane sizes; its natural row can only have field order four. -/
theorem ExchangedSource.constrained_natural_degree_two
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) : n = 2 :=
  (sp.localFamily_linearTwo_small_field (h := h) (Or.inl rfl) hG hM hJ hu hfull
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb).2

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies exact torus order on every escaping
natural local member. At prime five all group and intersection rows have
the full source conclusion, retaining the literal quotient markings.
Original 15.1.14 is used only to construct the same marked component. -/
theorem PreparedChosenModule.source_preExclusion_local_constrained_rows_torus
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
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          (⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedRows d K) ∧
          (m.prime = 5 → CaseIComponentData.LocalConstrainedSourceRows d K) ∧
          ∀ n : ℕ, ChapterC.IsL2EvenBlock K n →
            (m.prime ≠ 2 → 2 ^ n - 1 = m.prime) ∧
            (m.prime = 3 ∨ m.prime = 5 → m.prime = 3 ∧ n = 2) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  refine ⟨d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf,?_,?_⟩
  · intro hp
    exact ((hp ▸ s : d.PreExclusionSource h.normalized 5).localFamily_constrained_source_rows_five
      (h := h) hG hempty hM hJ hu hfull hK hq hout hf).2
  · intro n hb
    exact ⟨fun hp => s.localFamily_linearTwo_torus_eq_prime (h := h) hG hM hJ hu hfull hK hq hout hb hp,
      fun hp => s.localFamily_linearTwo_small_field (h := h) hp hG hM hJ hu hfull hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
