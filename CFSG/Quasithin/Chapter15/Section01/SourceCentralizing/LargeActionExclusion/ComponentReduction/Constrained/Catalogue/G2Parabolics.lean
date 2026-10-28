module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Block
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.Products
public import Theory.SpecificGroups.G2Even.CoreParabolics
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupTheory.NormalSymmetricThreeExtension
/-!
# G₂ source parabolics and placement in the original pair

The actual G₂(2)′ quotient has cubic rank two, so the original S normalizes
L. Its two marked parabolic preimages are S-invariant, have characteristic
two and symmetric-three two-core quotients, and generate L. Concrete
residual witnesses exclude the A₃-product case on both sides. Adjoining
the original normalizer two-group preserves each symmetric-three quotient;
thus both preimages satisfy every clause of the source parabolic family.

Original same-pair placement puts each in M ∩ L or M_L. Since they
generate L, these original intersections generate L, and the literal
O^{3′}(M ∩ L) escapes M_L. The FF quotient marking is retained, as are
both original source primes and the later exchanged plane sizes. The
actual-marker application uses the same seed and row.

The positive centralizer identity still requires the order-two bound on
the faithful normalizer omega-center. Small-block recognition, general
local-family Borel placement and catalogue exhaustiveness remain with
this owner. Original 15.1.14 retains its existing producer and assembly owner.

Source: Aschbacher--Smith 15.1.22(*), (!), (2), pp.1098--1100;
15.1.20(2b), pp.1094--1095. The concrete G₂ calculations use the licensed
ATLAS port through Theory.SpecificGroups.G2Even.CoreParabolics.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair Atlas.G2.ExceptionalLocalQuotients
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Cubic rank two normalizes every eligible G₂ member of the original local family. -/
theorem localFamily_g2_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : (K ⧸ pCore 2 K) ≃* DerivedModel) :
    d.S ≤ normalizer (K : Set G) := by
  apply d.localFamily_normalizes_of_oddRank hG h hK hq Nat.prime_three (by decide)
  rw [primeRank_equiv 3 e]
  exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived

omit [Finite G] in
private theorem embedded_sylow_invariant {K A : Subgroup G}
    (Q : Sylow 2 K) (hQ : (Q : Subgroup K).map K.subtype = A ⊓ K)
    (hn : A ≤ normalizer (K : Set G)) (C : Subgroup K)
    (hi : ∀ a : MulAut K, (Q : Subgroup K).map a.toMonoidHom = Q →
      C.map a.toMonoidHom = C) :
    A ≤ normalizer (C.map K.subtype : Set G) := by
  have hnQ : A ≤ normalizer ((A ⊓ K) : Set G) :=
    (le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  intro x hx
  let a := K.normalizerMonoidHom ⟨x,hn hx⟩
  have he : K.subtype.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp K.subtype := rfl
  have ha : (Q : Subgroup K).map a.toMonoidHom = Q := by
    apply map_injective K.subtype_injective
    rw [map_map,he,←map_map,hQ]
    exact mem_normalizer_iff_map_conj_eq.mp (hnQ hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (C.map K.subtype).map (MulAut.conj x).toMonoidHom = C.map K.subtype
  rw [map_map,←he,←map_map,hi a ha]


private theorem not_aThreeProduct_of_residual_image
    (P : Subgroup G) {H : Type*} [Group H]
    (f : P →* H) (hf : Function.Surjective f)
    (hH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1) : ¬ IsAThreeProduct P := by
  rintro ⟨F,hF,hc,hgen⟩
  obtain ⟨y,hy,hy6⟩ := hH
  rw [←map_pResidual_of_surjective 2 f hf] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  apply hy6
  rw [←map_pow,ChapterC.alternatingThree_product_pow_six F
    (fun A hA => (hF A hA).2) hc (hgen.symm ▸ hx),map_one]

omit [Finite G] in
private theorem mapped_cover (K : Subgroup G) (C : Subgroup K)
    {H : Type*} [Group H] (f : C →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ∃ g : C.map K.subtype →* H, Function.Surjective g ∧ IsPGroup 2 g.ker := by
  let e := C.equivMapOfInjective K.subtype K.subtype_injective
  exact ⟨f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective,
    hk.comap_of_injective _ e.symm.injective⟩

private theorem source_of_cover (d : CaseIComponentData T M Mc V)
    (P : Subgroup G) (hPL : P ≤ d.L) (hn : d.S ≤ normalizer (P : Set G))
    (hfit : generalizedFitting P = pCore 2 P)
    {H : Type*} [Group H] [Finite H]
    (eqH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (hH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1)
    (f : P →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    d.IsSourceParabolic P := by
  let e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3) :=
    (f.pCoreQuotientEquiv hf hk).trans eqH
  exact ⟨hPL,inf_le_left.trans hn,hfit,
    Or.inl (NormalSymmetricThreeExtension.normalized_join P d.sylowNormalizer
      (inf_le_left.trans hn) e (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))),
    not_aThreeProduct_of_residual_image P f hf hH⟩

private noncomputable def firstPermQuotient :
    (derivedFirst ⧸ pCore 2 derivedFirst) ≃* Equiv.Perm (Fin 3) :=
  derivedFirstQuotientEquiv.trans
    (dihedralEquivPSL.symm.trans nonempty_dihedralThreeEquivPerm.some)
private noncomputable def secondPermQuotient :
    (derivedSecond ⧸ pCore 2 derivedSecond) ≃* Equiv.Perm (Fin 3) :=
  derivedSecondQuotientEquiv.trans
    (dihedralEquivPSL.symm.trans nonempty_dihedralThreeEquivPerm.some)

private theorem lifted_source (d : CaseIComponentData T M Mc V)
    (Q : Sylow 2 d.L) (hQ : (Q : Subgroup d.L).map d.L.subtype = d.SL)
    (hnL : d.S ≤ normalizer (d.L : Set G)) (C : Subgroup d.L)
    (hCf : generalizedFitting C = pCore 2 C)
    (hinv : ∀ a : MulAut d.L, (Q : Subgroup d.L).map a.toMonoidHom = Q →
      C.map a.toMonoidHom = C)
    {H : Type*} [Group H] [Finite H]
    (eqH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (hH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1)
    (f : C →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    d.IsSourceParabolic (C.map d.L.subtype) ∧
      ∃ g : C.map d.L.subtype →* H, Function.Surjective g ∧ IsPGroup 2 g.ker := by
  let B := C.map d.L.subtype
  let eB := C.equivMapOfInjective d.L.subtype d.L.subtype_injective
  obtain ⟨g,hg,hkg⟩ := mapped_cover d.L C f hf hk
  have hBn := embedded_sylow_invariant Q hQ hnL C hinv
  have hBf : generalizedFitting B = pCore 2 B := by
    rw [←map_generalizedFitting_equiv eB,←pCore_map_iso 2 eB,hCf]
  exact ⟨source_of_cover d B (map_subtype_le _) hBn hBf eqH hH g hg hkg,⟨g,hg,hkg⟩⟩

private theorem pair_source (d : CaseIComponentData T M Mc V)
    (Q : Sylow 2 d.L) (hQ : (Q : Subgroup d.L).map d.L.subtype = d.SL)
    (hnL : d.S ≤ normalizer (d.L : Set G))
    {H I : Type*} [Group H] [Finite H] [Group I] [Finite I]
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (wH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1) (wI : ∃ y ∈ pResidual 2 I, y^6 ≠ 1)
    (pair : ∃ C E : Subgroup d.L, C ⊔ E = ⊤ ∧
      (Q : Subgroup d.L) ≤ C ∧ (Q : Subgroup d.L) ≤ E ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      (∃ f : C →* H, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : E →* I, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∀ a : MulAut d.L, (Q : Subgroup d.L).map a.toMonoidHom = Q →
        C.map a.toMonoidHom = C ∧ E.map a.toMonoidHom = E)) :
    ∃ P R : Subgroup G, d.IsSourceParabolic P ∧ d.IsSourceParabolic R ∧
      d.SL ≤ P ∧ d.SL ≤ R ∧ P ⊔ R = d.L ∧
      (∃ f : P →* H, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : R →* I, Function.Surjective f ∧ IsPGroup 2 f.ker) := by
  obtain ⟨C,E,hgen,hQC,hQE,hCf,hEf,⟨fC,hfC,hkC⟩,⟨fE,hfE,hkE⟩,hinv⟩ := pair
  obtain ⟨hB,hcovB⟩ := lifted_source (H := H) d Q hQ hnL C hCf
    (fun a ha => (hinv a ha).1) eH wH fC hfC hkC
  obtain ⟨hD,hcovD⟩ := lifted_source (H := I) d Q hQ hnL E hEf
    (fun a ha => (hinv a ha).2) eI wI fE hfE hkE
  refine ⟨C.map d.L.subtype,E.map d.L.subtype,hB,hD,
    hQ ▸ map_mono hQC,hQ ▸ map_mono hQE,?_,hcovB,hcovD⟩
  have hh := congrArg (map d.L.subtype) hgen
  simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh

/-- The two concrete G₂ preimages satisfy every source-family clause and generate L. -/
theorem constrained_g2_source_parabolics (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel) :
    ∃ P R : Subgroup G, d.IsSourceParabolic P ∧ d.IsSourceParabolic R ∧
      d.SL ≤ P ∧ d.SL ≤ R ∧ P ⊔ R = d.L ∧
      (∃ f : P →* derivedFirst, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : R →* derivedSecond, Function.Surjective f ∧ IsPGroup 2 f.ker) := by
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  change (Q : Subgroup d.L).map d.L.subtype = d.SL at hQ
  have hnL := d.localFamily_g2_normalizes hG h hK hq e
  exact pair_source (H := derivedFirst) (I := derivedSecond) d Q hQ hnL
    firstPermQuotient secondPermQuotient derivedFirst_residual_not_exponent_six
    derivedSecond_residual_not_exponent_six
    (Atlas.G2.BinaryParabolicPair.exists_core_parabolic_pair (X := d.L) hf e Q)

/-- The original G₂ FF row gives actual source parabolics, same-pair placement,
generation by the original intersections, and escape of their literal residual. -/
theorem PreExclusionSource.constrained_g2_parabolic_generation
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* DerivedModel) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel,
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      (∃ P R : Subgroup G, d.IsSourceParabolic P ∧ d.IsSourceParabolic R ∧
        (P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧ (R ≤ M ⊓ d.L ∨ R ≤ d.ML) ∧
        P ⊔ R = d.L ∧
        (∃ f : P →* derivedFirst, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
        (∃ f : R →* derivedSecond, Function.Surjective f ∧ IsPGroup 2 f.ker)) ∧
      (M ⊓ d.L) ⊔ d.ML = d.L ∧ ¬ d.localThreeResidual ≤ d.ML := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  let t := a.g2Derived_coreEquiv s.quasisimple e
  have hn := d.localFamily_g2_normalizes hG h hK s.quasisimple t
  obtain ⟨P,R,hP,hR,hSP,hSR,hgen,hcovP,hcovR⟩ :=
    d.constrained_g2_source_parabolics hG h hK s.quasisimple hf t
  have hp : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML :=
    s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hn
  have hpp : P ≤ M ⊓ d.L ∨ P ≤ d.ML := hp P hP
  have hpr : R ≤ M ⊓ d.L ∨ R ≤ d.ML := hp R hR
  have hge : d.L ≤ (M ⊓ d.L) ⊔ d.ML :=
    hgen.symm.le.trans (sup_le
      (hpp.elim (fun hh => hh.trans le_sup_left) (fun hh => hh.trans le_sup_right))
      (hpr.elim (fun hh => hh.trans le_sup_left) (fun hh => hh.trans le_sup_right)))
  have hjoin : (M ⊓ d.L) ⊔ d.ML = d.L :=
    le_antisymm (sup_le inf_le_right inf_le_right) hge
  have hF : ({P,R} : Set (Subgroup G)) ⊆ d.sourceParabolics := by
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact hP
    · exact (Set.mem_singleton_iff.mp hA).symm ▸ hR
  have hout : ¬ sSup ({P,R} : Set (Subgroup G)) ≤ d.ML := by
    rw [sSup_pair,hgen]
    intro hh
    exact d.L_not_le_MZ (hh.trans inf_le_left)
  have hres := (s.parabolic_family_residual_escape (h := h) hG hu hM.1.2 hp
    {P,R} hF hout).2
  exact ⟨t,fun x => a.g2Derived_coreEquiv_mk s.quasisimple e x,
    ⟨P,R,hP,hR,hpp,hpr,hgen,hcovP,hcovR⟩,hjoin,hres⟩

/-- Both exchanged plane sizes retain the actual G₂ quotient and the two
fully proved source parabolics. -/
theorem ExchangedSource.constrained_g2_source_parabolics
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* DerivedModel) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel,
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      ∃ P R : Subgroup G, d.IsSourceParabolic P ∧ d.IsSourceParabolic R ∧
        d.SL ≤ P ∧ d.SL ≤ R ∧ P ⊔ R = d.L ∧
        (∃ f : P →* derivedFirst, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
        (∃ f : R →* derivedSecond, Function.Surjective f ∧ IsPGroup 2 f.ker) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  let t := a.g2Derived_coreEquiv s.quasisimple e
  exact ⟨t,fun x => a.g2Derived_coreEquiv_mk s.quasisimple e x,
    d.constrained_g2_source_parabolics hG h hK s.quasisimple hf t⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]

/-- Actual-marker application of G₂ source placement and residual escape,
retaining both original primes and the independent original 15.1.14 premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_g2_generation
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
      (generalizedFitting d.L = pCore 2 d.L →
        Nonempty (d.normalizerImage d.L ≃* DerivedModel) →
        (∃ P R : Subgroup G, d.IsSourceParabolic P ∧ d.IsSourceParabolic R ∧
          (P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧ (R ≤ M ⊓ d.L ∨ R ≤ d.ML) ∧ P ⊔ R = d.L) ∧
        (M ⊓ d.L) ⊔ d.ML = d.L ∧ ¬ d.localThreeResidual ≤ d.ML) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro hf ⟨e⟩
  obtain ⟨t,ht,⟨P,R,hP,hR,hp,hr,hgen,hcovP,hcovR⟩,hjoin,hescape⟩ :=
    s.constrained_g2_parabolic_generation (h := h) hG hempty hM hJ hu hf e
  exact ⟨⟨P,R,hP,hR,hp,hr,hgen⟩,hjoin,hescape⟩
end CFSG.Quasithin.Chapter15.Section01
