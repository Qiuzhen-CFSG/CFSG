module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.LinearRefinement
public import Theory.SpecificGroups.BinaryLinear.EndpointParabolic

/-!
# The actual endpoint parabolic before ordinary-component selection

The binary-linear rank facts make the original component normal in G₁.
Transport the intrinsic endpoint parabolic along the given linear marking.
Its invariance under all Sylow-preserving automorphisms gives S-normalization;
its proper flag, characteristic-two property and literal S₃ × S₃ quotient
survive the same embedding. The Sylow-center centralizer lies in M_L, so the
intrinsic generating identity proves M_L ∨ B = L and B escapes M_L.
The original-marker application retains d, Z₁, row, prime and the same e.

This constructs the endpoint pair used in the ordinary binary-linear row,
but B itself need not be a source parabolic: its intrinsic quotient is
S₃ × S₃. The source family still requires its individual minimal parabolics
for an inner S-action, or the endpoint orbit with the literal wreath quotient
for a graph action, including the exclusions of A₃ products in O²(P).
Those constructions and the resulting M_L ∨ (M ∩ L) = L remain with
qt-e-15122-ordinary-pre-exclusion. The full local-family nonblock premise
retains producer qt-e-1515-constrained-source-catalogue and final discharge
by qt-e-15122-pre-exclusion-catalogue. No exchanged-plane hypothesis is used.

Source: Aschbacher--Smith 15.1.20(3e), 15.1.22(7), printed pp.1099--1100,
refs/quasithin.pdf. The normality argument uses the actual rank bound of A.3.18.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Theory.SpecificGroups.BinaryComponentResidual
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original binary linear component is normal in G₁. -/
theorem PreExclusionSource.binaryLinear_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    d.G1 ≤ normalizer (d.L : Set G) := by
  have hz : center d.L = ⊥ := by
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,(linear hn).1,card_bot]
  let q := ((QuotientGroup.quotientMulEquivOfEq
    ((s.ordinary hL).center_eq.symm.trans hz)).trans QuotientGroup.quotientBot).trans e
  let := s.quasisimple
  have he := (d.source_cubic_component hG h (Facts.of_equiv q (linear hn))).1
  rw [he]
  have hh := (primeToResidual 3 d.G1).le_normalizer_map d.G1.subtype
  rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh

private theorem linear_embedded_invariant
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

private theorem linear_embedded_center_centralizer
    {C : Type*} [Group C] (f : C →* G) (hf : Function.Injective f)
    (U : Subgroup C) (hU : U.map f = d.SL) :
    (centralizer ((center U).map U.subtype : Set C)).map f ≤
      centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨u,hu,heu⟩ := (show (z : G) ∈ U.map f from hU.symm ▸ z.property)
  have huc : (⟨u,hu⟩ : U) ∈ center U := by
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply hf
    change f ((v : C) * u) = f (u * (v : C))
    rw [map_mul,map_mul,heu]
    have hv : f v ∈ d.SL := hU ▸ mem_map_of_mem f v.property
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨f v,hv⟩ : d.SL))
  have hc := (mem_centralizer_iff.mp hx) u (mem_map_of_mem U.subtype huc)
  change (z : G) * f x = f x * z
  rw [←heu,←map_mul,←map_mul,hc]

private theorem binary_sylow_overgroup_fitting {n : ℕ} (hn : n = 4 ∨ n = 5)
    (Q : Sylow 2 (LinearGroup n)) (E : Subgroup (LinearGroup n))
    (hQE : (Q : Subgroup _) ≤ E) (hE : E ≠ ⊤) :
    generalizedFitting E = pCore 2 E := by
  rcases hn with rfl | rfl <;>
    exact proper_sylow_overgroup_generalizedFitting Q E hQE hE

/-- Construct the actual S-invariant endpoint parabolic. Its literal two-core
quotient is S₃ × S₃, and it generates L with the original M_L. -/
theorem PreExclusionSource.binaryLinear_endpoint_parabolic
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ∃ B : Subgroup G, d.OrdinaryLinearParabolic e B ∧ d.SL ≤ B ∧
      d.S ≤ normalizer (B : Set G) ∧ generalizedFitting B = pCore 2 B ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      d.ML ⊔ B = d.L ∧ ¬ B ≤ d.ML := by
  let a := e.trans (slEquivLinear n)
  let : Finite (LinearGroup n) := Finite.of_equiv d.L a.toEquiv
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨E,hQE,hE,⟨eE⟩,hinv,hgen⟩ := exists_endpoint_parabolic hn Q
  let f := d.L.subtype.comp a.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp a.symm.injective
  have hr : f.range = d.L := by
    rw [MonoidHom.range_comp,a.symm.toMonoidHom.range_eq_top_of_surjective a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hQ : (Q : Subgroup (LinearGroup n)).map f = d.SL := by
    change ((P : Subgroup d.L).map a.toMonoidHom).map f = _
    rw [map_map]
    have he : f.comp a.toMonoidHom = d.L.subtype := by
      ext x
      exact congrArg Subtype.val (a.symm_apply_apply x)
    rw [he]
    exact hP
  let B := E.map f
  have hBL : B ≤ d.L := hr ▸ map_le_range f E
  have hBne : B ≠ d.L := by
    intro hh
    apply hE
    apply map_injective hf
    rw [←MonoidHom.range_eq_map,hr]
    exact hh
  have hSB : d.SL ≤ B := hQ ▸ map_mono hQE
  have hnB : d.S ≤ normalizer (B : Set G) := linear_embedded_invariant f hf hr Q E hQ
    (d.S_le_G1.trans (s.binaryLinear_normal (h := h) hG hL hn e)) hinv
  let eb : E ≃* B := E.equivMapOfInjective f hf
  have hfit : generalizedFitting B = pCore 2 B := by
    rw [←map_generalizedFitting_equiv eb,←pCore_map_iso 2 eb]
    congr 1
    exact binary_sylow_overgroup_fitting hn Q E hQE hE
  have hc : (centralizer ((center (Q : Subgroup (LinearGroup n))).map
      (Q : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n))).map f ≤ d.ML := by
    apply le_trans (le_inf (hr ▸ map_le_range f _)
      (linear_embedded_center_centralizer f hf Q hQ))
    exact s.linear_centralizer_le (h := h) hG hM hu hL hn e
  have hg : d.ML ⊔ B = d.L := by
    apply le_antisymm (sup_le inf_le_right hBL)
    have hh := congrArg (map f) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,hr] at hh
    exact hh.ge.trans (sup_le (hc.trans le_sup_left) le_sup_right)
  refine ⟨B,s.linear_flag_overgroup (h := h) (by omega) e B hSB (lt_of_le_of_ne hBL hBne),
    hSB,hnB,hfit,?_,hg,?_⟩
  · exact ⟨(QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).symm.trans eE⟩
  · intro hh
    exact (s.ordinary hL).local_proper.not_ge (hg.ge.trans (sup_le le_rfl hh))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the endpoint construction before exchanged selection, retaining
Z₁, component, row, prime and the original linear isomorphism. -/
theorem PreparedChosenModule.source_preExclusion_binary_linear_endpoint
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ (n : ℕ), (n = 4 ∨ n = 5) →
          ∀ e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
            ∃ B : Subgroup G, d.OrdinaryLinearParabolic e B ∧ d.SL ≤ B ∧
              d.S ≤ normalizer (B : Set G) ∧ generalizedFitting B = pCore 2 B ∧
              Nonempty ((B ⧸ pCore 2 B) ≃*
                (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
              d.ML ⊔ B = d.L ∧ ¬ B ≤ d.ML) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn e =>
    s.binaryLinear_endpoint_parabolic (h := h) hG hM hu hL hn e⟩

end CFSG.Quasithin.Chapter15.Section01
