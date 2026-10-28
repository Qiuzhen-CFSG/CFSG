module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Endpoint
public import Theory.SpecificGroups.BinaryLinear.OuterParabolicGeneration

/-!
# The ordinary binary-linear row for an outer Sylow action

The established cubic residual escape puts M ∩ L outside M_L. Both are
Sylow overgroups, and M_L contains the actual Sylow-center centralizer.
If the original S has an outer action on L, transport that action through
the same given linear marking. It preserves S_L and M ∩ L, so the intrinsic
flag-reversal theorem gives M_L ∨ (M ∩ L) = L. The existing parabolic and
residual identities then complete the literal Ordinary22 linear row.

The complementary case is stated as S ≤ L C_G(L), retaining the actual
original S and L. Its minimal-parabolic source family is constructed in Linear/Inner and
applied in Linear/Application. The cubic Ru exclusion remains with
qt-e-15122-ordinary-pre-exclusion.
The independent full local-family nonblock input retains its producer
qt-e-1515-constrained-source-catalogue and final discharge by
qt-e-15122-pre-exclusion-catalogue. No placement or exchanged-plane premise
is used in the outer-action row.

Source: Aschbacher--Smith 15.1.22(7), printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

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

omit [Finite G] in
private theorem inner_normalizer_mem_product {A : Subgroup G}
    (x : normalizer (A : Set G))
    (hi : A.normalizerMonoidHom x ∈ MulAut.innerSubgroup A) :
    (x : G) ∈ A ⊔ centralizer (A : Set G) := by
  obtain ⟨a,ha⟩ := hi
  let aN : normalizer (A : Set G) := ⟨a,A.le_normalizer a.property⟩
  have haN : A.normalizerMonoidHom aN = MulAut.conj a := by ext y; rfl
  have hk : aN⁻¹*x ∈ A.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,haN,ha,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hm := (A ⊔ centralizer (A : Set G)).mul_mem
    (mem_sup_left a.property) (mem_sup_right (show (a : G)⁻¹*x ∈ centralizer (A : Set G) from hk))
  simpa only [mul_inv_cancel_left] using hm

omit [Finite G] in
private theorem embedded_invariant {C : Type*} [Group C]
    (f : C →* G) (hf : Function.Injective f) (a : MulAut C) (x : G)
    (he : f.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp f)
    (U : Subgroup C) (hx : x ∈ normalizer (U.map f : Set G)) :
    U.map a.toMonoidHom = U := by
  apply map_injective hf
  rw [map_map,he,←map_map]
  exact mem_normalizer_iff_map_conj_eq.mp hx

/-- Generation for the original binary linear intersections whenever the
full original S induces an outer automorphism on L. -/
theorem PreExclusionSource.binaryLinear_generation_of_outer
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hout : ¬ d.S ≤ d.L ⊔ centralizer (d.L : Set G)) :
    d.ML ⊔ (M ⊓ d.L) = d.L := by
  classical
  have hres := (s.binaryLinear_residual_control (h := h) hp hG hM hJ hu hL hn e).2.1
  have hMI : ¬ M ⊓ d.L ≤ d.ML := by
    intro hh
    exact hres ((map_subtype_le (primeToResidual 3 (M ⊓ d.L : Subgroup G))).trans hh)
  have hnL := d.S_le_G1.trans (s.binaryLinear_normal (h := h) hG hL hn e)
  have hl := s.local_intersections (h := h) hG hu hM.1.2
  obtain ⟨x,hx,hxi⟩ := SetLike.not_le_iff_exists.mp hout
  let a := e.trans (slEquivLinear n)
  let : Finite (LinearGroup n) := Finite.of_equiv d.L a.toEquiv
  let f := d.L.subtype.comp a.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp a.symm.injective
  have hfcomp : f.comp a.toMonoidHom = d.L.subtype := by
    ext y
    exact congrArg Subtype.val (a.symm_apply_apply y)
  have hr : f.range = d.L := by
    rw [MonoidHom.range_comp,a.symm.toMonoidHom.range_eq_top_of_surjective a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let A := (d.ML.subgroupOf d.L).map a.toMonoidHom
  let B := ((M ⊓ d.L).subgroupOf d.L).map a.toMonoidHom
  have hA : A.map f = d.ML := by
    rw [map_map,hfcomp]
    exact map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right)
  have hB : B.map f = M ⊓ d.L := by
    rw [map_map,hfcomp,map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hQ : (Q : Subgroup (LinearGroup n)).map f = d.SL := by
    change ((P : Subgroup d.L).map a.toMonoidHom).map f = _
    rw [map_map,hfcomp,hP]
  have hQA : (Q : Subgroup _) ≤ A := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [hQ,hA]
    exact hl.2.1
  have hQB : (Q : Subgroup _) ≤ B := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [hQ,hB]
    exact hl.2.2.2.1
  have hBA : ¬B ≤ A := by
    intro hh
    exact hMI (hB ▸ hA ▸ map_mono (f := f) hh)
  have hC : centralizer ((center (Q : Subgroup (LinearGroup n))).map
      (Q : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n)) ≤ A := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [hA]
    apply le_trans (le_inf (hr ▸ map_le_range f _)
      (linear_embedded_center_centralizer f hf Q hQ))
    exact s.linear_centralizer_le (h := h) hG hM hu hL hn e
  let α := d.L.normalizerMonoidHom ⟨x,hnL hx⟩
  let β := MulAut.congr a α
  have he : f.comp β.toMonoidHom = (MulAut.conj x).toMonoidHom.comp f := by
    ext y
    change (a.symm (a (α (a.symm y))) : G) = _
    rw [a.symm_apply_apply]
    rfl
  have hβ : β ∉ MulAut.innerSubgroup (LinearGroup n) := by
    intro hi
    apply hxi
    apply inner_normalizer_mem_product ⟨x,hnL hx⟩
    rw [←MulAut.map_innerSubgroup_congr a] at hi
    simpa only [β,MulEquiv.symm_apply_apply] using (mem_map_equiv).mp hi
  have hQS : (Q : Subgroup _).map β.toMonoidHom = Q := by
    apply embedded_invariant f hf β x he
    rw [hQ]
    exact inf_normalizer_le_normalizer_inf ⟨d.S.le_normalizer hx,hnL hx⟩
  have hBS : B.map β.toMonoidHom = B := by
    apply embedded_invariant f hf β x he
    rw [hB]
    exact inf_normalizer_le_normalizer_inf
      ⟨M.le_normalizer (hM.1.2 (d.S_le_T hx)),hnL hx⟩
  have hgen : A ⊔ B = ⊤ := by
    rcases hn with rfl | rfl <;>
      exact outer_invariant_escape_generates (by decide) (by decide)
        Q A B hQA hQB hC hBA β hβ hQS hBS
  have hh := congrArg (map f) hgen
  rw [Subgroup.map_sup,hA,hB,←MonoidHom.range_eq_map,hr] at hh
  exact hh

/-- The complete source linear row for every outer action of the original S. -/
theorem PreExclusionSource.ordinary22_binaryLinear_of_outer
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hout : ¬ d.S ≤ d.L ⊔ centralizer (d.L : Set G)) :
    d.Ordinary22Alternatives :=
  s.ordinary22_linear_of_generation (h := h) hp hG hM hJ hu hL hn e
    (s.binaryLinear_generation_of_outer (h := h) hp hG hM hJ hu hL hn e hout)

/-- Only the inner Sylow-action branch remains after the flag-reversal argument. -/
theorem PreExclusionSource.ordinary22_binaryLinear_or_inner
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    d.Ordinary22Alternatives ∨ d.S ≤ d.L ⊔ centralizer (d.L : Set G) := by
  by_cases hi : d.S ≤ d.L ⊔ centralizer (d.L : Set G)
  · exact .inr hi
  · exact .inl (s.ordinary22_binaryLinear_of_outer (h := h) hp hG hM hJ hu hL hn e hi)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
