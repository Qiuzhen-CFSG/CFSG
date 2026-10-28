module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.InnerPlacement
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
import Mathlib.Data.Finset.Sort

/-!
# The initial ordinary binary linear row

Every proper overgroup of the original S_L is an actual partial-flag
stabilizer under the same binary linear isomorphism. A marked central
involution fixes S_L pointwise; the binary linear Sylow-fixer theorem
makes its action inner. The original singleton centralizer overgroup then
places C_L(Z(S_L)) in M_L. These two arguments construct the complete
15.1.20(3e) row, including for a model supplied as PSL over an arbitrary
field of order two.

The flag theorem also applies to M ∩ L in the later refinement, but no
exhaustiveness, generation or residual-centralizer conclusion is asserted
here. Initial and refined catalogue assembly remain with
qt-e-15122-ordinary-pre-exclusion.
Source: Aschbacher--Smith 15.1.20(3e), printed pp.1094--1097.
-/

public section
open scoped Pointwise
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem binary_mem_linearStabilizer {n : ℕ}
    (W : Submodule (ZMod 2) (Space n)) (x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    x ∈ linearStabilizer W ↔ slEquivLinear n x ∈ parabolic W := by
  change Matrix.SpecialLinearGroup.toLin' x ∈
    MulAction.stabilizer (LinearGroup n) W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

private theorem exists_linearFlag_of_cuts {m : ℕ} (b : Basis m)
    (cuts : Set (Fin m)) (hc : cuts.Nonempty) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) (m + 1) k,
      f.stabilizer.map (slEquivLinear (m + 1)).toMonoidHom = cutStabilizer b cuts := by
  classical
  let c := cuts.toFinset
  let ι : Fin c.card ↪o Fin m := c.orderEmbOfFin rfl
  have hi : StrictMono (cutSpace b) := by
    intro i j hij
    apply lt_of_le_of_ne (cutSpace_mono b hij.le)
    intro he
    have hh := congrArg (fun W : Submodule (ZMod 2) (Space (m + 1)) => Module.finrank (ZMod 2) W) he
    rw [cutSpace_finrank, cutSpace_finrank] at hh
    have : i.val < j.val := hij
    omega
  let f : LinearFlag (ZMod 2) (m + 1) c.card := {
    space := fun i => cutSpace b (ι i)
    nonzero := fun i => cutSpace_ne_bot b (ι i)
    proper := fun i => cutSpace_ne_top b (ι i)
    increasing := hi.comp ι.strictMono }
  have hc' : c.Nonempty := by simpa [c] using hc
  refine ⟨c.card, Finset.card_pos.mpr hc', f, ?_⟩
  ext g
  obtain ⟨x, rfl⟩ := (slEquivLinear (m + 1)).surjective g
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_cutStabilizer]
  simp only [LinearFlag.stabilizer, mem_iInf]
  change (∀ i, x ∈ linearStabilizer (cutSpace b (ι i))) ↔ _
  constructor
  · intro hx j hj
    have hjc : j ∈ c := by simpa [c] using hj
    obtain ⟨i, he⟩ := (c.orderIsoOfFin rfl).surjective ⟨j,hjc⟩
    have he' : ι i = j := congrArg Subtype.val he
    exact (binary_mem_linearStabilizer _ x).mp (he' ▸ hx i)
  · intro hx i
    have hi' : ι i ∈ cuts := by
      exact Set.mem_toFinset.mp (c.orderEmbOfFin_mem rfl i)
    exact (binary_mem_linearStabilizer _ x).mpr (hx (ι i) hi')

/-- Every proper overgroup of the original component Sylow is an actual
flag stabilizer under the supplied binary linear equivalence. -/
theorem PreExclusionSource.linear_flag_overgroup
    (s : d.PreExclusionSource h.normalized p) {n : ℕ} (hn : 0 < n)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (K : Subgroup G) (hSK : d.SL ≤ K) (hK : K < d.L) :
    d.OrdinaryLinearParabolic e K := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let a := e.trans (slEquivLinear (m + 1))
  obtain ⟨P, hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let H := (K.subgroupOf d.L).map a.toMonoidHom
  have hPH : (Q : Subgroup (LinearGroup (m + 1))) ≤ H := by
    apply map_mono
    intro x hx
    exact hSK (hP ▸ mem_map_of_mem d.L.subtype hx)
  obtain ⟨b,cuts,_,hH⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le Q H hPH
  have hHne : H ≠ ⊤ := by
    intro he
    have ht : K.subgroupOf d.L = ⊤ := by
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [← MonoidHom.range_eq_map, a.toMonoidHom.range_eq_top_of_surjective a.surjective]
      exact he
    apply hK.ne
    have hm := congrArg (Subgroup.map d.L.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hK.le, ← MonoidHom.range_eq_map, range_subtype] using hm
  have hcuts : cuts.Nonempty := by
    by_contra hc
    have he : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp hc
    apply hHne
    rw [hH, he, cutStabilizer]
    simp
  obtain ⟨k,hk,f,hf⟩ := exists_linearFlag_of_cuts b cuts hcuts
  refine ⟨hK,k,hk,f,?_⟩
  apply map_injective (f := (slEquivLinear (m + 1)).toMonoidHom) (slEquivLinear (m + 1)).injective
  rw [map_map]
  exact hH.trans hf.symm

/-- The source central involutions act innerly on each actual binary
linear model, so the Sylow-center centralizer lies in the literal M_L. -/
theorem PreExclusionSource.linear_centralizer_le
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := ((s.ordinary hL).actions z hz hzne).2
  apply d.ordinary_inner_centralizer_le hG hu h s.centralizer_sylow s.odd_core hL hz hzne α ha
  let K := d.L.subgroupOf d.G1
  let a : K ≃* LinearGroup n :=
    (subgroupOfEquivOfLe d.L_component.1).trans (e.trans (slEquivLinear n))
  obtain ⟨P,hP,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hL.1
  have hfix (x : K) (hx : x ∈ Q) : α x = x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ha]
    have hxP : (x : d.G1) ∈ P := by
      change x ∈ (Q : Subgroup K) at hx
      rw [hQ] at hx
      exact hx
    exact mul_inv_eq_iff_eq_mul.mpr ((h115 z hz hzne).central x (mem_map_of_mem d.G1.subtype hxP)).symm
  let R := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨t,_,ht⟩ := sylow_fixing_inner hn R (MulAut.congr a α) (by
    rintro _ ⟨x,hx,rfl⟩
    change a (α (a.symm (a x))) = a x
    rw [a.symm_apply_apply,hfix x hx])
  refine ⟨a.symm t, ?_⟩
  apply MulEquiv.ext
  intro x
  apply a.injective
  have hh := congrArg (fun β : MulAut (LinearGroup n) => β (a x)) ht
  simpa using hh.symm

/-- The complete initial binary-linear row of 15.1.20(3e), including
its actual flag and centralizer clauses, for either source prime. -/
theorem PreExclusionSource.ordinary20_of_linear
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    d.Ordinary20Alternatives := by
  have ho := s.ordinary hL
  exact .linear n hn e
    (s.linear_flag_overgroup (h := h) (by omega) e d.ML ho.sylow_le_local ho.local_proper)
    (s.linear_centralizer_le (h := h) hG hM hu hL hn e)

/-- The model predicate supplied by 1.1.5 yields the full initial linear
row; field identification and the projective-to-linear comparison are proved. -/
theorem PreExclusionSource.ordinary20_of_binaryPSL
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL d.L n 2) :
    d.Ordinary20Alternatives := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact s.ordinary20_of_linear (h := h) hG hM hu hL hn
    ((e.trans (Atlas.fieldEquivPSL n k)).trans (projectiveEquivSL (by omega)))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
