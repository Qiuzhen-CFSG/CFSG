module

public import Theory.GroupTheory.ReducedNormal.SubspaceEquiv
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitFixedSpace

/-!
# Ambient subgroup consequences of binary orbit identities

The original inclusion preserves intersections and detects equality.
Fixed subspaces become relative centralizers, full linear commutators
become full group commutators, and conjugate subspaces become the original
conjugate subgroups. Thus the orbit-centralizer and TI conclusions retain
the original ambient group, rather than an unspecified isomorphic image.

Source: Aschbacher–Smith, Lemma 3.2.2(3)–(5), combined manuscript of
1 March 2004, printed p.579; the linear results are D.3.4(3),(4),(6).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H : Subgroup G)

theorem subspaceImage_inf (I J : Submodule (ZMod 2) (Additive (ModuleGroup H))) :
    subspaceImage H (I ⊓ J) = subspaceImage H I ⊓ subspaceImage H J := by
  ext g
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨_, ⟨v, hv.1, rfl⟩, rfl⟩, ⟨_, ⟨v, hv.2, rfl⟩, rfl⟩⟩
  · rintro ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, ⟨_, ⟨w, hw, rfl⟩, he⟩⟩
    have he' : w = v := Subtype.ext (Subtype.ext he)
    subst w
    exact ⟨_, ⟨v, ⟨hv, hw⟩, rfl⟩, rfl⟩

@[simp] theorem subspaceImage_bot : subspaceImage H ⊥ = ⊥ := by
  ext g
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    change Additive.ofMul v = 0 at hv
    exact congrArg (fun w : Additive (ModuleGroup H) => w.toMul.val.val) hv
  · rintro rfl
    exact (subspaceImage H ⊥).one_mem

theorem subspaceImage_injective : Function.Injective (subspaceImage H) := by
  intro I J he
  ext v
  constructor
  · intro hv
    have hm : v.toMul.val.val ∈ subspaceImage H J :=
      he ▸ mem_map_of_mem H.subtype (mem_map_of_mem (ModuleGroup H).subtype hv)
    obtain ⟨_, ⟨w, hw, rfl⟩, hwv⟩ := hm
    have hvw : w = v.toMul := Subtype.ext (Subtype.ext hwv)
    change Additive.ofMul w ∈ J at hw
    simpa only [hvw, ofMul_toMul] using hw
  · intro hv
    have hm : v.toMul.val.val ∈ subspaceImage H I :=
      he.symm ▸ mem_map_of_mem H.subtype (mem_map_of_mem (ModuleGroup H).subtype hv)
    obtain ⟨_, ⟨w, hw, rfl⟩, hwv⟩ := hm
    have hvw : w = v.toMul := Subtype.ext (Subtype.ext hwv)
    change Additive.ofMul w ∈ I at hw
    simpa only [hvw, ofMul_toMul] using hw

theorem mem_reduced_fixedSpace_iff (X : Subgroup G) (hXH : X ≤ H)
    (v : Additive (ModuleGroup H)) :
    v ∈ fixedSpace (representation H) (X.subgroupOf H) ↔
      v.toMul.val.val ∈ centralizer (X : Set G) := by
  constructor
  · intro hv x hx
    have he := congrArg (fun w : Additive (ModuleGroup H) => w.toMul.val.val)
      (hv ⟨⟨x, hXH hx⟩, hx⟩)
    change x * v.toMul.val.val * x⁻¹ = v.toMul.val.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val * v.toMul.val.val * x.val.val⁻¹ = v.toMul.val.val
    rw [hv x.val.val x.property, mul_inv_cancel_right]

theorem subspaceImage_inf_fixedSpace
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H))) (X : Subgroup G) (hXH : X ≤ H) :
    subspaceImage H (I ⊓ fixedSpace (representation H) (X.subgroupOf H)) =
      subspaceImage H I ⊓ centralizer (X : Set G) := by
  ext g
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨_, ⟨v, hv.1, rfl⟩, rfl⟩,
      (mem_reduced_fixedSpace_iff H X hXH _).mp hv.2⟩
  · rintro ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, hc⟩
    exact ⟨_, ⟨v, ⟨hv, (mem_reduced_fixedSpace_iff H X hXH _).mpr hc⟩, rfl⟩, rfl⟩

/-- Full linear commutator generation is full ambient group commutator generation. -/
theorem subspaceImage_eq_commutator
    (W : Submodule (ZMod 2) (Additive (ModuleGroup H))) (X : Subgroup G) (hXH : X ≤ H)
    (hW : X.subgroupOf H ≤ subspaceStabilizer (representation H) W)
    (hfull : subspaceCommutator (representation H) W (X.subgroupOf H) = W) :
    subspaceImage H W = ⁅subspaceImage H W, X⁆ := by
  apply le_antisymm
  · let C : Submodule (ZMod 2) (Additive (ModuleGroup H)) :=
      AddSubgroup.toZModSubmodule 2
        (((⁅subspaceImage H W, X⁆).comap H.subtype).comap (ModuleGroup H).subtype).toAddSubgroup
    have hc : subspaceCommutator (representation H) W (X.subgroupOf H) ≤ C := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, v, hv, rfl⟩
      change x.val * v.toMul.val.val * x.val⁻¹ / v.toMul.val.val ∈ ⁅subspaceImage H W, X⁆
      rw [Subgroup.commutator_comm]
      have hx' : (x : G) ∈ X := hx
      have hv' : v.toMul.val.val ∈ subspaceImage H W :=
        mem_map_of_mem H.subtype (mem_map_of_mem (ModuleGroup H).subtype hv)
      simpa only [commutatorElement_def, div_eq_mul_inv] using commutator_mem_commutator hx' hv'
    rw [hfull] at hc
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact hc hv
  · exact le_normalizer_iff_commutator_le_left.mp (subspaceImage_normalizes H X hXH W hW)

/-- The full ambient orbit is generated by its actor commutators. -/
theorem seedOrbit_eq_commutator (X : Subgroup G) (hXH : X ≤ H)
    [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I) :
    componentOrbit (subspaceImage H I) H = ⁅componentOrbit (subspaceImage H I) H, X⁆ := by
  have hn : (⊤ : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    rw [normalizer_eq_top]
  have hm := subspaceImage_orbitSpan H H le_rfl I
  rw [subgroupOf_self] at hm
  rw [← hm]
  exact subspaceImage_eq_commutator H _ X hXH
    (orbitSpan_component_invariant _ hn hI) (orbitSpan_full_commutator _ hn hI)

/-- The centralizer in the full orbit is generated by conjugates of the
centralizer in the original seed, retaining the original ambient group. -/
theorem seedOrbit_inf_centralizer [Finite G] (X : Subgroup G) (hXH : X ≤ H)
    [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I) :
    componentOrbit (subspaceImage H I) H ⊓ centralizer (X : Set G) =
      componentOrbit (subspaceImage H I ⊓ centralizer (X : Set G)) H := by
  have he := congrArg (subspaceImage H)
    (orbitSpan_inf_fixedSpace (representation H) (X.subgroupOf H) hI)
  have hm (J : Submodule (ZMod 2) (Additive (ModuleGroup H))) :=
    subspaceImage_orbitSpan H H le_rfl J
  simp only [subgroupOf_self] at hm
  rw [subspaceImage_inf_fixedSpace H _ X hXH, hm, hm,
    subspaceImage_inf_fixedSpace H _ X hXH] at he
  exact he

/-- Vanishing seed centralizer gives the literal TI alternative under H. -/
theorem seed_ti_of_centralizer_eq_bot (X : Subgroup G) (hXH : X ≤ H)
    [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (hc : subspaceImage H I ⊓ centralizer (X : Set G) = ⊥) (g : H) :
    subspaceImage H I ⊓ (subspaceImage H I).map (MulAut.conj (g : G)).toMonoidHom = ⊥ ∨
      (subspaceImage H I).map (MulAut.conj (g : G)).toMonoidHom = subspaceImage H I := by
  have hf : I ⊓ fixedSpace (representation H) (X.subgroupOf H) = ⊥ := by
    apply subspaceImage_injective H
    rw [subspaceImage_inf_fixedSpace H _ X hXH, hc, subspaceImage_bot]
  rcases ti_of_inf_fixedSpace_eq_bot (representation H) (X.subgroupOf H) hI hf g with h | h
  · left
    have he := congrArg (subspaceImage H) h
    rwa [subspaceImage_inf, subspaceImage_map, subspaceImage_bot] at he
  · right
    have he := congrArg (subspaceImage H) h
    rwa [subspaceImage_map] at he

end Theory.GroupTheory.ReducedNormal
