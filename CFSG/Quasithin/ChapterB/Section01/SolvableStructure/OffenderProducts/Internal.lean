module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.SupIndep

/-!
# Internal coordinates of solvable FF factors

The compatible group and linear equivalences in `SolvableFFFactors` give
independent subgroup factors and independent commutator supports. Distinct
factors commute; their displacement on another support lies in both supports,
so they fix that support pointwise. Normality here is relative to the offender
subgroup, not to the ambient group.

These are conditional consequences of the concrete witness for
Aschbacher–Smith, B.1.8(1)–(2), printed p. 70 (PDF p. 81).
-/

@[expose] public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

noncomputable def productInclusion : ((i : Fin d.count) → d.factor i) →* G :=
  (offenderSubgroup ρ).subtype.comp d.groupProduct.toMonoidHom

@[simp] theorem productInclusion_single (i : Fin d.count) (g : d.factor i) :
    d.productInclusion (Pi.mulSingle i g) = (g : G) := d.groupProduct_single i g

theorem productInclusion_injective : Function.Injective d.productInclusion :=
  Subtype.val_injective.comp d.groupProduct.injective

theorem factor_le_offenderSubgroup (i : Fin d.count) : d.factor i ≤ offenderSubgroup ρ := by
  intro g hg
  have := (d.groupProduct (Pi.mulSingle i ⟨g, hg⟩)).property
  rwa [d.groupProduct_single] at this

theorem factor_commute {i j : Fin d.count} (hij : i ≠ j)
    (g : d.factor i) (h : d.factor j) : Commute (g : G) (h : G) := by
  simpa only [d.productInclusion_single] using
    (Pi.mulSingle_commute hij g h).map d.productInclusion

theorem iSup_factor : (⨆ i, d.factor i) = offenderSubgroup ρ := by
  apply le_antisymm (iSup_le d.factor_le_offenderSubgroup)
  intro g hg
  let x := d.groupProduct.symm ⟨g, hg⟩
  have hc : Pairwise fun i j => ∀ (a : d.factor i) (b : d.factor j),
      Commute ((d.factor i).subtype a) ((d.factor j).subtype b) :=
    fun _ _ hij => d.factor_commute hij
  let f := MonoidHom.noncommPiCoprod (fun i => (d.factor i).subtype) hc
  have hf : f = d.productInclusion := by
    apply MonoidHom.pi_ext
    intro i a
    simp only [f, MonoidHom.noncommPiCoprod_mulSingle, d.productInclusion_single, Subgroup.subtype_apply]
  have hr : f.range = ⨆ i, d.factor i := by
    change (MonoidHom.noncommPiCoprod (fun i => (d.factor i).subtype) hc).range = _
    rw [MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
  rw [← hr]
  refine ⟨x, ?_⟩
  rw [hf]
  exact congrArg Subtype.val (d.groupProduct.apply_symm_apply ⟨g, hg⟩)

theorem factors_independent : iSupIndep d.factor := by
  intro i
  let K := (Pi.evalMonoidHom (fun j => d.factor j) i).ker.map d.productInclusion
  have hK : (⨆ (j) (_ : j ≠ i), d.factor j) ≤ K := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro g hg
    refine ⟨Pi.mulSingle (M := fun k => d.factor k) j ⟨g, hg⟩, ?_, d.productInclusion_single j ⟨g, hg⟩⟩
    change Pi.mulSingle (M := fun k => d.factor k) j (⟨g, hg⟩ : d.factor j) i = 1
    simp [hji]
  apply Disjoint.mono_right hK
  rw [Subgroup.disjoint_def]
  intro g hgi hgK
  obtain ⟨x, hx, hxg⟩ := hgK
  have he : x = Pi.mulSingle i (⟨g, hgi⟩ : d.factor i) :=
    d.productInclusion_injective (hxg.trans (d.productInclusion_single i ⟨g, hgi⟩).symm)
  have hi : x i = 1 := hx
  rw [he, Pi.mulSingle_eq_same] at hi
  exact congrArg Subtype.val hi

noncomputable def sumInclusion :
    ((i : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor i)) →ₗ[ZMod 2] V :=
  (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)).subtype.comp d.moduleSum.toLinearMap

@[simp] theorem sumInclusion_single (i : Fin d.count)
    (v : subspaceCommutator ρ ⊤ (d.factor i)) :
    d.sumInclusion (Pi.single i v) = (v : V) := d.moduleSum_single i v

theorem sumInclusion_injective : Function.Injective d.sumInclusion :=
  Subtype.val_injective.comp d.moduleSum.injective

theorem supports_independent : iSupIndep (fun i => subspaceCommutator ρ ⊤ (d.factor i)) := by
  intro i
  let K := (LinearMap.proj i :
    ((j : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor j)) →ₗ[ZMod 2]
      subspaceCommutator ρ ⊤ (d.factor i)).ker.map d.sumInclusion
  have hK : (⨆ (j) (_ : j ≠ i), subspaceCommutator ρ ⊤ (d.factor j)) ≤ K := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro v hv
    refine ⟨(Pi.single (M := fun k => subspaceCommutator ρ ⊤ (d.factor k)) j ⟨v, hv⟩ : (k : Fin d.count) → subspaceCommutator ρ ⊤ (d.factor k)), ?_, d.sumInclusion_single j ⟨v, hv⟩⟩
    change Pi.single (M := fun k => subspaceCommutator ρ ⊤ (d.factor k)) j (⟨v, hv⟩ : subspaceCommutator ρ ⊤ (d.factor j)) i = 0
    simp [hji]
  apply Disjoint.mono_right hK
  rw [Submodule.disjoint_def]
  intro v hvi hvK
  obtain ⟨x, hx, hxv⟩ := hvK
  have he : x = Pi.single i (⟨v, hvi⟩ : subspaceCommutator ρ ⊤ (d.factor i)) :=
    d.sumInclusion_injective (hxv.trans (d.sumInclusion_single i ⟨v, hvi⟩).symm)
  have hi : x i = 0 := hx
  rw [he, Pi.single_eq_same] at hi
  exact congrArg Subtype.val hi

theorem iSup_support : (⨆ i, subspaceCommutator ρ ⊤ (d.factor i)) =
    subspaceCommutator ρ ⊤ (offenderSubgroup ρ) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    intro v hv
    have := (d.moduleSum (Pi.single i ⟨v, hv⟩)).property
    rwa [d.moduleSum_single] at this
  · intro v hv
    let x := d.moduleSum.symm ⟨v, hv⟩
    have he : d.sumInclusion x = v :=
      congrArg Subtype.val (d.moduleSum.apply_symm_apply ⟨v, hv⟩)
    rw [← he, ← Finset.univ_sum_single x, map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      (le_iSup (fun j => subspaceCommutator ρ ⊤ (d.factor j)) i)
        (by rw [d.sumInclusion_single]; exact (x i).property)

theorem support_finrank (i : Fin d.count) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.factor i)) = 2 := by
  rw [(d.naturalEquiv i).finrank_eq]
  simp

theorem factor_preserves_other_support {i j : Fin d.count} (hij : i ≠ j)
    (g : d.factor i) {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ (d.factor j)) :
    ρ (g : G) v ∈ subspaceCommutator ρ ⊤ (d.factor j) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, w, _, rfl⟩ := hv
    have hc := d.factor_commute hij g ⟨h, hh⟩
    have he : ρ (g : G) (ρ h w) = ρ h (ρ (g : G) w) := by
      simpa only [map_mul, Module.End.mul_apply] using congrArg (fun a => ρ a w) hc.eq
    rw [map_sub, he]
    exact Submodule.subset_span ⟨h, hh, ρ (g : G) w, Submodule.mem_top, rfl⟩
  | zero => simp
  | add x y hx hy hfx hfy => simpa only [map_add] using Submodule.add_mem _ hfx hfy
  | smul a x hx hfx => simpa only [map_smul] using Submodule.smul_mem _ a hfx

theorem factor_fixes_other_support {i j : Fin d.count} (hij : i ≠ j)
    (g : d.factor i) {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ (d.factor j)) :
    ρ (g : G) v = v := by
  have hi : ρ (g : G) v - v ∈ subspaceCommutator ρ ⊤ (d.factor i) :=
    Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩
  have hj : ρ (g : G) v - v ∈ subspaceCommutator ρ ⊤ (d.factor j) :=
    Submodule.sub_mem _ (d.factor_preserves_other_support hij g hv) hv
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp
    (d.supports_independent.pairwiseDisjoint hij)) _ hi hj)

theorem support_le_fixedSpace_other {i j : Fin d.count} (hij : i ≠ j) :
    subspaceCommutator ρ ⊤ (d.factor j) ≤ fixedSpace ρ (d.factor i) := by
  intro v hv g
  exact d.factor_fixes_other_support hij g hv

theorem factor_preserves_support (i : Fin d.count) (g : d.factor i)
    {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ (g : G) v ∈ subspaceCommutator ρ ⊤ (d.factor i) := by
  rw [d.naturalEquiv_action i g ⟨v, hv⟩]
  exact Subtype.property _

theorem factor_le_support_stabilizer (i j : Fin d.count) :
    d.factor i ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.factor j)) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  by_cases hij : i = j
  · subst j
    exact d.factor_preserves_support i ⟨g, hg⟩ hv
  · rw [d.factor_fixes_other_support hij ⟨g, hg⟩ hv]
    exact hv

theorem offenderSubgroup_le_support_stabilizer (j : Fin d.count) :
    offenderSubgroup ρ ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.factor j)) := by
  rw [← d.iSup_factor]
  exact iSup_le fun i => d.factor_le_support_stabilizer i j

theorem support_ne_bot (i : Fin d.count) :
    subspaceCommutator ρ ⊤ (d.factor i) ≠ ⊥ := by
  intro h
  have hd := d.support_finrank i
  rw [h] at hd
  simp at hd

theorem factor_injective : Function.Injective d.factor := by
  intro i j he
  by_contra hn
  have hd := d.supports_independent.pairwiseDisjoint hn
  change Disjoint (subspaceCommutator ρ ⊤ (d.factor i))
    (subspaceCommutator ρ ⊤ (d.factor j)) at hd
  rw [he, disjoint_self] at hd
  exact d.support_ne_bot j hd

theorem commutator_finrank [FiniteDimensional (ZMod 2) V] :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) =
      2 * d.count := by
  rw [← d.moduleSum.finrank_eq, Module.finrank_pi_fintype]
  simp only [d.support_finrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

theorem productInclusion_conj_single (x : (i : Fin d.count) → d.factor i)
    (i : Fin d.count) (a : d.factor i) :
    d.productInclusion x * (a : G) * (d.productInclusion x)⁻¹ =
      ((x i * a * (x i)⁻¹ : d.factor i) : G) := by
  have he : x * Pi.mulSingle i a * x⁻¹ = Pi.mulSingle i (x i * a * (x i)⁻¹) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have := congrArg d.productInclusion he
  simpa only [map_mul, map_inv, d.productInclusion_single] using this

theorem factor_normal_in_offenderSubgroup (i : Fin d.count) :
    ((d.factor i).subgroupOf (offenderSubgroup ρ)).Normal := by
  refine ⟨fun a ha g => ?_⟩
  change (g : G) * (a : G) * (g : G)⁻¹ ∈ d.factor i
  let x := d.groupProduct.symm g
  have hx : d.productInclusion x = (g : G) :=
    congrArg Subtype.val (d.groupProduct.apply_symm_apply g)
  rw [← hx, d.productInclusion_conj_single x i ⟨a, ha⟩]
  exact Subtype.property _

/-- Coordinatewise inclusion into the internal group product. -/
def coordinateInclusion (A : Fin d.count → Subgroup G) (hA : ∀ i, A i ≤ d.factor i) :
    ((i : Fin d.count) → A i) →* ((i : Fin d.count) → d.factor i) where
  toFun x i := ⟨x i, hA i (x i).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def subproductInclusion (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : ((i : Fin d.count) → A i) →* G :=
  d.productInclusion.comp (d.coordinateInclusion A hA)

theorem coordinateInclusion_injective (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : Function.Injective (d.coordinateInclusion A hA) := by
  intro x y h
  funext i
  apply Subtype.ext
  exact congrArg (fun z : d.factor i => (z : G)) (congrFun h i)

@[simp] theorem subproductInclusion_single (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) (i : Fin d.count) (a : A i) :
    d.subproductInclusion A hA (Pi.mulSingle i a) = (a : G) := by
  have he : d.coordinateInclusion A hA (Pi.mulSingle i a) =
      Pi.mulSingle i (⟨a, hA i a.property⟩ : d.factor i) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [coordinateInclusion]
    · simp [coordinateInclusion, hj]
  change d.productInclusion (d.coordinateInclusion A hA (Pi.mulSingle i a)) = _
  rw [he, d.productInclusion_single]

theorem subproductInclusion_injective (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : Function.Injective (d.subproductInclusion A hA) :=
  d.productInclusion_injective.comp (d.coordinateInclusion_injective A hA)

theorem subproductInclusion_range (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : (d.subproductInclusion A hA).range = ⨆ i, A i := by
  have hc : Pairwise fun i j => ∀ (a : A i) (b : A j),
      Commute ((A i).subtype a) ((A j).subtype b) := by
    intro i j hij a b
    exact d.factor_commute hij ⟨a, hA i a.property⟩ ⟨b, hA j b.property⟩
  have hf : MonoidHom.noncommPiCoprod (fun i => (A i).subtype) hc =
      d.subproductInclusion A hA := by
    apply MonoidHom.pi_ext
    intro i a
    simp only [MonoidHom.noncommPiCoprod_mulSingle, d.subproductInclusion_single,
      Subgroup.subtype_apply]
  rw [← hf, MonoidHom.noncommPiCoprod_range]
  simp only [Subgroup.range_subtype]

/-- A literal Cartesian product of subgroups of different factors is internally
isomorphic to their join. -/
noncomputable def subproductEquiv (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : ((i : Fin d.count) → A i) ≃* (⨆ i, A i : Subgroup G) :=
  (MonoidHom.ofInjective (d.subproductInclusion_injective A hA)).trans
    (MulEquiv.subgroupCongr (d.subproductInclusion_range A hA))

@[simp] theorem subproductEquiv_apply (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) (x : (i : Fin d.count) → A i) :
    (d.subproductEquiv A hA x : G) = d.subproductInclusion A hA x := rfl

@[simp] theorem subproductEquiv_single (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) (i : Fin d.count) (a : A i) :
    (d.subproductEquiv A hA (Pi.mulSingle i a) : G) = (a : G) :=
  d.subproductInclusion_single A hA i a

theorem subproduct_card (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) :
    Nat.card (⨆ i, A i : Subgroup G) = ∏ i, Nat.card (A i) := by
  rw [← Nat.card_congr (d.subproductEquiv A hA).toEquiv, Nat.card_pi]

theorem subgroups_independent (A : Fin d.count → Subgroup G)
    (hA : ∀ i, A i ≤ d.factor i) : iSupIndep A :=
  d.factors_independent.mono hA

end CFSG.Quasithin.ChapterB.SolvableFFFactors
