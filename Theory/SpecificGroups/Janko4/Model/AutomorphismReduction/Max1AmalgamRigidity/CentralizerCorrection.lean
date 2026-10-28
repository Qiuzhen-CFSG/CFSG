module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares
import Mathlib.Tactic.Group

/-!
# Correcting the full marked involution centralizer

Let C be the full centralizer of the max1 kernel pair v from `Core`.
Every automorphism fixing v can be corrected by conjugation by an element
of C so that its right displacement on C belongs to the marked line ⟨v⟩.

The certified max2 normal closure is a normal two-subgroup of the literal
matrix-unit centralizer. Full generation transports its centralizer equality
into that group, and containment in the intrinsic two-core gives
C_C(O₂(C)) ≤ ⟨v⟩. The unsquared characteristic restriction normalizes the
conjugation image on O₂(C). Self-normalization realizes that restriction by
an actual local element; correcting by its inverse fixes O₂(C) pointwise.
The remaining displacement centralizes O₂(C), hence lies in the marked line.

The literal matrix-unit centralizer is compared with the full centralizer
in `Model` using its injective inclusion and exact range. The certified
fusion a = g v g⁻¹ then transports it by conjugation by g⁻¹, including the
marked involution and its powers. No identification with max1 is used.

Source context: GLS3 Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The concrete ATLAS max2 generation,
normal-closure and action certificates are supplied by the raw imports;
the max1 pair fusion is proved in `Simplicity.Max1Fusion.Seeds`.
-/

set_option backward.isDefEq.respectTransparency true
public section

namespace Janko4.Max1AmalgamRigidity
open Subgroup
open OuterReduction.FixedGenerator.NormalizerSquares
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel Cardinality.localX Cardinality.localY Cardinality.localKernelSeed

private noncomputable def generatedEquiv : localSubgroup ≃* involutionCentralizer :=
  (MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv

/-- The normal closure gives the marked-line bound, stronger than exponent two. -/
private theorem twoCore_centralizer_le_line :
    centralizer (involutionTwoCore : Set involutionCentralizer) ≤
      zpowers centralInvolution := by
  let N := localNormalClosure.map generatedEquiv.toMonoidHom
  have hn : N.Normal := localNormalClosure_normal.map _ generatedEquiv.surjective
  have hp : IsPGroup 2 N := localNormalClosure_isPGroup.map _
  have hN : N ≤ involutionTwoCore := le_sSup ⟨hn, hp⟩
  intro x hx
  obtain ⟨y, rfl⟩ := generatedEquiv.surjective x
  have hy : y ∈ centralizer (localNormalClosure : Set localSubgroup) := by
    intro z hz
    apply generatedEquiv.injective
    simpa only [map_mul] using
      (centralizer_le hN hx) (generatedEquiv z) (mem_map_of_mem _ hz)
  rw [localNormalClosure_centralizer_eq_zpowers] at hy
  have hmap := mem_map_of_mem generatedEquiv.toMonoidHom hy
  rw [MonoidHom.map_zpowers] at hmap
  exact hmap

private theorem displacement_mem_centralizer {G : Type*} [Group G]
    (N : Subgroup G) [N.Characteristic] (beta : MulAut G)
    (hb : MulAut.characteristic N beta = 1) (t : G) :
    t⁻¹ * beta t ∈ centralizer (N : Set G) := by
  have hfix (n : G) (hn : n ∈ N) : beta n = n :=
    congrArg N.subtype (DFunLike.congr_fun hb (⟨n, hn⟩ : N))
  intro n hn
  have h := hfix (t * n * t⁻¹) ((inferInstance : N.Normal).conj_mem n hn t)
  simp only [map_mul, map_inv, hfix n hn] at h
  have hh := congrArg (fun z : G => t⁻¹ * z * beta t) h
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- Realize the restriction itself, without taking a power of the automorphism. -/
private theorem literal_correction (alpha : MulAut involutionCentralizer) :
    ∃ c : involutionCentralizer, ∀ t : involutionCentralizer,
      t⁻¹ * (MulAut.conj c⁻¹ * alpha) t ∈ zpowers centralInvolution := by
  have ha : MulAut.characteristic involutionTwoCore alpha ∈
      involutionTwoCoreAction.range :=
    localTwoCoreActionSelfNormalizer localTwoCoreCentralizerControl
      (characteristic_mem_normalizer_conjNormal_range involutionTwoCore alpha)
  obtain ⟨c, hc⟩ := ha
  let beta : MulAut involutionCentralizer := MulAut.conj c⁻¹ * alpha
  have hb : MulAut.characteristic involutionTwoCore beta = 1 := by
    change (MulAut.characteristic involutionTwoCore) (MulAut.conj c⁻¹ * alpha) = 1
    rw [map_mul, characteristic_conj_eq_conjNormal]
    change involutionTwoCoreAction c⁻¹ * MulAut.characteristic involutionTwoCore alpha = 1
    rw [map_inv, hc, inv_mul_cancel]
  exact ⟨c, fun t => twoCore_centralizer_le_line
    (displacement_mem_centralizer involutionTwoCore beta hb t)⟩

private theorem map_centralizer_singleton {G : Type*} [Group G]
    (f : G ≃* G) (x : G) :
    (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({f x} : Set G) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({x} : Set G) f.toMonoidHom
  · intro y hy
    refine mem_map.mpr ⟨f.symm y, mem_centralizer_singleton_iff.mpr ?_,
      f.apply_symm_apply y⟩
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

private noncomputable def literalEquivFirst :
    involutionCentralizer ≃* centralizer ({Janko4.a} : Set Model) :=
  (MonoidHom.ofInjective centralizerToModel_injective).trans
    (MulEquiv.subgroupCongr centralizerToModel_range)

private theorem first_conjugates_to_mark {g : Model}
    (hg : Janko4.a = g * v * g⁻¹) :
    MulAut.conj g⁻¹ Janko4.a = v := by
  change g⁻¹ * Janko4.a * (g⁻¹)⁻¹ = v
  rw [hg]
  group

/-- Conjugation by g⁻¹ takes C(a) to C(v), since a = g v g⁻¹. -/
private noncomputable def literalEquivMarked (g : Model)
    (hg : Janko4.a = g * v * g⁻¹) : involutionCentralizer ≃* C :=
  literalEquivFirst.trans
    (((MulAut.conj g⁻¹).subgroupMap (centralizer ({Janko4.a} : Set Model))).trans
      (MulEquiv.subgroupCongr (by
        change (centralizer ({Janko4.a} : Set Model)).map
          (MulAut.conj g⁻¹).toMonoidHom = C
        rw [map_centralizer_singleton, first_conjugates_to_mark hg])))

private theorem literalEquivMarked_involution (g : Model)
    (hg : Janko4.a = g * v * g⁻¹) :
    (literalEquivMarked g hg centralInvolution : Model) = v :=
  first_conjugates_to_mark hg

private theorem marked_correction (e : involutionCentralizer ≃* C)
    (he : (e centralInvolution : Model) = v) (phi : MulAut C) :
    ∃ c : C, ∀ t : C,
      ((t⁻¹ * (MulAut.conj c⁻¹ * phi) t : C) : Model) ∈ zpowers v := by
  let alpha : MulAut involutionCentralizer := (e.trans phi).trans e.symm
  obtain ⟨c, hc⟩ := literal_correction alpha
  refine ⟨e c, fun t => ?_⟩
  have hd := mem_map_of_mem e.toMonoidHom (hc (e.symm t))
  rw [MonoidHom.map_zpowers] at hd
  have hd' : t⁻¹ * (MulAut.conj (e c)⁻¹ * phi) t ∈
      zpowers (e centralInvolution) := by
    change e ((e.symm t)⁻¹ * (c⁻¹ * e.symm (phi (e (e.symm t))) * (c⁻¹)⁻¹)) ∈
      zpowers (e centralInvolution) at hd
    change t⁻¹ * ((e c)⁻¹ * phi t * ((e c)⁻¹)⁻¹) ∈ _
    simpa only [map_mul, map_inv, e.apply_symm_apply] using hd
  have h := mem_map_of_mem C.subtype hd'
  rwa [MonoidHom.map_zpowers, Subgroup.subtype_apply, he] at h

/-- An automorphism fixing the marked involution has a local inner correction
whose right displacement on the full ambient centralizer lies in ⟨v⟩. -/
theorem centralizer_correction (alpha : MulAut Model) (hv : alpha v = v) :
    ∃ c : C, ∀ t ∈ C,
      t⁻¹ * (MulAut.conj (c : Model)⁻¹ * alpha) t ∈ Subgroup.zpowers v := by
  obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.pair_fuses_first
    matrixA_mul_self matrixB_pow_four
  have hga : Janko4.a = g * v * g⁻¹ := hg
  have hC : C.map alpha.toMonoidHom = C := by
    rw [map_centralizer_singleton, hv]
  let phi : MulAut C := (alpha.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  obtain ⟨c, hc⟩ := marked_correction (literalEquivMarked g hga)
    (literalEquivMarked_involution g hga) phi
  exact ⟨c, fun t ht => hc ⟨t, ht⟩⟩

end Janko4.Max1AmalgamRigidity
