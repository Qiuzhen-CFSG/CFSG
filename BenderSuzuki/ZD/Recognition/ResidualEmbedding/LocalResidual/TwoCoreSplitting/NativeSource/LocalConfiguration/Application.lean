module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.LocalConfiguration.FixedPair
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction

/-!
# The Section 17 local-configuration outputs at the counting interface

The fixed set and normalizer bound are transported to the literal centralizer
circle subtype used by the model-counting theorems. The final application
constructs the local data from the original selected involutions; it assumes
only their earlier source fusion and the universal Lemma 16.7, never the
local data or its noncentrality, fixed set or normalizer conclusion.

Source: GLS, Volume 4, Chapter 2, Lemma 17.2(e,f).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17.NativeSource
open Subgroup PFAppendixIII Theory.GroupTheory PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The exact fixed-set contract consumed by the model counting theorem. -/
public theorem localData_fixed_pair_iff
    (h : IsProductDisconnected Z M) (h16 : SectionSixteenNormalizer Z M)
    (d : TwoCoreLocalData Z M) :
    ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M) := by
  intro gamma
  have hh := (localData_fixed_pair_and_normalizer h h16 d).1
  have hm : residualPairStabilizer M d.t ⊓
        centralizerClosure Z (d.t * ((d.u : M) : G)) ≤ MulAction.stabilizer G gamma ↔
      gamma ∈ fixedPointsOfSubgroup G (G ⧸ M)
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z (d.t * ((d.u : M) : G))) := by
    constructor
    · intro hle g hg
      exact MulAction.mem_stabilizer_iff.mp (hle hg)
    · intro hf g hg
      exact MulAction.mem_stabilizer_iff.mpr (hf g hg)
  rw [hm, hh]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, MulAction.Quotient.smul_mk,
    smul_eq_mul, mul_one]

/-- The literal internal normalizer bound used by the PSL₂, Suzuki and
unitary odd-subgroup theorems. -/
public theorem localData_intrinsic_normalizer
    (h : IsProductDisconnected Z M) (h16 : SectionSixteenNormalizer Z M)
    (d : TwoCoreLocalData Z M) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
    let t : L := ⟨d.t, t_mem_twisted_circle d⟩
    normalizer (H : Set L) ≤ H ⊔ zpowers t := by
  let L := centralizerClosure Z (d.t * ((d.u : M) : G))
  let D := residualPairStabilizer M d.t ⊓ L
  let H := D.subgroupOf L
  let t : L := ⟨d.t, t_mem_twisted_circle d⟩
  change normalizer (H : Set L) ≤ H ⊔ zpowers t
  have hfixed := (localData_fixed_pair_and_normalizer h h16 d).1
  have hN : normalizer (D : Set G) ⊓ L ≤ D ⊔ zpowers d.t :=
    normalizer_inf_circle_le_twisted_pair_join (h.involutions d.t d.t_mem)
      d.t_not_mem L D (t_mem_twisted_circle d) hfixed
  have hmap : H.map L.subtype = D := map_subgroupOf_eq_of_le inf_le_right
  have hmapJoin : (H ⊔ zpowers t).map L.subtype = D ⊔ zpowers d.t := by
    rw [Subgroup.map_sup, hmap, MonoidHom.map_zpowers]
    rfl
  intro x hx
  have hxN : (x : G) ∈ normalizer (D : Set G) := by
    have hh := le_normalizer_map L.subtype (mem_map_of_mem L.subtype hx)
    rwa [hmap] at hh
  have hxJoin := hN ⟨hxN, x.property⟩
  rw [← hmapJoin] at hxJoin
  obtain ⟨y, hy, he⟩ := hxJoin
  exact (show y = x from Subtype.ext he) ▸ hy

/-- Application to the original Section 16 selected elements. It constructs
the local configuration and discharges both geometric premises of the
Section 17 model-counting consumer. -/
public theorem selected_local_data_geometry
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hg : ResidualGeneration Z M) (h16 : SectionSixteenNormalizer Z M)
    (t : G) (ht : t ∈ Z) (htM : t ∉ M)
    (u : residualPairIn M t) (hu : orderOf u = 2)
    (htu : Commute t ((u : M) : G)) (z : M) (hz : (z : G) ∈ Z)
    (hzu : Commute (z : G) ((u : M) : G))
    (hfusion : IsConj ((u : M) : G) (t * ((u : M) : G))) :
    let d := localDataOfSelected h r hg t ht htM u hu htu z hz hzu hfusion
    (∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M)) ∧
    (let L := centralizerClosure Z (d.t * ((d.u : M) : G))
      let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
      let t : L := ⟨d.t, t_mem_twisted_circle d⟩
      normalizer (H : Set L) ≤ H ⊔ zpowers t) := by
  dsimp only
  exact ⟨localData_fixed_pair_iff h h16 _, localData_intrinsic_normalizer h h16 _⟩

end BenderSuzuki.ZD.Section17.NativeSource
