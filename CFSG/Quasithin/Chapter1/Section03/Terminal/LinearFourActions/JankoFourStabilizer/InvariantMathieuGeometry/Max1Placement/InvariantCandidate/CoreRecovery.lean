module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Candidates
public import Theory.GroupTheory.SylowKernelCore

/-!
# Recovering a max1 candidate from the center of the section's two-core

For a local L₄(2) section A, the proposed intrinsic invariant is Z(O₂(A)),
viewed as a subgroup of the ambient group. Ambient isomorphisms preserve it.
Every candidate's two-core is elementary abelian of order 2048, by transport
from the certified literal max1 subgroup.

Two geometric assertions remain separate obligations. Inside a candidate H,
its two-core must be the unique elementary subgroup of order 2048 centralizing
Z(O₂(A)). In the ambient J₄, the centralizer of Z(O₂(A)) and the normalizer of
O₂(H) must lie in H. Together these assertions recover H from A; the assembly
in `InvariantCandidate` proves uniqueness and then invariance.

These assertions are not consequences of the intrinsic centralizer theorem in
`LocalStructure.Mathieu`: that theorem has ambient group max1, not J₄.
No J₄ simplicity, order, parity, or ambient-normalizer assertion is assumed
implicitly in the definitions or transport lemmas below.

Source: Aschbacher–Smith A.3.12(17) and its Sylow-overgroup proof, printed
pp.47–48, and the proof of 1.3.9, p.514. GLS3 Table 5.3i identifies the
normalizer of O₂(C(2B)) as E₂¹¹.M₂₄. Applying that entry to arbitrary
candidates still requires an actual embedding and centralizer calculation.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels
universe u v
variable {G : Type u} [Group G] {G' : Type v} [Group G']

/-- The center of the intrinsic two-core, embedded back into the ambient group. -/
@[expose] def coreCenter (A : Subgroup G) : Subgroup G :=
  A.pCoreIn 2 ⊓ centralizer (A.pCoreIn 2 : Set G)

/-- The intersection definition is exactly the embedded center. -/
theorem coreCenter_eq_mapped_center (A : Subgroup G) :
    coreCenter A = (center (A.pCoreIn 2)).map (A.pCoreIn 2).subtype := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hx.2 y y.property)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    intro z hz
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)

private theorem map_centralizer (U : Subgroup G) (e : G ≃* G') :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set G') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg e.toMonoidHom (hy w hw)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hx (e y) (mem_map_of_mem e.toMonoidHom hy)

/-- The embedded center of the two-core is preserved by ambient isomorphisms. -/
theorem map_coreCenter (A : Subgroup G) (e : G ≃* G') :
    (coreCenter A).map e.toMonoidHom = coreCenter (A.map e.toMonoidHom) := by
  rw [coreCenter, map_inf _ _ _ e.injective, map_centralizer,
    map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective]
  rfl

/-- Elementary order-2048 subgroups in the ambient centralizer of Z(O₂(A)). -/
@[expose] def centralElementary (A : Subgroup G) : Set (Subgroup G) :=
  {E | E ≤ centralizer (coreCenter A : Set G) ∧
    IsElementaryAbelian 2 E ∧ Nat.card E = 2048}

/-- Transport preserves the centralizer, elementary structure, and exact order. -/
theorem map_mem_centralElementary {A E : Subgroup G}
    (hE : E ∈ centralElementary A) (e : G ≃* G') :
    E.map e.toMonoidHom ∈ centralElementary (A.map e.toMonoidHom) := by
  let := hE.2.1
  refine ⟨?_, IsElementaryAbelian.map e.toMonoidHom, ?_⟩
  · have h := map_mono (f := e.toMonoidHom) hE.1
    rwa [map_centralizer, map_coreCenter] at h
  · rw [card_map_of_injective e.injective]
    exact hE.2.2

/-- Normality of the intrinsic core gives the lower ambient-normalizer bound. -/
theorem le_normalizer_core (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) := by
  apply le_normalizer_iff.mpr
  intro h hh x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
    (inferInstance : (pCore 2 H).Normal).conj_mem y hy ⟨h, hh⟩, rfl⟩

/-- Every candidate inherits the certified max1 two-core structure. -/
theorem core_elementary_and_card_of_candidate {A H : Subgroup G}
    (hH : H ∈ candidates A) :
    IsElementaryAbelian 2 (H.pCoreIn 2) ∧ Nat.card (H.pCoreIn 2) = 2048 := by
  obtain ⟨e⟩ := hH.2.1
  have he : IsElementaryAbelian 2 (pCore 2 certifiedMathieuSubgroup) := by
    change IsElementaryAbelian 2
      (pCore 2 (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    rw [← Janko4.LocalStructure.localKernel_eq_twoCore]
    exact Janko4.LocalStructure.localKernel_elementary _ _
  have hc : Nat.card (pCore 2 certifiedMathieuSubgroup) = 2048 := by
    change Nat.card
      (pCore 2 (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) = _
    rw [← Janko4.LocalStructure.localKernel_eq_twoCore]
    exact Janko4.Cardinality.localKernel_card _ _
  let := he
  have heH : IsElementaryAbelian 2 (pCore 2 H) := by
    have h := IsElementaryAbelian.map (p := 2) (A := pCore 2 certifiedMathieuSubgroup)
      e.symm.toMonoidHom
    rwa [pCore_map_iso] at h
  let := heH
  refine ⟨IsElementaryAbelian.map H.subtype, ?_⟩
  rw [pCoreIn, card_map_of_injective H.subtype_injective]
  rw [← card_map_of_injective (K := pCore 2 H) (f := e.toMonoidHom) e.injective, pCore_map_iso]
  exact hc

/-- Outstanding intrinsic geometry: recover the candidate core within H from
Z(O₂(A)). This uses the Sylow-local field of `candidates`; it does not assert
uniqueness of H or any ambient normalizer bound. -/
@[expose] def IntrinsicCoreRecovery : Prop :=
  ∀ (A H : Subgroup Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 → H ∈ candidates A →
    H.pCoreIn 2 ≤ centralizer (coreCenter A : Set Janko4.Model) ∧
      ∀ E ∈ centralElementary A, E ≤ H → E = H.pCoreIn 2

/-- Outstanding ambient geometry: two containment bounds inside J₄. These are
not the intrinsic normality and centralizer statements inside a max1 copy. -/
@[expose] def AmbientCoreRecovery : Prop :=
  ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (H : Subgroup Janko4.Model),
    ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
    A ∈ ChapterA.Section03.localCComponents S → H ∈ candidates A →
    centralizer (coreCenter A : Set Janko4.Model) ≤ H ∧
      normalizer (H.pCoreIn 2 : Set Janko4.Model) ≤ H

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
