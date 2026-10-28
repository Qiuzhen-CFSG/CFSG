module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.NativeInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.OuterRadical
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups

/-!
# Source placement in an actual M₂₂ hexad

Apply the native solvable-normal Sylow-overgroup classification to the actual
images of J = K∩M and L₁. Relative normality of K in H and T≤M imply that
T normalizes J; the native design-normalizer theorem therefore makes T*
stabilize the same hexad. One conjugating element marks both that hexad and
the parabolic. Both the pair–hexad and three-pair classes are retained.

The literal component two-core lies in J. Independently, the supplied Sylow
arrangement puts the radical of any K₁T inside T. This proves the required
radical containment without strengthening the solvable-overgroup hypothesis.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973).
-/

public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
namespace Setup
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : Setup H K L₁ T G₁ M)
include s

omit [Finite G] in
theorem sylow_normalizes_overlap : T ≤ normalizer (K ⊓ M : Set G) := by
  let := s.component_normal
  exact (le_inf
    ((le_sup_right.trans s.seed_join_sylow_le).trans
      (le_normalizer_of_normal_subgroupOf s.component_le))
    (s.sylow_le_M.trans M.le_normalizer)).trans inf_normalizer_le_normalizer_inf

theorem design_sylow_normalizes_overlap :
    (Source.starImage H T).map s.designHom ≤
      normalizer ((markedImage K (K ⊓ M) s.model).map
        M22ValueBound.Concrete.inclusion : Set m22DesignAut) := by
  rw [← s.starDesignMap_image _ inf_le_left]
  change ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map s.designHom ≤ _
  rw [map_map]
  change (T.subgroupOf H).map s.starDesignMap ≤ _
  have hn : T.subgroupOf H ≤ normalizer ((K ⊓ M).subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht j hj
    exact (le_normalizer_iff (H := T) (K := K ⊓ M)).mp
      s.sylow_normalizes_overlap t.val ht j.val hj
  exact (map_mono hn).trans (le_normalizer_map _)

omit [Finite G] in
theorem radical_le_sylow (K₁ : Subgroup G) :
    ((K₁ ⊔ T).subgroupOf H).pCoreIn 2 ≤ T.subgroupOf H := by
  have hT : (s.sylow : Subgroup H) ≤ (K₁ ⊔ T).subgroupOf H := by
    rw [s.sylow_eq]
    exact comap_mono le_sup_right
  have h := pCoreIn_le_sylow _ (s.sylow.subtype hT)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] at h
  rwa [s.sylow_eq] at h

theorem component_core_le_overlap : K.pCoreIn 2 ≤ K ⊓ M := by
  refine le_inf (pCoreIn_le 2 K) ?_
  let := s.component_normal
  obtain ⟨P, hP⟩ := s.sylow.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e : K.subgroupOf H ≃* K := subgroupOfEquivOfLe s.component_le
  have hc : pCore 2 K ≤ (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup K) :=
    pCore_isPGroup.le_sylow_of_normal _
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨x, hx, he⟩ := hc hk
  have hxT : x.val.val ∈ T := by
    rw [hP, s.sylow_eq] at hx
    exact hx
  exact s.sylow_le_M (show k.val ∈ T from (congrArg Subtype.val he) ▸ hxT)

theorem exists_native_placement (V₃ : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃) :
    ∃ B ∈ m22Blocks,
      markedImage K (K ⊓ M) s.model ≤ MulAction.stabilizer M22 B ∧
      IsCoatom ((markedImage K (K ⊓ M) s.model).subgroupOf
        (MulAction.stabilizer M22 B)) ∧
      m22HexadPointwiseKernel B ≤ markedImage K (K ⊓ M) s.model ∧
      Nat.card (markedImage K (K ⊓ M) s.model) = 384 ∧
      (Source.starImage H T).map s.designHom ≤ MulAction.stabilizer m22DesignAut B := by
  obtain ⟨B, hB, hX, hmax, hker, hcard, hnorm⟩ :=
    M22SolvableSylow.hexad_of_solvable_normal_three
      (markedImage K (K ⊓ M) s.model) (markedImage K L₁ s.model)
      s.native_seed_le_overlap s.native_seed_normal s.native_seed_solvable
      (s.native_seed_three_dvd V₃ hne hgen) s.native_overlap_contains_sylow
  exact ⟨B, hB, hX, hmax, hker, hcard,
    s.design_sylow_normalizes_overlap.trans hnorm⟩

omit [Finite G] in
theorem overlap_le_hexadLift {B : Finset (Fin 22)}
    (hX : markedImage K (K ⊓ M) s.model ≤ MulAction.stabilizer M22 B) :
    K ⊓ M ≤ hexadLift K s.model B := by
  intro x hx
  exact ⟨⟨x, hx.1⟩, hX (mem_map_of_mem _ hx), rfl⟩

/-- A single native conjugator marks the hexad and the two parabolic possibilities. -/
theorem marked_conjugacy {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hX : markedImage K (K ⊓ M) s.model ≤ MulAction.stabilizer M22 B)
    (hk : m22HexadPointwiseKernel B ≤ markedImage K (K ⊓ M) s.model)
    (hc : Nat.card (markedImage K (K ⊓ M) s.model) = 384) :
    ∃ g : M22, B = g • m22Hexad123 ∧
      (markedImage K (K ⊓ M) s.model =
        M22SolvableSylow.pairHexad.map (MulAut.conj g).toMonoidHom ∨
       markedImage K (K ⊓ M) s.model =
        M22ValueBound.Concrete.second.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, hg⟩ := M22SolvableSylow.LocalClassification.hexad_conjugacy hB
    (markedImage K (K ⊓ M) s.model) hX hc s.native_overlap_contains_sylow
  refine ⟨g, ?_, hg⟩
  apply Eq.symm
  apply M22SolvableSylow.invariant_six_eq_hexad hB (g • m22Hexad123)
    (by rw [Finset.card_smul_finset]; exact m22Block_card _ m22Hexad123_mem)
  apply hk.trans
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rcases hg with hg | hg
  · rw [hg]
    exact map_mono (show M22SolvableSylow.pairHexad ≤
      MulAction.stabilizer M22 m22Hexad123 from inf_le_left)
  · rw [hg]
    exact map_mono M22ValueBound.Concrete.PartitionStructure.second_le_hexad

end Setup
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
