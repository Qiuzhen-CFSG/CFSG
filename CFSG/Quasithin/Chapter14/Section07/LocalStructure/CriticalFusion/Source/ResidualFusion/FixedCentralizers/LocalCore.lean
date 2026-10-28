module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.PCoreImage

/-!
# The literal C.2.3 setup in the fixed-element centralizer

Set H_u = H ∩ C_G(u) and R_u = O₂(H_u). Since H_u is normal in H,
R_u = O₂(H) ∩ H_u and H normalizes R_u. Maximal two-locality forces
the normalizer of every nontrivial characteristic subgroup of R_u to be H.
Restricting this control to G_u gives C(G_u,R_u) ≤ H_u and proves that
R_u is radical in G_u. The normal closure of R_u inside H_u is R_u itself,
so the required Sylow condition is automatic. These are all the actual
hypotheses of C.2.3; the C.2.7 component classification is not assumed here.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed pp.1071–1072; Hypothesis C.2.3, p.144.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

/-- The actual R_u of the source, using the established K T_u = H ∩ G_u. -/
def fixedCore (u : F.U) : Subgroup G := (F.H ⊓ d.fixedCentralizer u : Subgroup G).pCoreIn 2

theorem fixedCore_ne_bot (u : F.U) (hu : (u : G) ∈ d.U₀) : d.fixedCore u ≠ ⊥ := by
  unfold fixedCore
  rw [d.fixedCentralizer_inter_H u hu]
  exact d.fixedJoin_core_ne_bot u

theorem H_normalizes_fixedCore (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) : F.H ≤ normalizer (d.fixedCore u : Set G) :=
  ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp
    (d.fixedCentralizer_inter_H_normal u hu hfix)).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem fixedCore_eq_inter (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) :
    d.fixedCore u = F.H.pCoreIn 2 ⊓ (F.H ⊓ d.fixedCentralizer u : Subgroup G) := by
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes inf_le_left
      ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp
        (d.fixedCentralizer_inter_H_normal u hu hfix))) (pCoreIn_le 2 _)
  · rw [inf_comm]
    exact inf_pCoreIn_le_of_le 2 inf_le_left

theorem fixedCore_normalizer_eq (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    normalizer (d.fixedCore u : Set G) = F.H := by
  have hH := d.H_normalizes_fixedCore u hu hfix
  exact le_antisymm (hmax.2 ⟨_, d.fixedCore_ne_bot u hu, isPGroup_pCoreIn 2 _, rfl⟩ hH) hH

theorem fixedCore_characteristicNormalizerClosure (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    (d.fixedCore u).characteristicNormalizerClosure = F.H := by
  apply le_antisymm
  · apply (characteristicNormalizerClosure_le_iff _ _).mpr
    intro C hC hne
    let := hC
    have hH : F.H ≤ normalizer (C.map (d.fixedCore u).subtype : Set G) :=
      (d.H_normalizes_fixedCore u hu hfix).trans
        (normalizer_le_normalizer_characteristic_image _ C)
    exact hmax.2 ⟨_, fun he => hne ((C.map_eq_bot_iff_of_injective
      (d.fixedCore u).subtype_injective).mp he),
      ((isPGroup_pCoreIn 2 _).to_subgroup C).map _, rfl⟩ hH
  · rw [← d.fixedCore_normalizer_eq u hu hfix hmax]
    exact normalizer_le_characteristicNormalizerClosure_self _ (d.fixedCore_ne_bot u hu)

theorem fixedCore_intrinsic_characteristic_control (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    ((d.fixedCore u).subgroupOf (d.fixedCentralizer u)).characteristicNormalizerClosure ≤
      (F.H ⊓ d.fixedCentralizer u : Subgroup G).subgroupOf (d.fixedCentralizer u) := by
  have hRGu : d.fixedCore u ≤ d.fixedCentralizer u := (pCoreIn_le 2 _).trans inf_le_right
  have h := characteristicNormalizerClosure_subgroupOf_le hRGu
    (d.fixedCore_characteristicNormalizerClosure u hu hfix hmax).le
  intro x hx
  exact ⟨h hx, x.property⟩

theorem fixedCore_radical (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    IsPRadical 2 ((d.fixedCore u).subgroupOf (d.fixedCentralizer u)) := by
  have hRGu : d.fixedCore u ≤ d.fixedCentralizer u := (pCoreIn_le 2 _).trans inf_le_right
  refine ⟨?_, ?_⟩
  · intro he
    apply d.fixedCore_ne_bot u hu
    simpa only [map_subgroupOf_eq_of_le hRGu, Subgroup.map_bot] using
      congrArg (map (d.fixedCentralizer u).subtype) he
  · apply map_injective (d.fixedCentralizer u).subtype_injective
    change ((normalizer ((d.fixedCore u).subgroupOf (d.fixedCentralizer u) :
      Set (d.fixedCentralizer u))).pCoreIn 2).map (d.fixedCentralizer u).subtype = _
    rw [map_pCoreIn_of_injective 2 _ (d.fixedCentralizer u).subtype
      (d.fixedCentralizer u).subtype_injective,
      ← subgroupOf_normalizer_eq hRGu, subgroupOf_map_subtype,
      d.fixedCore_normalizer_eq u hu hfix hmax, map_subgroupOf_eq_of_le hRGu]
    rfl

theorem fixedCore_normalClosure (u : F.U) :
    (normalClosure ((d.fixedCore u).subgroupOf (F.H ⊓ d.fixedCentralizer u : Subgroup G) :
      Set (F.H ⊓ d.fixedCentralizer u : Subgroup G))).map (F.H ⊓ d.fixedCentralizer u : Subgroup G).subtype =
      d.fixedCore u := by
  have he : (d.fixedCore u).subgroupOf (F.H ⊓ d.fixedCentralizer u : Subgroup G) =
      pCore 2 (F.H ⊓ d.fixedCentralizer u : Subgroup G) :=
    comap_map_eq_self_of_injective (F.H ⊓ d.fixedCentralizer u : Subgroup G).subtype_injective _
  rw [he, normalClosure_eq_self]
  rfl

/-- Hypothesis C.2.3 holds on the literal R_u, G_u and H_u. In particular,
normal closure is taken inside H_u and the radical equality inside G_u. -/
theorem fixedCentralizer_pushingUpSetup (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hne : (u : G) ≠ 1) (hfix : d.FixedModuloPoint u)
    (hmax : IsMaximalTwoLocal F.H) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u : Subgroup G) := by
  refine ⟨d.fixedCentralizer_sqtk u hne, (pCoreIn_le 2 _).trans inf_le_right,
    inf_le_right, d.fixedCore_radical u hu hfix hmax,
    d.fixedCore_intrinsic_characteristic_control u hu hfix hmax, ?_⟩
  rw [d.fixedCore_normalClosure u]
  exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 _, le_rfl,
    fun P _ hRP hPR => le_antisymm hPR hRP⟩
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
