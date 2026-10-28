module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryTerminal
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration

/-!
# Literal geometry of the ordinary root normalizer

The marked `Sp₄` carrier is embedded through the actual component inclusion.
The standard long root therefore becomes the literal source root.  The point
parabolic is the relative normalizer inside the component, and its solvable
residual is the literal second subgroup.  The two local residuals generate the
whole ordinary component.  These identities retain the source inclusions and
do not identify the second component with the later `KZ` component.

Source: Aschbacher--Smith 4.3.6, printed pp.614--615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

namespace OrdinarySymplecticMarking
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The marked matrix carrier embedded through the original `K ≤ H ≤ G`. -/
@[expose] noncomputable def modelEmbedding (m : OrdinarySymplecticMarking c n) :
    Sp m.Field →* G :=
  (c.H.subtype.comp c.K.subtype).comp m.componentEquiv.symm.toMonoidHom

theorem modelEmbedding_injective (m : OrdinarySymplecticMarking c n) :
    Function.Injective m.modelEmbedding :=
  c.H.subtype_injective.comp (c.K.subtype_injective.comp m.componentEquiv.symm.injective)

theorem modelEmbedding_range (m : OrdinarySymplecticMarking c n) :
    m.modelEmbedding.range = c.K.map c.H.subtype := by
  have hr : m.componentEquiv.symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr m.componentEquiv.symm.surjective
  rw [modelEmbedding, MonoidHom.range_comp,
    hr, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]

theorem planeLocal_image (m : OrdinarySymplecticMarking c n) :
    (planeLocal (F := m.Field)).map m.modelEmbedding = L := by
  have hLH : L ≤ c.H := c.le_component.trans (map_subtype_le c.K)
  have hLK : L.subgroupOf c.H ≤ c.K := by
    intro x hx
    obtain ⟨k, hk, he⟩ := c.le_component hx
    exact (Subtype.ext he : k = x) ▸ hk
  have hm : (planeLocal (F := m.Field)).map m.componentEquiv.symm.toMonoidHom =
      (L.subgroupOf c.H).subgroupOf c.K :=
    (map_symm_eq_iff_map_eq _ (e := m.componentEquiv)).mpr m.original_local
  rw [modelEmbedding, ← map_map, hm, ← map_map,
    map_subgroupOf_eq_of_le hLK, map_subgroupOf_eq_of_le hLH]

theorem root_image (m : OrdinarySymplecticMarking c n) :
    (RootSubgroup.group (F := m.Field) 0).map m.modelEmbedding = m.root := by
  rw [modelEmbedding, ← map_map, ← map_map, ← comap_equiv_eq_map_symm']
  rfl

/-- The literal root retains the order of the marked field. -/
theorem root_card (m : OrdinarySymplecticMarking c n) :
    Nat.card m.root = 2 ^ n := by
  rw [← m.root_image, card_map_of_injective m.modelEmbedding_injective,
    RootSubgroup.card, m.card]

theorem root_isPGroup (m : OrdinarySymplecticMarking c n) :
    IsPGroup 2 m.root :=
  IsPGroup.of_card m.root_card

theorem root_ne_bot (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    m.root ≠ ⊥ := by
  intro hroot
  have hc := m.root_card
  rw [hroot, card_bot] at hc
  have hgt : 2 < 2 ^ n :=
    (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  omega

/-- This is an ambient two-local, not merely the normalizer in the matrix model. -/
theorem rootNormalizer_twoLocal (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    IsTwoLocal m.rootNormalizer :=
  ⟨m.root, m.root_ne_bot hn, m.root_isPGroup, rfl⟩

theorem pointParabolic_image (m : OrdinarySymplecticMarking c n) :
    (pointParabolic (F := m.Field)).map m.modelEmbedding =
      c.K.map c.H.subtype ⊓ m.rootNormalizer := by
  have hroot : m.root ≤ m.modelEmbedding.range :=
    m.root_image ▸ map_le_range m.modelEmbedding (RootSubgroup.group (F := m.Field) 0)
  have hpre : m.rootNormalizer.comap m.modelEmbedding = pointParabolic := by
    rw [rootNormalizer, comap_normalizer_eq_of_le_range hroot, ← m.root_image,
      comap_map_eq_self_of_injective m.modelEmbedding_injective,
      RootNormalizerResidual.normalizer_zero_eq]
  rw [← hpre, map_comap_eq, m.modelEmbedding_range]

private theorem map_embedded_residual {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Injective f) (P : Subgroup X) :
    ((solvableResidual P).map P.subtype).map f =
      (solvableResidual (P.map f)).map (P.map f).subtype := by
  let e := P.equivMapOfInjective f hf
  have hh := congrArg (fun D => D.map (P.map f).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  rw [map_map] at hh
  rw [map_map]
  convert hh using 1
  congr 1

theorem pointLocal_image (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    (pointLocal (F := m.Field)).map m.modelEmbedding = m.second := by
  rw [← pointParabolic_solvableResidual_eq m.card hn,
    map_embedded_residual _ m.modelEmbedding_injective, m.pointParabolic_image]
  rfl

theorem original_sup_second (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    L ⊔ m.second = c.K.map c.H.subtype := by
  calc
    L ⊔ m.second = (planeLocal (F := m.Field)).map m.modelEmbedding ⊔
        (pointLocal (F := m.Field)).map m.modelEmbedding :=
      congrArg₂ (· ⊔ ·) m.planeLocal_image.symm (m.pointLocal_image hn).symm
    _ = c.K.map c.H.subtype := by
      rw [← Subgroup.map_sup, sup_comm, locals_sup_eq_top m.card hn, ← MonoidHom.range_eq_map,
        m.modelEmbedding_range]

theorem second_not_normalized (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ¬ (T : Subgroup G) ≤ normalizer (m.second : Set G) :=
  c.ordinary_second_not_normalized D (m.original_sup_second hn)

end OrdinarySymplecticMarking

/-- The literal matrix geometry discharges the two-generator premise in the
root-normalizer contradiction. The remaining root-core and FF-module premises
are explicit; this is not yet the unconditional source theorem 4.3.6. -/
theorem SourceConfiguration.ordinary_false_of_root_module
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    {n : ℕ} (hn : 1 < n) (m : OrdinarySymplecticMarking c n) (KZ : Subgroup G)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hU : m.rootSpan = m.second.pCoreIn 2)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (himage : KZ ≤ m.second ⊔ m.rootCore)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False :=
  c.ordinary_false_of_root_normalizer D m KZ hT (m.original_sup_second hn)
    hseed hU hQ hKZ himage hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
