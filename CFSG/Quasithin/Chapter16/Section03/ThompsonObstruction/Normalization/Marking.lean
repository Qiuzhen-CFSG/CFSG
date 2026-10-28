module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Marking.Restriction
public import Theory.SpecificGroups.SymmetricEight.TranspositionMarking
/-!
# Choosing the compatible S₈ marking

Restrict the chosen Sylow C_T(t) to C_{K⟨z⟩}(z), using the relative
normality of the actual enlargement. Under the original marking this gives
a Sylow subgroup of C_{S₈}((01)). Conjugate that Sylow to the standard
C₂ × C₂ × D₈. The conjugation fixes (01) and preserves the embedded A₈
and A₆, so composing the original equivalence gives a new full marking.

The preimage of (01)(23) then lies in T and centralizes T ∩ K⟨z⟩.
The explicit image equation for T_L = T ∩ L identifies its image with the
standard Sylow's intersection with the marked A₆. Both centralizer Sylow
equations, and the actual enlargement, are retained unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the marking
preceding Lemma 16.3.12, printed pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.SymmetricEight.TranspositionMarking
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Change only the permutation coordinates, preserving the marked pair,
both embedded alternating groups, and every intrinsic field of the enlargement. -/
noncomputable def MarkedEnlargement.relabel (d : MarkedEnlargement z t L)
    (a : Equiv.Perm (Fin 8)) (ha : a ∈ swapCentralizer) : MarkedEnlargement z t L := {
  d with
  equiv := d.equiv.trans (MulAut.conj a)
  enlargement_image := by
    change ((enlargement t L).subgroupOf (enlargement t L ⊔ zpowers z)).map
      ((MulAut.conj a).toMonoidHom.comp d.equiv.toMonoidHom) = _
    rw [← map_map, d.enlargement_image]
    exact Normal.map_conj_eq (alternatingGroup (Fin 8)) a
  component_image := by
    change (L.subgroupOf (enlargement t L ⊔ zpowers z)).map
      ((MulAut.conj a).toMonoidHom.comp d.equiv.toMonoidHom) = _
    rw [← map_map, d.component_image]
    exact conj_six ha
  involution_image := by
    change (MulAut.conj a) (d.equiv _) = _
    rw [d.involution_image]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ha) }

/-- The marked A₆ intersection is the image of the actual subgroup T_L. -/
theorem MarkedEnlargement.componentSylow_image (d : MarkedEnlargement z t L) (T : Sylow 2 G) :
    ((componentSylow T L).subgroupOf (enlargement t L ⊔ zpowers z)).map d.equiv.toMonoidHom =
      (((T : Subgroup G).subgroupOf (enlargement t L ⊔ zpowers z)).map
        d.equiv.toMonoidHom) ⊓ markedA6 := by
  change (((T : Subgroup G).subgroupOf (enlargement t L ⊔ zpowers z) ⊓
    L.subgroupOf (enlargement t L ⊔ zpowers z)).map d.equiv.toMonoidHom) = _
  rw [Subgroup.map_inf _ _ _ d.equiv.injective, d.component_image]

/-- Choose a full marking whose double transposition lies in T and centralizes
T_L. No compatibility assumption on the original marking is needed. -/
theorem Selected.exists_compatible_marking [Finite G] (s : Selected T z t L) :
    ∃ d : MarkedEnlargement z t L,
      d.u ∈ (T : Subgroup G) ∧ d.u ∈ centralizer (componentSylow T L : Set G) := by
  obtain ⟨S, hS⟩ := s.exists_markingSylow
  obtain ⟨a, ha, hconj⟩ := exists_conjugating_marking S
  let d := s.marked.relabel a ha
  let X := enlargement t L ⊔ zpowers z
  have hImage : ((T : Subgroup G).subgroupOf X).map d.equiv.toMonoidHom =
      (standardSylow : Subgroup swapCentralizer).map swapCentralizer.subtype := by
    change ((T : Subgroup G).subgroupOf X).map
      ((MulAut.conj a).toMonoidHom.comp s.marked.equiv.toMonoidHom) = _
    rw [← map_map, ← hS]
    exact hconj
  have huT : d.u ∈ (T : Subgroup G) := by
    have hm := delta_mem
    rw [← hImage] at hm
    obtain ⟨x, hx, he⟩ := hm
    have he' : x = d.equiv.symm doubleTransposition :=
      d.equiv.injective (he.trans (d.equiv.apply_symm_apply _).symm)
    change (d.equiv.symm doubleTransposition : G) ∈ (T : Subgroup G)
    rw [← he']
    exact hx
  refine ⟨d, huT, ?_⟩
  have hTL := d.componentSylow_image T
  rw [hImage] at hTL
  intro x hx
  have hxX : x ∈ X := (le_sup_left : enlargement t L ≤ X)
    (ComponentTransfer.le_layerClosure _ _ hx.2)
  let v : X := ⟨x, hxX⟩
  have hm : d.equiv v ∈ (standardSylow : Subgroup swapCentralizer).map swapCentralizer.subtype := by
    have hv : d.equiv v ∈ ((componentSylow T L).subgroupOf X).map d.equiv.toMonoidHom :=
      mem_map_of_mem _ hx
    rw [hTL] at hv
    exact hv.1
  have hc := delta_centralizes (d.equiv v) hm
  have he : v * d.equiv.symm doubleTransposition = d.equiv.symm doubleTransposition * v := by
    apply d.equiv.injective
    simpa only [map_mul, d.equiv.apply_symm_apply] using hc
  exact congrArg Subtype.val he

end CFSG.Quasithin.Chapter16.ThompsonObstruction
