module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.AtlasPort.LinearGroups.G2.BinaryException
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Marking the G₂ component Sylow subgroup

The actual model isomorphism, or the quotient map in the central-cover case,
can be conjugated so that the given component Sylow subgroup maps onto the
standard positive roots intersected with the derived group. Sylow restriction
uses subnormality in H; the ambient Sylow subgroup may permute components.
The conjugation changes neither the kernel nor the range of the model map.

This constructs the model and Sylow data needed by the parabolic coordinates.
Invariance of the two parabolics is a separate geometric assertion.
Source: Aschbacher–Smith 1.1.5(3)(a,b), printed pp.501–502, and the proof of
2.3.9(7), printed p.526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

/-- A genuine model map with the supplied Sylow intersection marked.
Parabolic invariance and characteristic two are not fields of this structure. -/
structure SylowModel (L S : Subgroup G) where
  field : Type
  fieldInstance : Field field
  finiteField : Finite field
  characteristic : CharP field 2
  exponent : ℕ
  exponent_pos : 1 ≤ exponent
  field_card : Nat.card field = 2 ^ exponent
  modelMap : L →* Atlas.G2.Model field
  model_range : modelMap.range = commutator (Atlas.G2.Model field)
  model_kernel : modelMap.ker = ⊥ ∨
    (Nat.card field = 4 ∧ modelMap.ker = center L ∧
      center L = pCore 2 L ∧ pCore 2 L ≠ ⊥)
  sylow_image : (S.subgroupOf L).map modelMap =
    Atlas.G2.unipotent ⊓ commutator (Atlas.G2.Model field)

attribute [instance] SylowModel.fieldInstance SylowModel.finiteField SylowModel.characteristic

private theorem mark_model_sylow {K F : Type*} [Group K] [Finite K]
    [Field F] [Finite F] [CharP F 2]
    (f : K →* Atlas.G2.Model F)
    (hf : f.range = commutator (Atlas.G2.Model F)) (R : Sylow 2 K) :
    ∃ g : K →* Atlas.G2.Model F,
      g.range = commutator (Atlas.G2.Model F) ∧ g.ker = f.ker ∧
      (R : Subgroup K).map g =
        Atlas.G2.unipotent ⊓ commutator (Atlas.G2.Model F) := by
  let D := commutator (Atlas.G2.Model F)
  let fD : K →* D := f.codRestrict D (fun x => by
    change f x ∈ commutator (Atlas.G2.Model F)
    rw [← hf]
    exact ⟨x, rfl⟩)
  have hsurj : Function.Surjective fD := by
    intro y
    obtain ⟨x, hx⟩ := (show y.val ∈ f.range from hf.symm ▸ y.property)
    exact ⟨x, Subtype.ext hx⟩
  let Q : Sylow 2 D := R.mapSurjective (f := fD) hsurj
  obtain ⟨T, hT⟩ := (Atlas.G2.LieParabolicSetup.sylow (F := F)).exists_subgroupOf_eq_of_normal D
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq D Q T
  let a : MulAut D := MulAut.conj u
  let g : K →* Atlas.G2.Model F := D.subtype.comp (a.toMonoidHom.comp fD)
  have honto : Function.Surjective (a.toMonoidHom.comp fD) := a.surjective.comp hsurj
  refine ⟨g, ?_, ?_, ?_⟩
  · change (D.subtype.comp (a.toMonoidHom.comp fD)).range = D
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr honto, ← MonoidHom.range_eq_map,
      range_subtype]
  · ext x
    change (a (fD x) : Atlas.G2.Model F) = 1 ↔ f x = 1
    constructor
    · intro hx
      have hd : a (fD x) = 1 := Subtype.ext hx
      have he := a.injective (hd.trans (map_one a).symm)
      exact congrArg Subtype.val he
    · intro hx
      have hd : fD x = 1 := Subtype.ext hx
      rw [hd, map_one]
      rfl
  · change ((R : Subgroup K).map ((D.subtype).comp (a.toMonoidHom.comp fD))) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map]
    have hh := congrArg Sylow.toSubgroup hu
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    have hQ : (Q : Subgroup D) = (R : Subgroup K).map fD :=
      Sylow.coe_mapSurjective hsurj R
    change (Q : Subgroup D).map a.toMonoidHom = (T : Subgroup D) at hh
    rw [← hQ, hh, hT, subgroupOf_map_subtype]
    rfl

/-- Construct the actual map and Sylow marking in both permitted G₂ cases.
The binary case maps into G₂(2)′; every allowed central cover of G₂(4)
retains its full central two-kernel. -/
theorem exists_sylowModel {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (hmodel : IsModelCase L) :
    Nonempty (SylowModel L ((S : Subgroup H).map H.subtype)) := by
  let := h.finite
  obtain ⟨R, hR⟩ := h.component_sylow
  rcases hmodel with ⟨F, hF, hfin, n, hn, hcard, ⟨e⟩⟩ | ⟨hZ, hO, F, hF, hfin, hcard, ⟨e⟩⟩
  · let := hF
    let := hfin
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let D := commutator (Atlas.G2.Model F)
    let f : L →* Atlas.G2.Model F := D.subtype.comp e.toMonoidHom
    have hf : f.range = D := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
        ← MonoidHom.range_eq_map, range_subtype]
    obtain ⟨g, hgr, hgk, hgs⟩ := mark_model_sylow f hf R
    have hfk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr
      (Subtype.val_injective.comp e.injective)
    exact ⟨{
      field := F
      fieldInstance := hF
      finiteField := hfin
      characteristic := inferInstance
      exponent := n
      exponent_pos := hn
      field_card := hcard
      modelMap := g
      model_range := hgr
      model_kernel := Or.inl (hgk.trans hfk)
      sylow_image := hR ▸ hgs }⟩
  · let := hF
    let := hfin
    let := Fintype.ofFinite F
    have hpow : Nat.card F = 2 ^ 2 := hcard
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hpow)
    let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect (by omega)
    let f : L →* Atlas.G2.Model F := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    have hf : f.range = commutator (Atlas.G2.Model F) := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact MonoidHom.range_eq_top.mpr (e.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨g, hgr, hgk, hgs⟩ := mark_model_sylow f hf R
    have hfk : f.ker = pCore 2 L := by
      change (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker = _
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact ⟨{
      field := F
      fieldInstance := hF
      finiteField := hfin
      characteristic := inferInstance
      exponent := 2
      exponent_pos := by decide
      field_card := hpow
      modelMap := g
      model_range := hgr
      model_kernel := Or.inr ⟨hcard, (hgk.trans hfk).trans hZ.symm, hZ, hO⟩
      sylow_image := hR ▸ hgs }⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
