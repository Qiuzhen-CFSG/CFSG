module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.NormalizerTransport
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Sylow marking for the G₂ branches of E.6.8

The actual component Sylow intersection is transported to the standard derived
G₂ Sylow group by conjugating the model map. The existing intrinsic invariance
proof then supplies both pullback parabolics. Full G₂ over fields larger than
two is compared with its derived subgroup using perfectness; the binary branch
keeps the genuine G₂(2)′ carrier. In the cover branch quasisimplicity identifies
the two-core with the entire center, without bounding that center's order.

The marking argument adapts `Chapter2...G2.Geometry.Marking` to the E.6 Sylow
intersection, without requiring the unrelated Chapter 2 local setup. No
normalization of the component by all of Q is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and 1.1.5(3)(a,b), pp.501–502.
The concrete model APIs use the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
open Chapter2.ComponentRefinement.LieType.G2
variable {G : Type*} [Group G]

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
theorem exists_sylowModel [Finite G] {L Q : Subgroup G}
    (R : Sylow 2 L) (hR : (R : Subgroup L) = Q.subgroupOf L)
    (hmodel : IsModelCase L) : Nonempty (SylowModel L Q) := by
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


variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- The source Sylow intersection supplies invariant parabolic coordinates. -/
theorem exists_coordinates (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) (hm : IsModelCase L) :
    Nonempty (ParabolicCoordinates L Q) := by
  obtain ⟨R, hR⟩ := component_sylow_intersection h hU hL
  have he : (R : Subgroup L) = Q.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hR, subgroupOf_map_subtype, hQ, inf_comm]
  obtain ⟨d⟩ := exists_sylowModel R he hm
  exact ⟨d.coordinatesOfStabilizerInvariant
    Atlas.G2.SylowParabolicInvariance.restricted_parabolics_invariant⟩

/-- Perfectness compares the full nonbinary model with its actual derived subgroup. -/
theorem modelCase_of_g2 {X : Type*} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At X (2^f)) : IsModelCase X := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  let := hF
  let := hfin
  have hlt : 2 < Nat.card F := by
    rw [hc]
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hf
    norm_num at he
    omega
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hlt
  let eD : Atlas.G2.Model F ≃* commutator (Atlas.G2.Model F) :=
    Subgroup.topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)
  exact Or.inl ⟨F, hF, hfin, f, by omega, hc, ⟨e.trans eD⟩⟩

/-- The endpoint is the derived carrier, with no identification with full G₂(2). -/
theorem modelCase_of_derived {X : Type*} [Group X]
    (hm : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))) : IsModelCase X :=
  Or.inl ⟨ZMod 2, inferInstance, inferInstance, 1, by decide, by simp, hm⟩

/-- Every central two-cover is retained, including the trivial-center case. -/
theorem modelCase_of_cover {X : Type*} [Group X] [Finite X] [IsQuasisimple X]
    (hz : IsPGroup 2 (center X))
    (hm : ClassificationModels.IsG2At (X ⧸ center X) 4) : IsModelCase X := by
  have hZ : center X = pCore 2 X :=
    le_antisymm (le_sSup ⟨inferInstance, hz⟩) (IsQuasisimple.pCore_le_center 2)
  by_cases hc : pCore 2 X = ⊥
  · have e : X ≃* (X ⧸ center X) :=
      QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (hZ.trans hc).symm)
    obtain ⟨F, hF, hfin, hcard, ⟨em⟩⟩ := hm
    exact modelCase_of_g2 (f := 2) (by decide)
      ⟨F, hF, hfin, hcard, ⟨e.trans em⟩⟩
  · obtain ⟨F, hF, hfin, hcard, ⟨em⟩⟩ := hm
    exact Or.inr ⟨hZ, hc, F, hF, hfin, hcard,
      ⟨(QuotientGroup.quotientMulEquivOfEq hZ.symm).trans em⟩⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
