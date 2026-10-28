module
public import Theory.Mathieu.M24.ChapterHStabilizers.SextetAction
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores
public import Theory.Representation.HexacodeAction.PairGeometry

/-!
# The native common four as an F4 line with fifteen conjugates

Under the native translation coordinates, the intersection of the octad
and sextet two-cores is exactly the hexacode plane vanishing on the two
columns forming the marked octad. This binary plane is a line over the
actual four-element scalar field. Its sextet-stabilizer conjugates are
in bijection with the fifteen unordered pairs of the six columns.

All conjugates below are literal subgroups of native M24, and conjugators
belong to the actual standard sextet stabilizer. The coordinate proof
therefore identifies the source subgroup, not just an abstract plane.

Source: Aschbacher–Smith H.14.1(6), printed p.397. The hexacode coordinate
model and its licensed ATLAS provenance are described in `SextetAction`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.CommonPlane
open M24LocalGeometry M24LocalGeometry.SextetCore Atlas.Codes MathieuCode
open Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm)
open SextetAction
noncomputable section

def basePair : Pair := ⟨{0,4}, by decide⟩

theorem octad_coordinates : ∀ (i : HexIndex) (k : Fin 4),
    atlasPointEquiv (i,k) ∈ standardOctad.val ↔ hexIndexEquiv i ∈ basePair.val := by
  decide +kernel

theorem translation_coordinates (v : hexacode) (i : HexIndex) (k : Fin 4) :
    (ambientTranslationEquiv (Multiplicative.ofAdd v)).val.val (atlasPointEquiv (i,k)) =
      atlasPointEquiv (i, rowLabel.symm (rowLabel k + v.val i)) := by
  have h := sextetTranslation_coordinates (Multiplicative.ofAdd v) i k
  have he : sextetEquiv (translationEquiv (Multiplicative.ofAdd v)).val =
      sextetTranslation (Multiplicative.ofAdd v) := sextetEquiv.apply_symm_apply _
  rw [← he, sextetEquiv_apply] at h
  apply atlasPointEquiv.symm.injective
  rw [atlasPointEquiv.symm_apply_apply]
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, toAdd_ofAdd] at h
  exact h

def common : Subgroup M24 :=
  ((pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype) ⊓ core

theorem common_card : Nat.card common = 4 := M23Geometry.CommonFour.ambient_common_card

/-- Elementary structure is inherited from the intrinsic sextet core. -/
theorem common_elementary : IsElementaryAbelian 2 common := by
  let f : common →* core := Subgroup.inclusion inf_le_right
  have hf : Function.Injective f := Subgroup.inclusion_injective inf_le_right
  exact {
    is_comm := ⟨fun x y => hf (by
      simpa only [map_mul] using
        core_ambient_elementary.toIsMulCommutative.is_comm.comm (f x) (f y))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hf (by
      simpa only [map_pow, map_one] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          core_ambient_elementary.exponent_dvd_p (f x)))) }

theorem translation_mem_common (v : hexacode) :
    (ambientTranslationEquiv (Multiplicative.ofAdd v)).val ∈ common ↔
      v ∈ zeroPairPlane basePair := by
  change _ ∈ ((pCore 2 (octadStabilizer standardOctad)).map
    (octadStabilizer standardOctad).subtype) ∧ _ ∈ core ↔ _
  rw [octad_core_map_eq_pointwise]
  simp only [(ambientTranslationEquiv (Multiplicative.ofAdd v)).property, and_true]
  rw [mem_octadPointwiseKernel]
  constructor
  · intro h i hi
    have ho := (octad_coordinates (hexPos i) 0).mpr (by simpa using hi)
    have he := h (atlasPointEquiv (hexPos i,0)) ho
    change (ambientTranslationEquiv (Multiplicative.ofAdd v)).val.val _ = _ at he
    rw [translation_coordinates] at he
    have hr := congrArg (fun p : Omega => rowLabel p.2) (atlasPointEquiv.injective he)
    simpa using hr
  · intro h x hx
    obtain ⟨⟨i,k⟩, rfl⟩ := atlasPointEquiv.surjective x
    have hi := (octad_coordinates i k).mp hx
    have hz := h (hexIndexEquiv i) hi
    have hz' : v.val i = 0 := by simpa using hz
    change (ambientTranslationEquiv (Multiplicative.ofAdd v)).val.val _ = _
    rw [translation_coordinates, hz', add_zero, rowLabel.symm_apply_apply]

def planeGroup (s : Pair) : Subgroup M24 :=
  (zeroPairPlane s).toAddSubgroup.toSubgroup.map
    (core.subtype.comp ambientTranslationEquiv.toMonoidHom)

theorem translation_mem_planeGroup (s : Pair) (v : hexacode) :
    (ambientTranslationEquiv (Multiplicative.ofAdd v)).val ∈ planeGroup s ↔
      v ∈ zeroPairPlane s := by
  apply Subgroup.mem_map_iff_mem
  exact core.subtype_injective.comp ambientTranslationEquiv.injective

theorem planeGroup_injective : Function.Injective planeGroup := by
  intro s t h
  apply zeroPairPlane_injective
  ext v
  rw [← translation_mem_planeGroup, ← translation_mem_planeGroup, h]

theorem common_eq_planeGroup : common = planeGroup basePair := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := ambientTranslationEquiv.surjective ⟨x,hx.2⟩
    have he : (ambientTranslationEquiv v).val = x := congrArg Subtype.val hv
    rw [← he] at hx ⊢
    exact (translation_mem_planeGroup _ v.toAdd).mpr ((translation_mem_common v.toAdd).mp hx)
  · rintro ⟨v,hv,rfl⟩
    exact (translation_mem_common v.toAdd).mpr hv

theorem planeGroup_map (g : Stabilizer) (s : Pair) :
    (planeGroup s).map (MulAut.conj g.val).toMonoidHom =
      planeGroup (pairPerm (columnHom g) s) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v,hv,rfl⟩, rfl⟩
    change g.val * (ambientTranslationEquiv v).val * g.val⁻¹ ∈ _
    have he := ambientTranslationEquiv_conjugation g v.toAdd
    simp only [ofAdd_toAdd] at he
    rw [he]
    apply (translation_mem_planeGroup _ _).mpr
    have h : action (quotientHom g) v.toAdd ∈
        (zeroPairPlane s).map (action (quotientHom g)) := ⟨v.toAdd, hv, rfl⟩
    rw [zeroPairPlane_map] at h
    exact h
  · rintro _ ⟨v,hv,rfl⟩
    change v.toAdd ∈ zeroPairPlane (pairPerm (hexCoordinateSixHom (quotientHom g)) s) at hv
    rw [← zeroPairPlane_map] at hv
    obtain ⟨w,hw,he⟩ := hv
    refine ⟨(ambientTranslationEquiv (Multiplicative.ofAdd w)).val,
      (translation_mem_planeGroup s w).mpr hw, ?_⟩
    change g.val * (ambientTranslationEquiv (Multiplicative.ofAdd w)).val * g.val⁻¹ = _
    rw [ambientTranslationEquiv_conjugation, he]
    rfl

private theorem pair_transport (s : Pair) :
    ∃ σ : Equiv.Perm (Fin 6), pairPerm σ basePair = s := by
  have h : ∀ s : Pair, ∃ i j : Fin 6,
      pairPerm (Equiv.swap 0 i * Equiv.swap 4 j) basePair = s := by decide +kernel
  obtain ⟨i,j,hij⟩ := h s
  exact ⟨_,hij⟩

/-- These are literal M24 subgroups, conjugated only by the sextet stabilizer. -/
def Conjugates := {A : Subgroup M24 //
  ∃ g : Stabilizer, common.map (MulAut.conj g.val).toMonoidHom = A}

def conjugateOfPair (s : Pair) : Conjugates := ⟨planeGroup s, by
  obtain ⟨σ,hσ⟩ := pair_transport s
  obtain ⟨g,hg⟩ := columnHom_surjective σ
  refine ⟨g, ?_⟩
  rw [common_eq_planeGroup, planeGroup_map, hg, hσ]⟩

theorem conjugateOfPair_bijective : Function.Bijective conjugateOfPair := by
  constructor
  · intro s t h
    exact planeGroup_injective (congrArg Subtype.val h)
  · rintro ⟨A,g,hg⟩
    refine ⟨pairPerm (columnHom g) basePair, Subtype.ext ?_⟩
    change planeGroup (pairPerm (columnHom g) basePair) = A
    rw [← planeGroup_map, ← common_eq_planeGroup]
    exact hg

/-- The marked common four has exactly fifteen conjugates under the sextet stabilizer. -/
theorem conjugates_card : Nat.card Conjugates = 15 := by
  rw [← Nat.card_congr (Equiv.ofBijective conjugateOfPair conjugateOfPair_bijective)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem zeroPairPlane_scalar_stable (s : Pair) :
    hexZ ∈ Representation.BinaryOffender.subspaceStabilizer action (zeroPairPlane s) := by
  intro w
  change (∀ i ∈ s.val, (action hexZ w).val (hexPos i) = 0) ↔ _
  simp only [action_coordinate_zero, hexZ_six]
  rfl

/-- The source common four, in the faithful core coordinates, is an actual F4 line. -/
def commonFieldLine : Submodule F hexacode :=
  scalarSubmodule (zeroPairPlane basePair) (zeroPairPlane_scalar_stable basePair)

theorem commonFieldLine_finrank : Module.finrank F commonFieldLine = 1 := by
  have h := scalarSubmodule_finrank (zeroPairPlane basePair)
    (zeroPairPlane_scalar_stable basePair)
  rw [zeroPairPlane_finrank] at h
  change 2 * Module.finrank F commonFieldLine = 2 at h
  omega

theorem translation_mem_commonFieldLine (v : hexacode) :
    (ambientTranslationEquiv (Multiplicative.ofAdd v)).val ∈ common ↔
      v ∈ commonFieldLine := translation_mem_common v

end
end Sporadic.Mathieu.M24ChapterHStabilizers.CommonPlane
