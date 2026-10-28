module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics

/-!
# The full binary Ree group is the automorphism extension of the marked Tits group

The bijective derived conjugation action is transported through the certified
Atlas--derived equivalence. Its only comparison premise is discharged by the
actual Parrott root realization. The resulting equivalence with `MulAut` retains
the conjugation formula and sends the embedded Atlas group to its usual inner
automorphisms, of index two.

Transporting the full parabolics and their whole Borel gives an inclusion amalgam
inside the actual automorphism group. The three intersections with the inner
group are exactly the marked Atlas subgroups, through the same conjugation map.
Thus the automorphism identification also identifies the marked extension.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, and Parrott (1972),
§5, p.683. This proves the automorphism-extension assertion used by the binary
Ree alternative; it makes no uniqueness assertion for arbitrary amalgams.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee
open Theory.GroupTheory

/-- The concrete derived comparison discharges the last coverage premise. -/
theorem atlasAction_bijective : Function.Bijective atlasAction :=
  (MulAut.congr atlasDerivedEquiv.symm).bijective.comp
    (ReeF4.Parabolics.OuterLocal.binaryDerivedAction_bijective
      InvolutionRootGeometry.derivedEquiv.symm)

/-- All automorphisms, with the fixed embedding and conjugation convention. -/
def atlasAutEquiv : ReeF4.Model 0 ≃* MulAut Atlas1600Group :=
  MulEquiv.ofBijective atlasAction atlasAction_bijective

@[simp] theorem atlasAutEquiv_apply (g : ReeF4.Model 0) :
    atlasAutEquiv g = atlasAction g := rfl

@[simp] theorem atlasAutEquiv_embedding (x : Atlas1600Group) :
    atlasAutEquiv (atlasEmbedding x) = MulAut.conj x := atlasAction_embedding x

theorem atlasAutEquiv_comp_embedding :
    atlasAutEquiv.toMonoidHom.comp atlasEmbedding = MulAut.conj :=
  MonoidHom.ext atlasAutEquiv_embedding

theorem derived_map_inner :
    (commutator (ReeF4.Model 0)).map atlasAutEquiv.toMonoidHom =
      (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).range := by
  rw [← atlasEmbedding_range, ← MonoidHom.range_comp, atlasAutEquiv_comp_embedding]

theorem inner_index :
    (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).range.index = 2 := by
  rw [← derived_map_inner, Subgroup.index_map_of_bijective (f := atlasAutEquiv.toMonoidHom)
    atlasAutEquiv.bijective, derived_index]

namespace AutomorphismModel

def first : Subgroup (MulAut Atlas1600Group) := FullRee.first.map atlasAutEquiv.toMonoidHom
def second : Subgroup (MulAut Atlas1600Group) := FullRee.second.map atlasAutEquiv.toMonoidHom
def B : Subgroup (MulAut Atlas1600Group) := FullRee.B.map atlasAutEquiv.toMonoidHom
def S : Subgroup (MulAut Atlas1600Group) := FullRee.S.map atlasAutEquiv.toMonoidHom

theorem borel_eq_sylow : B = S := by rw [B, S, FullRee.borel_eq_sylow]

theorem borel_le_first : B ≤ first := Subgroup.map_mono FullRee.borel_le_first
theorem borel_le_second : B ≤ second := Subgroup.map_mono FullRee.borel_le_second

theorem overlap_eq_borel : first ⊓ second = B := by
  rw [first, second, ← Subgroup.map_inf _ _ atlasAutEquiv.toMonoidHom atlasAutEquiv.injective,
    FullRee.overlap_eq_borel, B]

theorem generate : first ⊔ second = ⊤ := by
  rw [first, second, ← Subgroup.map_sup, FullRee.generate,
    Subgroup.map_top_of_surjective atlasAutEquiv.toMonoidHom atlasAutEquiv.surjective]

def sylow : Sylow 2 (MulAut Atlas1600Group) :=
  FullRee.sylow.mapSurjective (f := atlasAutEquiv.toMonoidHom) atlasAutEquiv.surjective

theorem sylow_coe : (sylow : Subgroup (MulAut Atlas1600Group)) = S := by
  change (FullRee.sylow : Subgroup (ReeF4.Model 0)).map atlasAutEquiv.toMonoidHom = S
  rw [FullRee.sylow_coe]
  rfl

def amalgam : RankTwoAmalgam first B second :=
  RankTwoAmalgam.ofSubgroups first B second borel_le_first borel_le_second

/-- Both overlap squares commute through the same ambient equivalence. -/
def amalgamIso : RankTwoAmalgam.Iso FullRee.amalgam amalgam :=
  RankTwoAmalgam.ofSubgroupsIso atlasAutEquiv FullRee.borel_le_first
    FullRee.borel_le_second borel_le_first borel_le_second rfl rfl rfl

@[simp] theorem amalgamIso_left_coe (x : FullRee.first) :
    (amalgamIso.left x : MulAut Atlas1600Group) = atlasAction x := rfl

@[simp] theorem amalgamIso_middle_coe (x : FullRee.B) :
    (amalgamIso.middle x : MulAut Atlas1600Group) = atlasAction x := rfl

@[simp] theorem amalgamIso_right_coe (x : FullRee.second) :
    (amalgamIso.right x : MulAut Atlas1600Group) = atlasAction x := rfl

theorem inner_first :
    ExceptionalParabolics.first.map MulAut.conj =
      first ⊓ (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).range := by
  rw [← atlasAutEquiv_comp_embedding, ← Subgroup.map_map, atlas_first_map,
    Subgroup.map_inf _ _ atlasAutEquiv.toMonoidHom atlasAutEquiv.injective, derived_map_inner,
    atlasAutEquiv_comp_embedding]
  rfl

theorem inner_second :
    ExceptionalParabolics.second.map MulAut.conj =
      second ⊓ (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).range := by
  rw [← atlasAutEquiv_comp_embedding, ← Subgroup.map_map, atlas_second_map,
    Subgroup.map_inf _ _ atlasAutEquiv.toMonoidHom atlasAutEquiv.injective, derived_map_inner,
    atlasAutEquiv_comp_embedding]
  rfl

theorem inner_sylow :
    ExceptionalParabolics.S.map MulAut.conj =
      S ⊓ (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).range := by
  rw [← atlasAutEquiv_comp_embedding, ← Subgroup.map_map, atlas_sylow_map,
    Subgroup.map_inf _ _ atlasAutEquiv.toMonoidHom atlasAutEquiv.injective, derived_map_inner,
    atlasAutEquiv_comp_embedding]
  rfl

end AutomorphismModel
end Tits.ExceptionalParabolics.FullRee

