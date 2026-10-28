module

public import Theory.SpecificGroups.Lyons.Atlas111OrderSetup

/-!
# Matrix-level identification of the concrete local subgroup

The subgroup used in the Lyons order calculation lives inside `LyonsGroup`,
itself a subgroup of matrix units. We identify it with the subgroup generated
by the same two ATLAS words directly in the matrix units. Thus a faithful
representation with this image gives an isomorphism with the original local
subgroup, without a separate proof that every represented element lies in
the ambient Lyons group. Generation reduces the image equality to two words.

The equivalence is only a change of carrier; it does not identify the local
subgroup with G₂(5). That requires a separate concrete representation or
isomorphism certificate.

Source for the words: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
Original program and attribution: `Atlas111OrderSource/`.
-/

namespace Lyons.OrderCertificate

/-- The ATLAS word program commutes with group homomorphisms. -/
public theorem max1Program_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) :
    Prod.map f f (max1Program a b) = max1Program (f a) (f b) := by
  simp only [max1Program, Prod.map, map_mul, map_pow, map_inv]

/-- The local subgroup viewed directly in the matrix units. -/
@[expose] public def localMatrixSubgroup : Subgroup AtlasMatrixˣ :=
  Subgroup.closure {(max1Program atlasA atlasB).1, (max1Program atlasA atlasB).2}

/-- Inclusion into matrix units, using the named group instance of `LyonsGroup`. -/
@[expose] public def ambientUnitsHom : LyonsGroup →* AtlasMatrixˣ where
  toFun x := x.val
  map_one' := rfl
  map_mul' _ _ := rfl

public theorem ambientUnitsHom_injective : Function.Injective ambientUnitsHom :=
  fun _ _ h => Subtype.ext h

public theorem map_localSubgroup :
    localSubgroup.map ambientUnitsHom = localMatrixSubgroup := by
  have ha : ambientUnitsHom generatorA = atlasA := rfl
  have hb : ambientUnitsHom generatorB = atlasB := rfl
  rw [localSubgroup, MonoidHom.map_closure, Set.image_pair]
  simp only [localMatrixSubgroup, localA, localB, max1Program_fst, max1Program_snd,
    map_mul, map_pow, map_inv, ha, hb]

/-- Removing the intermediate ambient-group subtype preserves the local group. -/
public noncomputable def localSubgroupMatrixEquiv : localSubgroup ≃* localMatrixSubgroup :=
  (localSubgroup.equivMapOfInjective ambientUnitsHom
    ambientUnitsHom_injective).trans (MulEquiv.subgroupCongr map_localSubgroup)

/-- A generating pair with the specified images certifies the whole image. -/
public theorem range_eq_localMatrixSubgroup {G : Type*} [Group G]
    (f : G →* AtlasMatrixˣ) (u v : G)
    (hgen : Subgroup.closure ({u, v} : Set G) = ⊤)
    (hu : f u = (max1Program atlasA atlasB).1)
    (hv : f v = (max1Program atlasA atlasB).2) :
    f.range = localMatrixSubgroup := by
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Set.image_pair, hu, hv]
  rfl

/-- A faithful representation with the specified image identifies the local group. -/
public noncomputable def localSubgroupEquivOfMatrixRange {G : Type*} [Group G]
    (f : G →* AtlasMatrixˣ) (hf : Function.Injective f)
    (hrange : f.range = localMatrixSubgroup) : localSubgroup ≃* G :=
  (localSubgroupMatrixEquiv.trans (MulEquiv.subgroupCongr hrange.symm)).trans
    (MonoidHom.ofInjective hf).symm

end Lyons.OrderCertificate
