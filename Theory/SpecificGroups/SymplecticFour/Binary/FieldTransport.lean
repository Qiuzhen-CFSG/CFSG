module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Field transport of the symplectic four-space flag

Applying a field isomorphism to matrix entries gives an isomorphism of the
actual symplectic groups. The coordinate equations defining the point and
plane parabolics are preserved, so this restricts to their stabilizers and
their whole overlap. In particular, the binary local-model problem reduces
to the two concrete stabilizers over `ZMod 2`.

The construction `fieldEquivSp` is adapted from
`Atlas/LinearGroups/Symplectic/FieldTransport.lean` in ATLAS, by Gerald Höhn
and the ATLAS contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
under the ATLAS Research and Attribution License
1.0 (`LICENSES/ATLAS.txt`, citation in `LICENSES/ATLAS-CITATION.cff`). Changes:
specialized to the four-dimensional CFSG carrier, added the flag restrictions
and binary-field specialization, and adapted to the project module system.

Source: the matrix flag underlying Aschbacher--Smith F.1.12(I)(2),
printed pp.262--264. These transport results do not by themselves identify
either binary parabolic with a symmetric-group product.
-/

@[expose] public section
noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.Binary

variable {F K : Type*} [Field F] [Field K]

/-- Entrywise field transport of the actual matrix group. -/
def fieldEquivSp (e : F ≃+* K) : Sp F ≃* Sp K where
  toFun g := ⟨g.val.map e, SymplecticGroup.map_mem g.property e⟩
  invFun g := ⟨g.val.map e.symm, SymplecticGroup.map_mem g.property e.symm⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

@[simp] theorem fieldEquivSp_apply (e : F ≃+* K) (g : Sp F)
    (i j : Fin 2 ⊕ Fin 2) : (fieldEquivSp e g).val i j = e (g.val i j) := rfl

@[simp] theorem fieldEquivSp_mem_pointParabolic (e : F ≃+* K) (g : Sp F) :
    fieldEquivSp e g ∈ pointParabolic ↔ g ∈ pointParabolic := by
  simp only [mem_pointParabolic_iff, fieldEquivSp_apply, EmbeddingLike.map_eq_zero_iff]

@[simp] theorem fieldEquivSp_mem_planeParabolic (e : F ≃+* K) (g : Sp F) :
    fieldEquivSp e g ∈ planeParabolic ↔ g ∈ planeParabolic := by
  simp only [mem_planeParabolic_iff, fieldEquivSp_apply, EmbeddingLike.map_eq_zero_iff]

@[simp] theorem fieldEquivSp_mem_borel (e : F ≃+* K) (g : Sp F) :
    fieldEquivSp e g ∈ borel ↔ g ∈ borel := by
  simp only [borel, Subgroup.mem_inf, fieldEquivSp_mem_pointParabolic,
    fieldEquivSp_mem_planeParabolic]

theorem map_pointParabolic (e : F ≃+* K) :
    (pointParabolic (F := F)).map (fieldEquivSp e).toMonoidHom =
      pointParabolic (F := K) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (fieldEquivSp_mem_pointParabolic e x).mpr hx
  · intro hg
    obtain ⟨x, rfl⟩ := (fieldEquivSp e).surjective g
    exact ⟨x, (fieldEquivSp_mem_pointParabolic e x).mp hg, rfl⟩

theorem map_planeParabolic (e : F ≃+* K) :
    (planeParabolic (F := F)).map (fieldEquivSp e).toMonoidHom =
      planeParabolic (F := K) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (fieldEquivSp_mem_planeParabolic e x).mpr hx
  · intro hg
    obtain ⟨x, rfl⟩ := (fieldEquivSp e).surjective g
    exact ⟨x, (fieldEquivSp_mem_planeParabolic e x).mp hg, rfl⟩

theorem map_borel (e : F ≃+* K) :
    (borel (F := F)).map (fieldEquivSp e).toMonoidHom = borel (F := K) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (fieldEquivSp_mem_borel e x).mpr hx
  · intro hg
    obtain ⟨x, rfl⟩ := (fieldEquivSp e).surjective g
    exact ⟨x, (fieldEquivSp_mem_borel e x).mp hg, rfl⟩

/-- Field transport restricted to the actual point stabilizer. -/
def pointParabolicFieldEquiv (e : F ≃+* K) :
    pointParabolic (F := F) ≃* pointParabolic (F := K) :=
  ((fieldEquivSp e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_pointParabolic e))

/-- Field transport restricted to the actual plane stabilizer. -/
def planeParabolicFieldEquiv (e : F ≃+* K) :
    planeParabolic (F := F) ≃* planeParabolic (F := K) :=
  ((fieldEquivSp e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_planeParabolic e))

/-- Both parabolic transports restrict to this map on their whole overlap. -/
def borelFieldEquiv (e : F ≃+* K) : borel (F := F) ≃* borel (F := K) :=
  ((fieldEquivSp e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_borel e))

@[simp] theorem pointParabolicFieldEquiv_coe (e : F ≃+* K)
    (g : pointParabolic (F := F)) :
    (pointParabolicFieldEquiv e g).val = fieldEquivSp e g.val := rfl

@[simp] theorem planeParabolicFieldEquiv_coe (e : F ≃+* K)
    (g : planeParabolic (F := F)) :
    (planeParabolicFieldEquiv e g).val = fieldEquivSp e g.val := rfl

@[simp] theorem borelFieldEquiv_coe (e : F ≃+* K) (g : borel (F := F)) :
    (borelFieldEquiv e g).val = fieldEquivSp e g.val := rfl

/-- The coefficient-field identification used for the binary specialization. -/
def fieldEquivZModTwo (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2) :
    F ≃+* ZMod 2 := by
  letI : Fintype F := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [← Nat.card_eq_fintype_card] using hF)).symm

/-- Reduction of the point parabolic over any binary field to `ZMod 2`. -/
def pointParabolicEquivZModTwo [Finite F] (hF : Nat.card F = 2) :
    pointParabolic (F := F) ≃* pointParabolic (F := ZMod 2) :=
  pointParabolicFieldEquiv (fieldEquivZModTwo F hF)

/-- Reduction of the plane parabolic over any binary field to `ZMod 2`. -/
def planeParabolicEquivZModTwo [Finite F] (hF : Nat.card F = 2) :
    planeParabolic (F := F) ≃* planeParabolic (F := ZMod 2) :=
  planeParabolicFieldEquiv (fieldEquivZModTwo F hF)

end Theory.SpecificGroups.SymplecticFour.Binary
