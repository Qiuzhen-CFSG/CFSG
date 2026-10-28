module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Characters on the literal local Z-group

The common decomposition of Z_alpha as the product of its natural subgroup
and its fixed summand gives a unique natural projection. Pairing its natural
coordinates with the marked dual quotient coordinates constructs homomorphisms
on both higher layers. The projection is equivariant and the dot product pairs
the natural action with inverse transpose, always with common.natural.marking.
Injectivity of the character embedding gives the exact relative kernels.

These maps do not yet identify neighboring subgroup images. That geometric
obligation is isolated in Pairings.Reduction, whose construction consumes the
maps here. No choice of a different path or different SL3 marking is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.1), (4.5.3)--(4.5.5),
printed pp.881--882 and 897--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
variable {G : Type*} [Group G] {A B C : Subgroup G}

private def productMap (hA : A ≤ C) (hB : B ≤ C) [IsMulCommutative C] : A × B →* C where
  toFun x := ⟨x.1 * x.2, C.mul_mem (hA x.1.property) (hB x.2.property)⟩
  map_one' := by apply Subtype.ext; exact one_mul _
  map_mul' x y := by
    apply Subtype.ext
    change ((x.1 : G) * y.1) * ((x.2 : G) * y.2) =
      ((x.1 : G) * x.2) * ((y.1 : G) * y.2)
    have hcomm := setLike_mul_comm (hA y.1.property) (hB x.2.property)
    simpa only [mul_assoc] using congrArg (fun z => (x.1 : G) * z * y.2) hcomm

private theorem productMap_injective (hA : A ≤ C) (hB : B ≤ C) [IsMulCommutative C]
    (hd : Disjoint A B) : Function.Injective (productMap hA hB) := by
  intro x y h
  have he : (x.1 : G) * x.2 = (y.1 : G) * y.2 := congrArg Subtype.val h
  have hh : (y.1 : G)⁻¹ * x.1 = (y.2 : G) * (x.2 : G)⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    rw [mul_assoc, he, inv_mul_cancel_left]
  have hone : (y.1 : G)⁻¹ * x.1 = 1 := hd.le_bot
    ⟨A.mul_mem (A.inv_mem y.1.property) x.1.property,
      hh ▸ B.mul_mem y.2.property (B.inv_mem x.2.property)⟩
  have hu : x.1 = y.1 := Subtype.ext (inv_mul_eq_one.mp hone).symm
  apply Prod.ext hu
  apply Subtype.ext
  rw [hu] at he
  exact mul_left_cancel he

private theorem productMap_surjective (hA : A ≤ C) (hB : B ≤ C) [IsMulCommutative C]
    (hs : C = A ⊔ B) : Function.Surjective (productMap hA hB) := by
  let f := C.subtype.comp (productMap hA hB)
  have hAr : A ≤ f.range := by
    intro x hx
    exact ⟨(⟨x,hx⟩,1), mul_one x⟩
  have hBr : B ≤ f.range := by
    intro x hx
    exact ⟨(1,⟨x,hx⟩), one_mul x⟩
  intro z
  have hz : (z : G) ∈ f.range := (hs ▸ sup_le hAr hBr) z.property
  obtain ⟨x,hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩



open DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} (common : CommonFacts R source geometry)

/-- The literal fixed summand in the common splitting of Z_alpha. -/
@[expose] noncomputable def fixedSummand : Subgroup (FreeAmalgam R) :=
  Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))

private noncomputable def splitting :
    U R (alpha R) × fixedSummand (R := R) ≃* Z R (alpha R) := by
  letI := geometry.Z_elementary (lt_trans (by decide) common.large_distance) (alpha R) rfl
  exact MulEquiv.ofBijective (productMap (U_le_Z R _) inf_le_left)
    ⟨productMap_injective _ _ common.disjoint,
      productMap_surjective _ _ common.decomposition⟩

include common in
/-- The common splitting is an actual product decomposition inside Z_alpha. -/
theorem exists_natural_fixed_decomposition (z : Z R (alpha R)) :
    ∃ (u : U R (alpha R)) (f : fixedSummand (R := R)),
      (u : FreeAmalgam R) * f = z := by
  refine ⟨((splitting common).symm z).1, ((splitting common).symm z).2, ?_⟩
  exact congrArg Subtype.val ((splitting common).apply_symm_apply z)

/-- Project onto U_alpha along the supplied fixed summand, then use the given natural coordinates. -/
noncomputable def naturalCoordinates : Z R (alpha R) →* Multiplicative W :=
  common.natural.equiv.toMonoidHom.comp
    ((MonoidHom.fst _ _).comp (splitting common).symm.toMonoidHom)

/-- The coordinate map evaluates the natural factor of an actual product decomposition. -/
theorem naturalCoordinates_of_decomposition (z : Z R (alpha R))
    (u : U R (alpha R)) (f : fixedSummand (R := R))
    (hz : (u : FreeAmalgam R) * f = z) :
    naturalCoordinates common z = common.natural.equiv u := by
  have he : splitting common (u,f) = z := Subtype.ext hz
  rw [← he]
  change common.natural.equiv ((splitting common).symm (splitting common (u,f))).1 = _
  rw [MulEquiv.symm_apply_apply]

/-- On the natural subgroup the extension agrees with the original marking. -/
theorem naturalCoordinates_on_U (u : U R (alpha R)) :
    naturalCoordinates common ⟨u, U_le_Z R _ u.property⟩ = common.natural.equiv u :=
  naturalCoordinates_of_decomposition common _ u 1 (mul_one _)

/-- The extended coordinates vanish on the literal fixed summand. -/
theorem naturalCoordinates_on_fixed (f : fixedSummand (R := R)) :
    naturalCoordinates common ⟨f, f.property.1⟩ = 1 := by
  rw [naturalCoordinates_of_decomposition common _ 1 f (one_mul _), map_one]

/-- Every natural coordinate is attained already on U_alpha. -/
theorem naturalCoordinates_surjective : Function.Surjective (naturalCoordinates common) := by
  intro v
  let u := common.natural.equiv.symm v
  refine ⟨⟨u, U_le_Z R _ u.property⟩, ?_⟩
  rw [naturalCoordinates_on_U]
  exact common.natural.equiv.apply_symm_apply v

include common in
/-- Normality of the fixed summand is relative to the actual local stabilizer. -/
theorem fixedSummand_normalized :
    stabilizer R (alpha R) ≤ normalizer (fixedSummand (R := R)) := by
  have hZQ : Z R (alpha R) ≤ Q R (alpha R) :=
    Z_le_Q_of_dist_lt R (alpha R) (geometry.exists_critical _ rfl)
      (by simpa only [SimpleGraph.dist_self, Geometry.b] using
        lt_trans (by decide : 0 < 2) common.large_distance)
  have he : fixedSummand (R := R) = Z R (alpha R) ⊓ fixedCore R (alpha R) := by
    ext x
    exact ⟨fun h => ⟨h.1,hZQ h.1,h.2⟩, fun h => ⟨h.1,h.2.2⟩⟩
  rw [he]
  exact (le_inf (Z_normalized R _) (PathCentrality.fixedCore_normalized R _)).trans
    inf_normalizer_le_normalizer_inf

/-- The extension preserves the given natural action, with no new quotient marking. -/
theorem naturalCoordinates_action (m : M) (x y : Z R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    (naturalCoordinates common y).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec
        (naturalCoordinates common x).toAdd := by
  let u := ((splitting common).symm x).1
  let f := ((splitting common).symm x).2
  have hx : (u : FreeAmalgam R) * f = x :=
    congrArg Subtype.val ((splitting common).apply_symm_apply x)
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    change embedM R m ∈ stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let u' : U R (alpha R) := ⟨embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp (U_normalized _) _ hm _ u.property⟩
  let f' : fixedSummand (R := R) := ⟨embedM R m * (f : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp (fixedSummand_normalized common) _ hm _ f.property⟩
  have hy' : (u' : FreeAmalgam R) * f' = y := by
    change (embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹) *
      (embedM R m * (f : FreeAmalgam R) * (embedM R m)⁻¹) = _
    rw [hy, ← hx]
    group
  rw [naturalCoordinates_of_decomposition common y u' f' hy',
    naturalCoordinates_of_decomposition common x u f hx]
  exact common.natural.action m u u' rfl

private def scalarCharacter (v : Multiplicative W) : Multiplicative W →* Multiplicative (ZMod 2) where
  toFun w := Multiplicative.ofAdd (dotProduct v.toAdd w.toAdd)
  map_one' := by change Multiplicative.ofAdd (dotProduct _ 0) = 1; rw [dotProduct_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (dotProduct _ (x.toAdd + y.toAdd)) = _
    rw [dotProduct_add]
    rfl

/-- Pair a covector with the extended natural coordinates of the actual Z-group. -/
noncomputable def characterEmbedding : Multiplicative W →*
    (Z R (alpha R) →* Multiplicative (ZMod 2)) where
  toFun v := (scalarCharacter v).comp (naturalCoordinates common)
  map_one' := by ext z; change Multiplicative.ofAdd (dotProduct (0 : W) (naturalCoordinates common z).toAdd) = 1; rw [zero_dotProduct]; rfl
  map_mul' v w := by
    ext z
    change Multiplicative.ofAdd (dotProduct (v.toAdd + w.toAdd) _) = _
    rw [add_dotProduct]
    rfl

/-- The character evaluates by the ordinary binary dot product. -/
theorem characterEmbedding_apply (v : Multiplicative W) (z : Z R (alpha R)) :
    characterEmbedding common v z =
      Multiplicative.ofAdd (dotProduct v.toAdd (naturalCoordinates common z).toAdd) := by rfl

/-- Natural coordinate surjectivity makes the character embedding injective. -/
theorem characterEmbedding_injective : Function.Injective (characterEmbedding common) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  apply dotProduct_eq
  intro u
  obtain ⟨z,hz⟩ := naturalCoordinates_surjective common (Multiplicative.ofAdd u)
  have he := congrArg (fun f : Z R (alpha R) →* Multiplicative (ZMod 2) => (f z).toAdd) h
  change dotProduct v.toAdd (naturalCoordinates common z).toAdd =
    dotProduct w.toAdd (naturalCoordinates common z).toAdd at he
  rw [hz] at he
  exact he

private theorem dual_pairing (g : S) (v w : W) :
    dotProduct (dual g v) (g.val.mulVec w) = dotProduct v w := by
  rw [dotProduct_comm, dual, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

/-- Simultaneous natural and contragredient conjugation preserves evaluation. -/
theorem characterEmbedding_action (m : M) (v : Multiplicative W) (x y : Z R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    characterEmbedding common
      (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v.toAdd)) y =
        characterEmbedding common v x := by
  simp only [characterEmbedding_apply, naturalCoordinates_action common m x y hy]
  exact congrArg Multiplicative.ofAdd (dual_pairing _ _ _)



/-- The marked dual section gives a character-valued homomorphism on its literal upper group. -/
noncomputable def firstMap {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N) :
    A →* (Z R (alpha R) →* Multiplicative (ZMod 2)) :=
  (characterEmbedding common).comp s.quotient

/-- The first map has exactly the relative kernel supplied by the actual quotient. -/
theorem firstMap_kernel {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N) :
    (firstMap common s).ker = N.subgroupOf A := by
  rw [firstMap, MonoidHom.ker_comp_of_injective _ _ (characterEmbedding_injective common), s.kernel]

/-- The first pairing is invariant under simultaneous ambient conjugation. -/
theorem firstMap_action {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N)
    (m : M) (x y : A) (z t : Z R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹)
    (ht : (t : FreeAmalgam R) = embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹) :
    firstMap common s y t = firstMap common s x z := by
  change characterEmbedding common (s.quotient y) t = characterEmbedding common (s.quotient x) z
  have he : s.quotient y = Multiplicative.ofAdd
      (dual (common.natural.marking (source.projection m)) (s.quotient x).toAdd) :=
    Multiplicative.toAdd.injective (s.action m x y hy)
  rw [he]
  exact characterEmbedding_action common m _ z t ht

private def component (i : Bool) : Multiplicative (W × W) →* Multiplicative W where
  toFun v := Multiplicative.ofAdd (if i then v.toAdd.1 else v.toAdd.2)
  map_one' := by cases i <;> rfl
  map_mul' x y := by cases i <;> rfl

/-- The two marked dual factors give two character coordinates on the actual upper group. -/
noncomputable def secondMap {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common A N true) : A →*
    ((Z R (alpha R) →* Multiplicative (ZMod 2)) ×
      (Z R (alpha R) →* Multiplicative (ZMod 2))) :=
  ((characterEmbedding common).comp ((component true).comp s.quotient)).prod
    ((characterEmbedding common).comp ((component false).comp s.quotient))

/-- The pair of characters retains the exact relative quotient kernel. -/
theorem secondMap_kernel {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common A N true) :
    (secondMap common s).ker = N.subgroupOf A := by
  ext x
  rw [← s.kernel]
  change secondMap common s x = 1 ↔ s.quotient x = 1
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · have h1 := congrArg Prod.fst h
      have hz := (characterEmbedding_injective common)
        (h1.trans (characterEmbedding common).map_one.symm)
      exact congrArg Multiplicative.toAdd hz
    · have h2 := congrArg Prod.snd h
      have hz := (characterEmbedding_injective common)
        (h2.trans (characterEmbedding common).map_one.symm)
      exact congrArg Multiplicative.toAdd hz
  · intro h
    simp [secondMap, h]

/-- Both second-layer coordinates respect the same simultaneous conjugation. -/
theorem secondMap_action {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common A N true)
    (m : M) (x y : A) (z t : Z R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹)
    (ht : (t : FreeAmalgam R) = embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹) :
    ((secondMap common s y).1 t = (secondMap common s x).1 z) ∧
      ((secondMap common s y).2 t = (secondMap common s x).2 z) := by
  have he := s.action m x y hy
  simp only [↓reduceIte] at he
  constructor
  · change characterEmbedding common (component true (s.quotient y)) t =
      characterEmbedding common (component true (s.quotient x)) z
    change characterEmbedding common (Multiplicative.ofAdd (s.quotient y).toAdd.1) t = _
    rw [he]
    exact characterEmbedding_action common m _ z t ht
  · change characterEmbedding common (component false (s.quotient y)) t =
      characterEmbedding common (component false (s.quotient x)) z
    change characterEmbedding common (Multiplicative.ofAdd (s.quotient y).toAdd.2) t = _
    rw [he]
    exact characterEmbedding_action common m _ z t ht



/-- Every constructed character vanishes on the fixed summand. -/
theorem characterEmbedding_on_fixed (v : Multiplicative W) (z : Z R (alpha R))
    (hz : (z : FreeAmalgam R) ∈ fixedSummand (R := R)) :
    characterEmbedding common v z = 1 := by
  have he := naturalCoordinates_of_decomposition common z 1 ⟨z,hz⟩ (one_mul _)
  rw [map_one] at he
  rw [characterEmbedding_apply, he]
  change Multiplicative.ofAdd (dotProduct v.toAdd 0) = 1
  rw [dotProduct_zero]
  rfl


/-- The first-layer characters annihilate the fixed summand. -/
theorem firstMap_on_fixed {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N) (x : A) (z : Z R (alpha R))
    (hz : (z : FreeAmalgam R) ∈ fixedSummand (R := R)) : firstMap common s x z = 1 :=
  characterEmbedding_on_fixed common _ z hz

/-- Both second-layer character coordinates annihilate the fixed summand. -/
theorem secondMap_on_fixed {A N : Subgroup (FreeAmalgam R)}
    (s : MarkedPairSection source common A N true) (x : A) (z : Z R (alpha R))
    (hz : (z : FreeAmalgam R) ∈ fixedSummand (R := R)) :
    (secondMap common s x).1 z = 1 ∧ (secondMap common s x).2 z = 1 :=
  ⟨characterEmbedding_on_fixed common _ z hz, characterEmbedding_on_fixed common _ z hz⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
