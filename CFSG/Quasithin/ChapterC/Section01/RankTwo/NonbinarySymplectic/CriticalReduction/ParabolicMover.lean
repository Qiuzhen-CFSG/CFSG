module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ParabolicFixedSelection
public import Theory.SpecificGroups.SymplecticFour.QuadraticFixedPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverFixed

/-!
# The smaller mover in the chosen symplectic parabolic

In the chosen-parabolic branch, maximality identifies the entire small-mover
join J with the edge intersection with Q₁. A field-sized critical endpoint
lies in this intersection, and its quotient image is properly smaller than
J's image. These statements retain the original degree and the whole kernel.

The large quadratic subactor calculation gives the same natural fixed plane
for J and Q₁. Exact cover indices lift this to the full U-layer. MS93 (5.3)
then lifts the equality to the entire Z-layer: a fixed element is a product
of an element of U and an element of the residual-fixed core, whose Z-part
centralizes the whole vertex stabilizer. No central complement is chosen.

The actual maximizing-parabolic application keeps its existing selector and
proves the common-fixed-subgroup clause for the two conjugates of J. This
supplies smaller-mover fixed-layer and endpoint inputs to MS93 (5.6), printed
pp.917--918. Generation by that smaller join, the larger-image source choices,
selected paths and terminal distance exclusions remain unproved.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A field-sized critical endpoint lies in the full chosen plane-radical preimage. -/
theorem Input.replacement_endpoint_le_parabolic_core
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    : Z d.radical z ≤
      (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype := by
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rwa [geometry.distance_constant a path.start_color])
        z path.end_color path.critical }
  have hi := h.replacement_small_critical_indices_eq_field d rev hpos hsmall
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hzS := path.endpoint_Z_le_start_stabilizer hpos
  have haS := rev.endpoint_Z_le_start_stabilizer hpos
  have hC : C d.radical z = Q d.radical z := MSCentralOrbit.C_eq_Q _
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d) z path.end_color
  have hcz : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) =
      (Q d.radical z).relIndex (Z d.radical a) := by
    rw [←hC]
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical a)).index =
      ((stabilizer d.radical z ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
        (Z d.radical a)).index
    congr 1
    ext x
    exact ⟨fun hx => ⟨haS x.property,hx⟩,fun hx => hx.2⟩
  let := finite_Z d.radical a
  have hiU : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card B.Carrier := by
    apply (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans
    rw [hcz,hi.2,hcard]
  let A₀ := (Z d.radical z).subgroupOf S
  let A₁ := (A₀.map f).subgroupOf unipotent
  have hAU : A₀.map f ≤ unipotent := (map_mono (comap_mono hzT)).trans hTf
  have hAm : A₁.map unipotent.subtype = A₀.map f := map_subgroupOf_eq_of_le hAU
  have hiA : CentralRootGeometry.SmallMovers.movingIndex A₁ ≤ Nat.card B.Carrier := by
    have hi₀ := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) A₀
    rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
      map_subgroupOf_eq_of_le hzS,hindex] at hi₀
    rw [hi₀] at hiU
    rw [←CentralRootGeometry.SmallMovers.binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) A₁ ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hAm]
    exact hiU
  have hAw : A₁ ≤ CentralRootGeometry.wing true := by
    by_contra hn
    have hq : 1 < Nat.card B.Carrier := Finite.one_lt_card
    have hq2 : Nat.card B.Carrier < Nat.card B.Carrier^2 := by nlinarith
    have he := CentralRootGeometry.SmallMovers.Degree.movingIndex_eq_square_of_not_le_wing A₁
      (hiA.trans hq2.le) hn
    omega
  have hAz : A₀.map f ≤ P := by
    rw [←hAm]
    exact map_mono hAw
  have hzD : Z d.radical z ≤ D := by
    have hh : A₀ ≤ D₀ := (map_le_iff_le_comap).mp hAz
    have hh' := map_mono (f := S.subtype) hh
    rwa [map_subgroupOf_eq_of_le hzS] at hh'
  exact hzD

omit [Finite H] [Finite F] [CharP F 2] in
private theorem plane_preimage_index
    {a : Vertex d.radical}
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f)) :
    (centralizer ((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F^2 := by
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) (P.comap f)
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    hindex,map_comap_eq_self_of_surjective hf] at hh
  have hp : P=SymplecticConjugatePair.planeRadical :=
    SymplecticConjugatePair.planeRadical_eq_wing.symm
  rw [hp] at hh
  change _ = 2 ^ fixedCodim (SymplecticConjugatePair.binaryNatural (F := B.Carrier))
    SymplecticConjugatePair.planeRadical at hh
  rw [SymplecticConjugatePair.planeRadical_natural_fixedCodim B.card_eq] at hh
  rw [←hp] at hh
  rw [hh,h.field_card,hB,show 2*n=n*2 by omega,pow_mul]

/-- In the chosen-parabolic branch the small-mover join is the entire
intersection of the replacement edge with the literal parabolic two-core. -/
theorem Input.replacement_small_mover_parabolic_intersection
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    Q d.radical t ⊓
      (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) := by
  let S := stabilizer d.radical a
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hJD : J ≤ D := by
    have hh := map_mono (f := S.subtype) hJplane
    rwa [map_subgroupOf_eq_of_le (hJT.trans hTS)] at hh
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  apply h.replacement_small_mover_absorbs d geometry hb ha hat _ inf_le_left (le_inf hJT hJD)
  have hi := relIndex_le_of_le_left
    (centralizer_le (show Q d.radical t ⊓ D ≤ D from inf_le_right))
    (index_ne_zero_of_finite (H := (centralizer (D : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)))
  exact hi.trans_eq (plane_preimage_index h d B hB f hf hindex)

/-- The field-sized critical endpoint lies in the actual small-mover join
in the chosen-parabolic branch, even when that join has order below q cubed. -/
theorem Input.replacement_root_endpoint_le_small_mover
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    Z d.radical z ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  rw [←h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
    B hB f hf hindex hJplane]
  refine le_inf ?_ (h.replacement_endpoint_le_parabolic_core d path hb hfirst hsmall
    B hB f hTf hindex)
  rw [←hfirst]
  apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
  rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
  change path.walk.length - 1 < geometry.b d.radical
  rw [path.length_eq_b]
  omega

/-- The smaller join and the entire chosen parabolic core have the same
fixed subgroup on the full original U-layer. The proof uses exact indices
through the cover and retains its central kernel. -/
theorem Input.replacement_small_mover_parabolic_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
      U d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let σ := SymplecticConjugatePair.binaryNatural (F := B.Carrier)
  have hJD : J ≤ D := by
    dsimp only [J]
    rw [←h.replacement_small_mover_parabolic_intersection d geometry hb ha hat B hB f hf hindex hJplane]
    exact inf_le_right
  have hJS : J ≤ S := hJD.trans ((map_le_range _ _).trans_eq (range_subtype _))
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hc : Nat.card B.Carrier^2 ≤ Nat.card (J₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh,hcard]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hq : Nat.card B.Carrier < Nat.card B.Carrier^2 := by
    have hh : 1 < Nat.card B.Carrier := Finite.one_lt_card
    nlinarith
  have hfixed := large_quadratic_subactor_fixed_eq (J₀.map f) P
    ((map_le_iff_le_comap).mpr hJplane)
    CentralRootGeometry.SmallMovers.Degree.plane_radical_quadratic (hq.trans_le hc)
  have hfixed₂ : fixedSpace σ (J₀.map f) = fixedSpace σ P := by
    have bridge (A : Subgroup (Sp B.Carrier)) :
        fixedSpace σ A = (TwoLocalCover.fixedSpace A).restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
    rw [bridge,bridge,hfixed]
  have hdim : fixedCodim σ (J₀.map f) = fixedCodim σ P := by
    unfold fixedCodim
    rw [hfixed₂]
  have hJU := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) J₀
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    map_subgroupOf_eq_of_le hJS,hindex] at hJU
  have hDU := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) D₀
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    hindex,map_comap_eq_self_of_surjective hf] at hDU
  have hi : (centralizer (D : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [hJU,hDU,hdim]
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let CD := (centralizer (D : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  let CJ := (centralizer (J : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  have he : CD = CJ := by
    apply eq_of_le_of_card_ge (comap_mono (centralizer_le hJD))
    have hCD := CD.card_mul_index
    have hCJ := CJ.card_mul_index
    change CD.index = CJ.index at hi
    rw [hi] at hCD
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CJ)).bot_lt
      (hCJ.trans hCD.symm)).le
  apply le_antisymm
  · intro u hu
    refine ⟨hu.1,?_⟩
    exact (show (⟨u,hu.1⟩ : U d.radical a) ∈ CD from he.symm ▸ hu.2)
  · exact inf_le_inf_left _ (centralizer_le hJD)

/-- The smaller join and the entire chosen parabolic core fix exactly the
same subgroup of the full Z-layer. MS93 (5.3) reduces a fixed element to U
and the whole residual-fixed core; no central complement is chosen. -/
theorem Input.replacement_small_mover_parabolic_full_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let S := stabilizer d.radical a
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have heU := h.replacement_small_mover_parabolic_fixed d geometry hb ha hat B hB f hf hfQ hindex hJplane
  have hsat : Q d.radical t ⊓ D = J :=
    h.replacement_small_mover_parabolic_intersection d geometry hb ha hat B hB f hf hindex hJplane
  have hJD : J ≤ D := hsat ▸ inf_le_right
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJS : J ≤ S := hJD.trans hDS
  have hZX : Z d.radical a ≤ X d.radical a := Z_le_X_of_positive d.radical a ha
    (geometry.exists_critical a ha) (by rw [geometry.distance_constant a ha]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hS : Ltilde d.radical a ⊔ Q d.radical a = S := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hN : fixedCore d.radical a ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (show fixedCore d.radical a ≤ S from fun _ hx => hx.1.1).trans (U_normalized a)
  apply le_antisymm
  · intro z hz
    have hzUD := h.replacement_small_mover_X_centralizer d geometry hb ha hat ⟨hZX hz.1,hz.2⟩
    have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) *
        (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hN]
      exact hzUD
    obtain ⟨u,hu,c,hc,he⟩ := hzprod
    have hcZ : c ∈ Z d.radical a := by
      have hh := (Z d.radical a).mul_mem ((Z d.radical a).inv_mem (U_le_Z a hu)) hz.1
      simpa only [←he,inv_mul_cancel_left] using hh
    have hcS : c ∈ centralizer (S : Set (FreeAmalgam d.radical)) := by
      have hSL : Ltilde d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hc.2 y hy)
      have hSQ : Q d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr
          ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)) hcZ y hy)
      intro y hy
      exact mem_centralizer_singleton_iff.mp ((sup_le hSL hSQ) (hS.symm ▸ hy))
    have huJ : u ∈ centralizer (J : Set (FreeAmalgam d.radical)) := by
      have hh := (centralizer (J : Set (FreeAmalgam d.radical))).mul_mem hz.2
        ((centralizer (J : Set (FreeAmalgam d.radical))).inv_mem (centralizer_le hJS hcS))
      simpa only [←he,mul_inv_cancel_right] using hh
    have huD : u ∈ centralizer (D : Set (FreeAmalgam d.radical)) :=
      (show u ∈ U d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) from
        heU ▸ ⟨hu,huJ⟩).2
    refine ⟨hz.1,?_⟩
    rw [←he]
    exact (centralizer (D : Set (FreeAmalgam d.radical))).mul_mem huD (centralizer_le hDS hcS)
  · exact inf_le_inf_left _ (centralizer_le hJD)

omit h d [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem conjugate_fixed_eq {G : Type*} [Group G]
    (Z J D : Subgroup G) (he : Z ⊓ centralizer (J : Set G) = Z ⊓ centralizer (D : Set G))
    (g : G) (hg : g ∈ normalizer (Z : Set G)) :
    Z ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G) =
      Z ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hz := mem_normalizer_iff_map_conj_eq.mp hg
  change Z.map (MulAut.conj g).toMonoidHom = Z at hz
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,
    hz] at hh
  exact hh

/-- The same original maximizing parabolic and root selector retain the
exact smaller-mover intersection, endpoint placement, and full U fixed
subgroup. The same selector gives the full Z fixed-layer clause for J. The remaining source branch is the literal containment J ≤ Q₁;
no cubic-order premise or scalar closure of the smaller mover is assumed. -/
theorem Input.replacement_maximizing_parabolic_root_mover
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
         let Q₁ := P.comap f
         let D := Q₁.map (stabilizer d.radical a).subtype
         let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
           (Q d.radical t) (Nat.card F^2)
         (planeParabolic.comap f).pCoreIn 2 = Q₁ ∧
         (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ planeParabolic.comap f ∧
         ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),Q₁⁆,Q₁⁆ = ⊥ ∧
         (∀ x : Sp B.Carrier,
           Nat.card (J.subgroupOf (stabilizer d.radical a) ⊓
             (P.map (MulAut.conj x).toMonoidHom).comap f :
               Subgroup (stabilizer d.radical a)) ≤ Nat.card
                 (J.subgroupOf (stabilizer d.radical a) ⊓ Q₁ :
                   Subgroup (stabilizer d.radical a))) ∧
         (∀ c : Vertex d.radical, Adjacent d.radical c t →
           let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
             (Q d.radical t) (Nat.card F^2)
           (Jc ≠ J ∨ ¬ J.subgroupOf (stabilizer d.radical a) ≤ Q₁) →
           Nat.card F^2 < (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) :
             Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ∧
           ¬ IsQuadratic (restrictScalars (k := ZMod 2)
             (symplecticNatural (k := B.Carrier) 2))
             (((J ⊔ Jc).subgroupOf (stabilizer d.radical a)).map f)) ∧
         (J.subgroupOf (stabilizer d.radical a) ≤ Q₁ →
           Q d.radical t ⊓ D = J ∧
           Z d.radical z ≤ J ∧
           ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f <
             (J.subgroupOf (stabilizer d.radical a)).map f ∧
           U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
             U d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical))) ∧
         ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
           (D.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
             (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
           ((Z d.radical a ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
             centralizer ((D.map (MulAut.conj g).toMonoidHom).map
               (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
               Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
           x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
           x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
           (J.subgroupOf (stabilizer d.radical a) ≤ Q₁ →
             ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
               centralizer ((J.map (MulAut.conj g).toMonoidHom).map
                 (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
                 Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hsep,g,hg,x,hx,hgen,hfixed,hxn,hxp⟩ :=
    h.replacement_maximizing_parabolic_root_fixed_selection d path hb hat hfirst hsmall
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hsep,?_,g,hg,x,hx,hgen,hfixed,hxn,hxp,?_⟩
  · intro hJplane
    have hsat := h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
      B hB f hf hindex hJplane
    have hzJ := h.replacement_root_endpoint_le_small_mover d path hb hat hfirst hsmall
      B hB f hf hTf hindex hJplane
    refine ⟨hsat,hzJ,?_,h.replacement_small_mover_parabolic_fixed d geometry hb path.start_color hat
      B hB f hf hfQ hindex hJplane⟩
    let S := stabilizer d.radical a
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    have hJS : J ≤ S := by
      dsimp only [J]
      rw [←hsat]
      exact inf_le_right.trans ((map_le_range _ _).trans_eq (range_subtype _))
    have hcJ : Nat.card F^2 ≤ Nat.card ((J.subgroupOf S).map f) := by
      rw [←relIndex_ker]
      have hh := relIndex_map_map_of_injective f.ker (J.subgroupOf S) S.subtype_injective
      rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
      rw [←hh]
      exact h.replacement_small_mover_join_index d geometry hb path.start_color hat
    have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
    have hcZ : Nat.card (((Z d.radical z).subgroupOf S).map f) < Nat.card F^2 := by
      have hh := Sp4Four.SourceComparison.quotient_image_card _ _ _ hzS f hfQ
      have he : (f.comp (inclusion hzS)).range = ((Z d.radical z).subgroupOf S).map f := by
        rw [MonoidHom.range_comp]
        congr 1
        ext y
        exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
      rw [he] at hh
      rwa [hh]
    apply lt_of_le_of_ne (map_mono (comap_mono hzJ))
    intro he
    have hcZ' := hcZ.trans_le hcJ
    exact (Nat.ne_of_lt hcZ') (congrArg (fun A : Subgroup (Sp B.Carrier) => Nat.card A) he)
  · intro hJplane
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
      B hB f hf hfQ hindex hJplane
    have he₁ := conjugate_fixed_eq (Z d.radical a) J D he g
      (Z_normalized d.radical a (Ltilde_le_stabilizer a hg))
    have he₂ := conjugate_fixed_eq (Z d.radical a) _ _ he₁ x⁻¹
      (Z_normalized d.radical a ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hx)))
    apply le_antisymm
    · intro w hw
      have hw₁ : w ∈ Z d.radical a ⊓ centralizer
          (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) := he₁ ▸ hw.1
      have hw₂ : w ∈ Z d.radical a ⊓ centralizer
          ((D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom :
            Set (FreeAmalgam d.radical)) := he₂ ▸ ⟨hw.1.1,hw.2⟩
      exact hfixed ▸ ⟨hw₁,hw₂.2⟩
    · intro w hw
      have hwD : w ∈ (Z d.radical a ⊓ centralizer
          (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓ centralizer
          ((D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom :
            Set (FreeAmalgam d.radical)) := hfixed.symm ▸ hw
      refine ⟨he₁.symm ▸ hwD.1,?_⟩
      exact (show w ∈ Z d.radical a ⊓ centralizer
        ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom :
          Set (FreeAmalgam d.radical)) from he₂.symm ▸ ⟨hwD.1.1,hwD.2⟩).2

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
