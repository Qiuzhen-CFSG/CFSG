module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.CoordinateData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Lifting

/-!
# The two cubic residual plane actions

The matrix `(x,y) ↦ (y,x+y)` has order three and invertible displacement
on the four-element plane. Supported on coordinate `j`, it belongs to the
full orthogonal two-residual and fixes the other plane `i`. The full-image
hypothesis lifts it into the literal centralizer of that plane; finite
residual-image transport then puts it in the image of `O²(C_Y(Vᵢ))`.

Both residual-centralizer images are nontrivial and disjoint in the known
order-nine image of Y, so each has order three. Thus the image centralizing
`i` is exactly the cyclic group supported on `j`. Literal conjugation
compatibility transports the cubic displacement to both `[V,O²(C_Y(Vᵢ))]`
and `[Vⱼ,O²(C_Y(Vᵢ))]`, giving Vⱼ. The two labels remain independent,
and no hypothesis on the order of Y/O₂(Y) is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the definite
plane construction and 15.3.7 on printed pp.1121–1122, and its uses in
15.3.39–40 on pp.1137–1138. This produces the coordinate facts required by
the CaseOne assembly; the earlier source proof of the full image is an input.
-/

open Subgroup
open scoped Matrix commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
namespace FullActionCoordinates
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

/-- The actual order-three binary matrix, acting by `(x,y) ↦ (y,x+y)`. -/
@[expose] public def cubicMatrix : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide +kernel⟩

private theorem cubicMatrix_cube : cubicMatrix ^ 3 = 1 := by decide +kernel

private theorem cubicMatrix_ne_one : cubicMatrix ≠ 1 := by decide +kernel

private theorem cubicMatrix_displacement : ∀ w : OrthogonalPlaneVector,
    cubicMatrix • (cubicMatrix • w) * (cubicMatrix • w)⁻¹ = w := by decide +kernel

/-- Embed a matrix in the indicated moving coordinate, with no plane permutation. -/
@[expose] public def coordinateEmbedding (j : OrthogonalPlaneIndex) : OrthogonalPlaneActor →* OrthogonalActor where
  toFun a := ⟨fun k => if k = j then a else 1, 1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext k; simp
    · rfl
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext k
      by_cases hk : k = j <;> simp [hk]
    · simp

/-- The cubic actor supported on the moving plane `j`. -/
@[expose] public def coordinateCubic (j : OrthogonalPlaneIndex) : OrthogonalActor :=
  coordinateEmbedding j cubicMatrix

/-- Each supported cubic belongs to the odd-order part of the orthogonal actor. -/
public theorem coordinateCubic_cube (j : OrthogonalPlaneIndex) : coordinateCubic j ^ 3 = 1 := by
  rw [coordinateCubic, ← map_pow, cubicMatrix_cube, map_one]

/-- The supported cubic is nonidentity for either plane label. -/
public theorem coordinateCubic_ne_one (j : OrthogonalPlaneIndex) : coordinateCubic j ≠ 1 := by
  intro h
  have he := congrArg (fun a : OrthogonalActor => a.left j) h
  exact cubicMatrix_ne_one (by simpa [coordinateCubic, coordinateEmbedding] using he)

private theorem coordinateCubic_smul (j k : OrthogonalPlaneIndex) (v : OrthogonalVector) :
    (coordinateCubic j • v) k = (if k = j then cubicMatrix else 1) • v k := by
  change (if k = j then cubicMatrix else 1) • v ((1 : OrthogonalPlaneIndex)⁻¹ * k) = _
  rw [inv_one, one_mul]

private theorem coordinateCubic_fixes {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (v : OrthogonalVector) (hv : v ∈ orthogonalCoordinatePlane i) :
    coordinateCubic j • v = v := by
  funext k
  rw [coordinateCubic_smul]
  by_cases hk : k = j
  · subst k
    rw [if_pos rfl, hv j hij.symm, smul_one]
  · rw [if_neg hk, one_smul]

private theorem coordinateCubic_displacement (j : OrthogonalPlaneIndex)
    (v : OrthogonalVector) (hv : v ∈ orthogonalCoordinatePlane j) :
    ∃ w ∈ orthogonalCoordinatePlane j, coordinateCubic j • w * w⁻¹ = v := by
  let w : OrthogonalVector := fun k => if k = j then cubicMatrix • v k else 1
  refine ⟨w, (fun k hk => if_neg hk), ?_⟩
  funext k
  change (coordinateCubic j • w) k * (w k)⁻¹ = v k
  rw [coordinateCubic_smul]
  by_cases hk : k = j
  · simp only [w, if_pos hk]
    exact cubicMatrix_displacement _
  · simp only [w, if_neg hk, one_smul, inv_one, one_mul]
    exact (hv k hk).symm

variable {G : Type*} [Group G]

private theorem cubic_mem_residual [Finite G] (C : Subgroup G) {a : G}
    (ha : a ∈ C) (hc : a ^ 3 = 1) : a ∈ Stellmacher.twoResidualAmbient C := by
  rw [Stellmacher.twoResidualAmbient,
    Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual']
  refine ⟨⟨a, ha⟩, ?_, rfl⟩
  have hp : (⟨a, ha⟩ : C) ^ 3 = 1 := Subtype.ext hc
  apply (show pResidual 2 C ≤ BenderSuzuki.External.hktPResidual 2 C from
    sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
      BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩)
  exact mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp))

private theorem image_twoResidual [Finite G] {M V C : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hCM : C ≤ M) :
    d.image (Stellmacher.twoResidualAmbient C) =
      Stellmacher.twoResidualAmbient (d.image C) := by
  have he := map_twoResidualAmbient_of_subgroup_image (C.subgroupOf M) M.subtype C
    (map_subgroupOf_eq_of_le hCM)
  have hsub : (Stellmacher.twoResidualAmbient C).subgroupOf M =
      Stellmacher.twoResidualAmbient (C.subgroupOf M) := by
    rw [← he]
    exact comap_map_eq_self_of_injective M.subtype_injective _
  change ((Stellmacher.twoResidualAmbient C).subgroupOf M).map d.actor = _
  rw [hsub]
  exact map_twoResidualAmbient_of_subgroup_image _ _ _ rfl

private theorem coordinateCubic_zpowers_fix_coordinate (j k : OrthogonalPlaneIndex) (hk : k ≠ j)
    {a : OrthogonalActor} (ha : a ∈ zpowers (coordinateCubic j)) (v : OrthogonalVector) :
    (a • v) k = v k := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
  rw [coordinateCubic, ← map_zpow]
  change (if k = j then cubicMatrix ^ n else 1) • v ((1 : OrthogonalPlaneIndex)⁻¹ * k) = v k
  simp [hk]

private theorem plane_mem_iff {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ d.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem centralizes_of_coordinateCubic {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (m : M) (hm : d.actor m = coordinateCubic j) :
    (m : G) ∈ centralizer (d.plane i : Set G) := by
  intro v hv
  let v₀ : V := ⟨v, d.plane_le i hv⟩
  have hc := d.compatible m v₀
  rw [hm, coordinateCubic_fixes hij _ ((plane_mem_iff d i v₀).mp hv)] at hc
  have he := congrArg Subtype.val (d.coordinates.injective hc)
  change (m : G) * v * (m : G)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem cubic_mem_factor_image [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    coordinateCubic j ∈ d.image (centralizingFactor Y (d.plane i)) := by
  have ha : coordinateCubic j ∈ d.image Y := by
    rw [himage]
    exact orthogonal_cubic_mem_twoResidual _ (coordinateCubic_cube j)
  obtain ⟨m, hmY, hm⟩ := ha
  have hmC : (m : G) ∈ Y ⊓ centralizer (d.plane i : Set G) :=
    ⟨hmY, centralizes_of_coordinateCubic d hij m hm⟩
  rw [centralizingFactor, image_twoResidual d (inf_le_left.trans hYM)]
  exact cubic_mem_residual _ (mem_map.mpr ⟨m, hmC, hm⟩) (coordinateCubic_cube j)

private theorem factor_image_ne_bot [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (i : OrthogonalPlaneIndex) :
    d.image (centralizingFactor Y (d.plane i)) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := exists_ne i
  intro hbot
  have hm := cubic_mem_factor_image d hYM himage hj.symm
  rw [hbot, mem_bot] at hm
  exact coordinateCubic_ne_one j hm

private theorem factor_image_card [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (i : OrthogonalPlaneIndex) :
    Nat.card (d.image (centralizingFactor Y (d.plane i))) = 3 := by
  let A := d.image (centralizingFactor Y (d.plane i))
  have hle : A ≤ d.image Y :=
    map_mono (fun x hx => centralizingFactor_le_left Y (d.plane i) hx)
  have hcard : Nat.card (d.image Y) = 9 := himage ▸ orthogonal_twoResidual_card
  have hd : Nat.card A ∣ 3 ^ 2 := by
    have hd := card_dvd_of_le hle
    rw [hcard] at hd
    convert hd using 1
    norm_num
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hnot1 : Nat.card A ≠ 1 := fun h =>
    factor_image_ne_bot d hYM himage i (card_eq_one.mp h)
  have hnot9 : Nat.card A ≠ 9 := by
    intro h
    have hA : A = d.image Y := eq_of_le_of_card_ge hle (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    have hdis := natural_centralizingFactor_images_disjoint (X := Y) d hj.symm
    have hB : d.image (centralizingFactor Y (d.plane j)) ≤ A := by
      rw [hA]
      exact map_mono (fun x hx => centralizingFactor_le_left Y (d.plane j) hx)
    have hbot : d.image (centralizingFactor Y (d.plane j)) = ⊥ := by
      apply le_bot_iff.mp
      exact (le_inf hB le_rfl).trans hdis.le_bot
    exact factor_image_ne_bot d hYM himage j hbot
  change Nat.card A = 3
  interval_cases n
  · exact False.elim (hnot1 (he.trans (by norm_num)))
  · simpa only [pow_one] using he
  · exact False.elim (hnot9 (he.trans (by norm_num)))

private theorem factor_image_eq [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    d.image (centralizingFactor Y (d.plane i)) = zpowers (coordinateCubic j) := by
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr (cubic_mem_factor_image d hYM himage hij))
  rw [factor_image_card d hYM himage i, Nat.card_zpowers,
    orderOf_eq_prime (coordinateCubic_cube j) (coordinateCubic_ne_one j)]

private theorem commutator_upper {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) (j : OrthogonalPlaneIndex)
    (himage : d.image X = zpowers (coordinateCubic j)) :
    ⁅V, X⁆ ≤ d.plane j := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx v hv
  let m : M := ⟨x, hXM hx⟩
  let v₀ : V := ⟨v, hv⟩
  let w : V := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀ * v₀⁻¹
  change (w : G) ∈ d.plane j
  rw [plane_mem_iff]
  dsimp only [w]
  rw [map_mul, map_inv, d.compatible]
  have ha : d.actor m ∈ zpowers (coordinateCubic j) := by
    rw [← himage]
    exact mem_map.mpr ⟨m, hx, rfl⟩
  intro k hk
  change (d.actor m • d.coordinates v₀) k * (d.coordinates v₀ k)⁻¹ = 1
  rw [coordinateCubic_zpowers_fix_coordinate j k hk ha, mul_inv_cancel]

private theorem commutator_lower {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (j : OrthogonalPlaneIndex)
    (himage : d.image X = zpowers (coordinateCubic j)) :
    d.plane j ≤ ⁅d.plane j, X⁆ := by
  rw [commutator_comm]
  intro v hv
  let v₀ : V := ⟨v, d.plane_le j hv⟩
  obtain ⟨w, hw, he⟩ := coordinateCubic_displacement j (d.coordinates v₀)
    ((plane_mem_iff d j v₀).mp hv)
  let w₀ := d.coordinates.symm w
  have hw₀ : (w₀ : G) ∈ d.plane j :=
    (plane_mem_iff d j w₀).mpr (by simpa only [w₀, MulEquiv.apply_symm_apply] using hw)
  have ha : coordinateCubic j ∈ d.image X := by rw [himage]; exact mem_zpowers _
  obtain ⟨m, hmX, hm⟩ := ha
  have hc : d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ w₀ * w₀⁻¹) =
      d.coordinates v₀ := by
    rw [map_mul, map_inv, d.compatible, hm]
    simpa only [w₀, MulEquiv.apply_symm_apply] using he
  have heq := congrArg Subtype.val (d.coordinates.injective hc)
  change ⁅(m : G), (w₀ : G)⁆ = v at heq
  rw [← heq]
  exact commutator_mem_commutator hmX hw₀

private theorem coordinate_facts [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    FullActionCoordinateFacts d Y := by
  have hle (i : OrthogonalPlaneIndex) : centralizingFactor Y (d.plane i) ≤ M :=
    (centralizingFactor_le_left _ _).trans hYM
  refine ⟨factor_image_card d hYM himage, ?_, ?_⟩
  · intro i j hij
    have he := factor_image_eq d hYM himage hij
    exact le_antisymm (commutator_upper d (hle i) j he)
      ((commutator_lower d j he).trans (commutator_mono (d.plane_le j) le_rfl))
  · intro i j hij
    have he := factor_image_eq d hYM himage hij
    exact le_antisymm
      ((commutator_mono (d.plane_le j) le_rfl).trans (commutator_upper d (hle i) j he))
      (commutator_lower d j he)

end FullActionCoordinates

variable {G : Type*} [Group G] [Finite G]

/-- The image centralizing plane `i` is exactly the cubic factor on the distinct
moving plane `j`. This equation retains both source plane labels. -/
public theorem residualY_centralizingFactor_image_eq_coordinateCubic {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    d.image (centralizingFactor (residualY M Mc) (d.plane i)) =
      zpowers (FullActionCoordinates.coordinateCubic j) :=
  FullActionCoordinates.factor_image_eq d
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) h7 hij

/-- The genuine full residual image supplies all cubic coordinate facts.
No order-nine two-core quotient, actor pair, or containment premise is needed. -/
public theorem residualY_fullActionCoordinateFacts {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    FullActionCoordinateFacts d (residualY M Mc) :=
  FullActionCoordinates.coordinate_facts d
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) h7

end CFSG.Quasithin.Chapter15.Section03.RankTwo
