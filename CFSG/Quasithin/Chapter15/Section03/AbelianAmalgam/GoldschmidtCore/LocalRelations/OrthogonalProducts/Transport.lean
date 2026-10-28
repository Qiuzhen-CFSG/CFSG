module

public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.ConjugateGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoordinateLifting
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.ProductConsequences

/-!
# Coordinate and kernel transport for the terminal line product

The fixed `NaturalAction` sends the relative normalizer of an ambient line
onto its actual coordinate stabilizer. Residual functoriality therefore
identifies the image of `Y_E` with the corresponding coordinate residual.
A two-group centralizer makes the kernel on `Y` a normal two-subgroup; lifting
the two coordinate factors then gives the literal product `Y_E Y_F O₂(Y)`.

The same coordinates preserve line cardinality, singularity, distinction and
a common nonidentity vector. Commutativity of the model residual also gives
relative normality using the independently proved ProductConsequences API.
The finite residual and product calculations are explicit premises here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7 and
the construction before 15.3.68, printed pp.1122 and 1154.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] {V M : Subgroup G}

/-- The image of the actual ambient line under the chosen vector coordinates. -/
def coordinateLine (d : NaturalAction V M) (E : Subgroup G) : Subgroup (Multiplicative Space) :=
  (E.subgroupOf V).map d.coordinates.toMonoidHom

/-- Membership is tested by the inverse of the actual coordinate equivalence. -/
theorem mem_coordinateLine (d : NaturalAction V M) (E : Subgroup G)
    (w : Multiplicative Space) : w ∈ coordinateLine d E ↔ (d.coordinates.symm w : G) ∈ E := by
  exact mem_map_equiv

/-- Coordinate membership after the action agrees with ambient conjugation. -/
theorem coordinateLine_action_mem (d : NaturalAction V M) (E : Subgroup G) (m : M) (v : V) :
    vectorAction (d.action m) (d.coordinates v) ∈ coordinateLine d E ↔
      MulAut.conj (m : G) (v : G) ∈ E := by
  rw [mem_coordinateLine]
  change (d.coordinates.symm (Multiplicative.ofAdd
    ((d.action m).val (Multiplicative.toAdd (d.coordinates v)))) : G) ∈ E ↔ _
  rw [d.intertwines]

/-- The coordinate stabilizer pulls back to the actual line normalizer. -/
theorem coordinateLine_stabilizer_iff (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (m : M) :
    d.action m ∈ lineStabilizer (coordinateLine d E) ↔ (m : G) ∈ lineNormalizer E := by
  constructor
  · intro h
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hc := (h (d.coordinates ⟨x, hEV hx⟩)).mpr
        ((mem_coordinateLine d E _).mpr (by simpa using hx))
      exact (coordinateLine_action_mem d E m ⟨x, hEV hx⟩).mp hc
    · intro hx
      have hxV : x ∈ V := (d.normalizes m.property x).mpr (hEV hx)
      have hc := (h (d.coordinates ⟨x, hxV⟩)).mp
        ((coordinateLine_action_mem d E m ⟨x, hxV⟩).mpr hx)
      simpa using (mem_coordinateLine d E _).mp hc
  · intro h w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    rw [coordinateLine_action_mem, mem_coordinateLine, d.coordinates.symm_apply_apply]
    exact (h v).symm

/-- Taking the relative line normalizer commutes with the compatible action. -/
theorem actionImage_lineNormalizer (d : NaturalAction V M) (Y E : Subgroup G)
    (hEV : E ≤ V) :
    actionImage d (Y ⊓ lineNormalizer E) = actionImage d Y ⊓ lineStabilizer (coordinateLine d E) := by
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨mem_map_of_mem _ hm.1, (coordinateLine_stabilizer_iff d E hEV m).mpr hm.2⟩
  · rintro ⟨⟨m, hm, rfl⟩, ha⟩
    exact mem_map.mpr ⟨m, ⟨hm, (coordinateLine_stabilizer_iff d E hEV m).mp ha⟩, rfl⟩

variable [Finite G]

private theorem twoResidual_eq_pResidual (H : Subgroup G) :
    Stellmacher.twoResidualSubgroup H = pResidual 2 H := by
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    refine ⟨hN, ?_⟩
    let := hN
    exact IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

/-- The embedded two-residual commutes with the action on a subgroup of `M`. -/
theorem actionImage_twoResidual (d : NaturalAction V M) (H : Subgroup G) (hHM : H ≤ M) :
    actionImage d (Stellmacher.twoResidualAmbient H) =
      Stellmacher.twoResidualAmbient (actionImage d H) := by
  have h := map_twoResidualAmbient_of_subgroup_image (H.subgroupOf M) M.subtype H
    (map_subgroupOf_eq_of_le hHM)
  have h' : (Stellmacher.twoResidualAmbient H).subgroupOf M =
      Stellmacher.twoResidualAmbient (H.subgroupOf M) := by
    rw [← h, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  rw [actionImage, h']
  exact map_twoResidualAmbient_of_subgroup_image _ _ _ rfl

/-- The image of `Y_E` is the intrinsic residual of the coordinate stabilizer. -/
theorem actionImage_lineY (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V)
    (himage : actionImage d Y = pResidual 2 IsometryGroup) :
    actionImage d (lineY Y E) = lineResidual (coordinateLine d E) := by
  change actionImage d (Stellmacher.twoResidualAmbient (Y ⊓ lineNormalizer E)) = _
  rw [actionImage_twoResidual d _ (inf_le_left.trans hYM),
    actionImage_lineNormalizer d Y E hEV, himage]
  unfold Stellmacher.twoResidualAmbient lineResidual
  rw [twoResidual_eq_pResidual]

omit [Finite G] in
/-- The coordinate line has the same order as its ambient counterpart. -/
theorem coordinateLine_card (d : NaturalAction V M) (E : Subgroup G) (hEV : E ≤ V) :
    Nat.card (coordinateLine d E) = Nat.card E := by
  rw [coordinateLine, card_map_of_injective d.coordinates.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hEV).toEquiv

omit [Finite G] in
/-- The given singularity condition is preserved by the fixed coordinates. -/
theorem coordinateLine_singular (d : NaturalAction V M) (E : Subgroup G) (hEV : E ≤ V)
    (hE : ∀ e : E, d.singular ⟨e, hEV e.property⟩) :
    ∀ w ∈ coordinateLine d E, form (Multiplicative.toAdd w) = 0 := by
  intro w hw
  have he := (mem_coordinateLine d E w).mp hw
  have h := hE ⟨d.coordinates.symm w, he⟩
  change form (Multiplicative.toAdd (d.coordinates (d.coordinates.symm w))) = 0 at h
  simpa using h

omit [Finite G] in
/-- Distinct ambient subgroups contained in `V` have distinct coordinate images. -/
theorem coordinateLine_injective (d : NaturalAction V M) (E F : Subgroup G)
    (hEV : E ≤ V) (hFV : F ≤ V) (h : coordinateLine d E = coordinateLine d F) : E = F := by
  have he := map_injective d.coordinates.injective h
  have hm := congrArg (Subgroup.map V.subtype) he
  simpa only [map_subgroupOf_eq_of_le hEV, map_subgroupOf_eq_of_le hFV] using hm

omit [Finite G] in
/-- A common nonidentity element gives a common nonidentity coordinate vector. -/
theorem coordinateLine_common_vector (d : NaturalAction V M) (E F : Subgroup G)
    (hEV : E ≤ V) (z : G) (hzE : z ∈ E) (hzF : z ∈ F) (hz : z ≠ 1) :
    ∃ w : Multiplicative Space, w ≠ 1 ∧ w ∈ coordinateLine d E ∧ w ∈ coordinateLine d F := by
  refine ⟨d.coordinates ⟨z, hEV hzE⟩, ?_, ?_, ?_⟩
  · intro h
    exact hz (congrArg Subtype.val (d.coordinates.injective (h.trans (map_one d.coordinates).symm)))
  · exact (mem_coordinateLine d E _).mpr (by simpa using hzE)
  · exact (mem_coordinateLine d F _).mpr (by simpa using hzF)


omit [Finite G] in
/-- A two-group centralizer puts the kernel on `Y` inside its intrinsic two-core. -/
theorem action_kernel_le_twoCore (d : NaturalAction V M) (Y : Subgroup G) (hYM : Y ≤ M)
    (hC : IsPGroup 2 (centralizer (V : Set G))) :
    Y ⊓ centralizer (V : Set G) ≤ Stellmacher.twoCoreAmbient Y := by
  let f : Y →* IsometryGroup := d.action.comp (inclusion hYM)
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf Y := by
    ext y
    have he := congrArg (fun K : Subgroup M => (inclusion hYM y) ∈ K) (action_ker d)
    exact Iff.of_eq he
  have hkp : IsPGroup 2 f.ker := by rw [hk]; exact hC.comap_subtype
  have hle : f.ker ≤ pCore 2 Y := le_sSup ⟨inferInstance, hkp⟩
  rintro y ⟨hy, hc⟩
  exact mem_map.mpr ⟨⟨y, hy⟩, hle (hk ▸ hc), rfl⟩

omit [Finite G] in
/-- Lift the image product, correcting the remaining factor inside `O₂(Y)`. -/
theorem line_product_of_action_product (d : NaturalAction V M) (Y E F : Subgroup G)
    (hYM : Y ≤ M) (hC : IsPGroup 2 (centralizer (V : Set G)))
    (hprod : (actionImage d Y : Set IsometryGroup) =
      (actionImage d (lineY Y E) : Set IsometryGroup) *
      (actionImage d (lineY Y F) : Set IsometryGroup)) :
    (Y : Set G) = (lineY Y E : Set G) * (lineY Y F : Set G) *
      (Stellmacher.twoCoreAmbient Y : Set G) := by
  apply Set.Subset.antisymm
  · intro y hy
    have hi : d.action ⟨y, hYM hy⟩ ∈ actionImage d Y := mem_map_of_mem _ hy
    rw [← SetLike.mem_coe, hprod] at hi
    obtain ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, hab⟩ := hi
    have hab' : d.action a * d.action b = d.action ⟨y, hYM hy⟩ := hab
    let q : M := (a * b)⁻¹ * ⟨y, hYM hy⟩
    have hqker : q ∈ d.action.ker := by
      change d.action ((a * b)⁻¹ * ⟨y, hYM hy⟩) = 1
      rw [map_mul, map_inv, map_mul, hab', inv_mul_cancel]
    have hqC : (q : G) ∈ centralizer (V : Set G) := by
      rw [action_ker d] at hqker
      exact hqker
    have hqY : (q : G) ∈ Y := Y.mul_mem
      (Y.inv_mem (Y.mul_mem ((lineY_le Y E).trans inf_le_left ha)
        ((lineY_le Y F).trans inf_le_left hb))) hy
    refine ⟨(a : G) * (b : G), ⟨a, ha, b, hb, rfl⟩, q,
      action_kernel_le_twoCore d Y hYM hC ⟨hqY, hqC⟩, ?_⟩
    exact mul_inv_cancel_left _ _
  · rintro y ⟨ab, ⟨a, ha, b, hb, rfl⟩, q, hq, rfl⟩
    exact Y.mul_mem (Y.mul_mem ((lineY_le Y E).trans inf_le_left ha)
      ((lineY_le Y F).trans inf_le_left hb)) (map_subtype_le _ hq)

/-- The coordinate residual product gives the literal three-factor product in `G`. -/
theorem line_product_of_coordinate_product (d : NaturalAction V M) (Y E F : Subgroup G)
    (hYM : Y ≤ M) (hC : IsPGroup 2 (centralizer (V : Set G)))
    (hEV : E ≤ V) (hFV : F ≤ V)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hprod : (pResidual 2 IsometryGroup : Set IsometryGroup) =
      (lineResidual (coordinateLine d E) : Set IsometryGroup) *
      (lineResidual (coordinateLine d F) : Set IsometryGroup)) :
    (Y : Set G) = (lineY Y E : Set G) * (lineY Y F : Set G) *
      (Stellmacher.twoCoreAmbient Y : Set G) := by
  apply line_product_of_action_product d Y E F hYM hC
  rw [actionImage_lineY d Y E hYM hEV himage,
    actionImage_lineY d Y F hYM hFV himage, himage]
  exact hprod

/-- Commutativity of the coordinate residual gives the required relative normality. -/
theorem lineY_normal_of_coordinate_commutative (d : NaturalAction V M) (Y T E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hTY : T ≤ normalizer (Y : Set G))
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hcomm : IsMulCommutative (pResidual 2 IsometryGroup)) :
    ((lineY Y E).subgroupOf (Y ⊔ lineT T E)).Normal := by
  have : IsMulCommutative (actionImage d Y) := himage ▸ hcomm
  exact lineY_normal_in_local_product Y T V E hEV hTY
    (actionImage_commutative_commutator d Y hYM)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
