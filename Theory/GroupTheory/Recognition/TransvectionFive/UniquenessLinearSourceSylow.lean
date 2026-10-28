module
public import Theory.GroupTheory.Recognition.TransvectionFive.NormalizerTransport
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Ambient Sylow subgroups of a marked transvection centralizer

The standard binary unitriangular Sylow lies in the model point centralizer.
The existing linear Sylow-center bound therefore gives a center of order at
most two for every Sylow of that centralizer. Under the original marking,
the central involution generates the center of its Sylow image. Its ambient
normalizer consequently fixes the involution, and the finite two-group
normalizer condition promotes the image to an ambient Sylow subgroup.

The canonical choice uses the original standard flag. All four marked root
groups lie in it, and transport of the unitriangular normalizer shows it is
self-normalizing in the original group. This proves Aschbacher, *Sporadic
Groups* (1994), 39.2, printed p.214, without a simplicity hypothesis, as
required when applying the local argument inside the subgroup generated
by normalizers in 41.1. Fusion control and the source comparison are not
asserted here.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open Theory.SpecificGroups.LinearSylowNormalizers

private theorem unipotent_le_point_centralizer : unipotent 5 (ZMod 2) ≤ centralizer := by
  intro g hg
  obtain ⟨hu, hd⟩ := (mem_unipotent 5 (ZMod 2) g).mp hg
  have hu := (mem_borel 5 (ZMod 2) g).mp hu
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  change (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (1 + Matrix.single 0 4 1) =
    (1 + Matrix.single 0 4 1) * (g : Matrix (Fin 5) (Fin 5) (ZMod 2))
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 4
  · subst i; subst j
    simp [hd]
  · subst i
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj,
      Matrix.single_mul_apply_same, one_mul]
    exact (hu (show j < 4 from by omega)).symm
  · subst j
    rw [Matrix.mul_single_apply_same, mul_one,
      Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]
    exact hu (show 0 < i from Fin.pos_iff_ne_zero.mpr hi)
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj,
      Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]

private def modelPointSylow : Sylow 2 centralizer :=
  (standardSylow 5 (ZMod 2) (by decide)).subtype (by
    simpa only [coe_standardSylow] using unipotent_le_point_centralizer)

private theorem model_point_sylow_center_bound (S : Sylow 2 centralizer) :
    Nat.card (Subgroup.center S) ≤ 2 := by
  rw [Nat.card_congr (Subgroup.centerCongr (S.equiv modelPointSylow)).toEquiv]
  let e : modelPointSylow ≃* standardSylow 5 (ZMod 2) (by decide) :=
    subgroupOfEquivOfLe (by
      simpa only [coe_standardSylow] using unipotent_le_point_centralizer)
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact BinaryLinear.sl_sylow_center_card_le_two (by decide) _

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

include F in
/-- The marked centralizer transfers the binary Sylow-center bound. -/
theorem point_sylow_center_bound
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    Nat.card (Subgroup.center S) ≤ 2 := by
  let P := S.mapSurjective (f := F.equiv.toMonoidHom) F.equiv.surjective
  let e : S ≃* P := (S : Subgroup _).equivMapOfInjective
    F.equiv.toMonoidHom F.equiv.injective
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact model_point_sylow_center_bound P

/-- The image of a Sylow subgroup of the full point centralizer. -/
abbrev pointSylowImage (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) : Subgroup G :=
  (S : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype

omit [Finite G] in
include F in
/-- The distinguished central involution lies in every local Sylow image. -/
theorem point_mem_pointSylowImage
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) : z ∈ pointSylowImage S := by
  let C := Subgroup.centralizer ({z} : Set G)
  let t : C := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective C.subtype Subtype.val_injective t]
    exact F.point_orderOf
  have hZ : zpowers t ≤ Subgroup.center C := by
    apply zpowers_le.mpr
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  let : (zpowers t).Normal := ⟨fun a ha b => by
    rw [mem_center_iff.mp (hZ ha) b, mul_inv_cancel_right]
    exact ha⟩
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  exact mem_map_of_mem C.subtype ((hp.le_sylow_of_normal S) (mem_zpowers t))

include F in
/-- The embedded Sylow center is exactly the original involution line. -/
theorem pointSylowImage_center
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    (Subgroup.center (pointSylowImage S)).map (pointSylowImage S).subtype = zpowers z := by
  let A := pointSylowImage S
  let e : S ≃* A := (S : Subgroup _).equivMapOfInjective
    (Subgroup.centralizer ({z} : Set G)).subtype Subtype.val_injective
  have hc : Nat.card (Subgroup.center A) ≤ 2 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact point_sylow_center_bound F S
  have hz : (⟨z, point_mem_pointSylowImage F S⟩ : A) ∈ Subgroup.center A := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (map_subtype_le _ a.property))
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem A.subtype hz)) ?_).symm
  change Nat.card ((Subgroup.center A).map A.subtype) ≤ Nat.card (zpowers z)
  rw [Nat.card_zpowers, F.point_orderOf, card_map_of_injective A.subtype_injective]
  exact hc

include F in
/-- The characteristic involution line forces ambient normalizer containment. -/
theorem pointSylowImage_normalizer_le
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    normalizer (pointSylowImage S : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
  normalizer_le_centralizer_of_characteristic_involution
    (pointSylowImage S) (Subgroup.center (pointSylowImage S)) z F.point_orderOf
    (pointSylowImage_center F S)

/-- Source 39.2: a Sylow subgroup of the full point centralizer is Sylow in G.
This construction does not require simplicity, fusion, or a hypothesis on a generated subgroup. -/
def pointSylow (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) : Sylow 2 G where
  toSubgroup := pointSylowImage S
  isPGroup' := S.isPGroup'.map _
  is_maximal' := by
    intro U hU hSU
    apply prime_overgroup_eq_of_normalizer_control (pointSylowImage S) ⊤
      (Subgroup.centralizer ({z} : Set G)) (pointSylowImage_normalizer_le F S) ?_ U hU hSU le_top
    intro V hV hSV _ hVC
    have he : V.subgroupOf (Subgroup.centralizer ({z} : Set G)) = S :=
      S.is_maximal' (hV.comap_subtype) (by
        intro s hs
        exact hSV (mem_map_of_mem _ hs))
    rw [← map_subgroupOf_eq_of_le hVC, he]

/-- Promotion preserves the literal subgroup image under centralizer inclusion. -/
theorem coe_pointSylow (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    (pointSylow F S : Subgroup G) = pointSylowImage S := by rfl

private theorem upper_le_unipotent : upper ≤ unipotent 5 (ZMod 2) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, rfl⟩
  change root hij ∈ unipotent 5 (ZMod 2)
  rw [mem_unipotent]
  constructor
  · apply (mem_borel 5 (ZMod 2) _).mpr
    exact Matrix.blockTriangular_transvection hij.le 1
  · intro k
    simp [root, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
    aesop

private theorem unipotent_normalizer :
    normalizer (unipotent 5 (ZMod 2) : Set SL) = unipotent 5 (ZMod 2) := by
  rw [normalizer_unipotent]
  apply le_antisymm _ (unipotent_le_borel 5 (ZMod 2))
  intro g hg
  apply (mem_unipotent 5 (ZMod 2) g).mpr
  refine ⟨hg, fun i => ?_⟩
  have hd := g.property
  rw [Matrix.det_of_isUpperTriangular ((mem_borel 5 (ZMod 2) g).mp hg)] at hd
  have hn : g.val i i ≠ 0 := Finset.prod_ne_zero_iff.mp
    (show (∏ j, g.val j j) ≠ 0 by rw [hd]; exact one_ne_zero) i (Finset.mem_univ i)
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn

/-- The source Sylow uses the standard flag under the original centralizer marking. -/
def sourceSylow : Sylow 2 G :=
  pointSylow F (modelPointSylow.mapSurjective (f := F.equiv.symm.toMonoidHom)
    F.equiv.symm.surjective)

/-- Its subgroup is the literal marked pullback of the upper unitriangular group. -/
theorem coe_sourceSylow : (sourceSylow F : Subgroup G) = F.pullback (unipotent 5 (ZMod 2)) := by
  change pointSylowImage (modelPointSylow.mapSurjective
    (f := F.equiv.symm.toMonoidHom) F.equiv.symm.surjective) = _
  change (((standardSylow 5 (ZMod 2) (by decide) : Subgroup SL).subgroupOf centralizer).map
    F.equiv.symm.toMonoidHom).map (Subgroup.centralizer ({z} : Set G)).subtype = _
  rw [coe_standardSylow]
  rfl

/-- The flag Sylow lies in the original full point centralizer. -/
theorem sourceSylow_le_point_centralizer :
    (sourceSylow F : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [coe_sourceSylow]
  exact F.pullback_le _

/-- Every point-centralizer Sylow center is the original involution line. -/
theorem sourceSylow_center :
    (Subgroup.center (sourceSylow F)).map (sourceSylow F : Subgroup G).subtype = zpowers z := by
  change (Subgroup.center (pointSylowImage _)).map (pointSylowImage _).subtype = _
  exact pointSylowImage_center F _

/-- The canonical Sylow has no ambient normalizer outside the full point centralizer. -/
theorem sourceSylow_normalizer_le_point_centralizer :
    normalizer ((sourceSylow F : Subgroup G) : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  exact pointSylowImage_normalizer_le F _

omit [Finite G] in
private theorem pullback_mono {A B : Subgroup SL} (hAB : A ≤ B) :
    F.pullback A ≤ F.pullback B :=
  map_mono (map_mono (comap_mono hAB))

/-- The four marked groups all lie in the same actual ambient Sylow subgroup. -/
theorem flag_le_sourceSylow :
    F.row ≤ (sourceSylow F : Subgroup G) ∧
    F.column ≤ (sourceSylow F : Subgroup G) ∧
    F.plane ≤ (sourceSylow F : Subgroup G) ∧
    F.threeSpace ≤ (sourceSylow F : Subgroup G) := by
  rw [coe_sourceSylow]
  exact ⟨pullback_mono F (dualFactor_le_kernel.trans (kernel_le_upper.trans upper_le_unipotent)),
    pullback_mono F (naturalFactor_le_kernel.trans (kernel_le_upper.trans upper_le_unipotent)),
    pullback_mono F ((rectangle_le_upper 2).trans upper_le_unipotent),
    pullback_mono F ((rectangle_le_upper 3).trans upper_le_unipotent)⟩

/-- The actual source flag Sylow is self-normalizing, by transport inside C_G(z). -/
theorem sourceSylow_normalizer : normalizer ((sourceSylow F : Subgroup G) : Set G) = sourceSylow F := by
  have he := F.pullback_relativeNormalizer (unipotent 5 (ZMod 2)) unipotent_le_point_centralizer
  rw [unipotent_normalizer, inf_eq_right.mpr unipotent_le_point_centralizer,
    ← coe_sourceSylow, inf_eq_right.mpr (sourceSylow_normalizer_le_point_centralizer F)] at he
  exact he.symm

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
