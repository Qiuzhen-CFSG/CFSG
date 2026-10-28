module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Summands

/-!
# Multiplicative coordinates on the actual cubic blocks

The D-centralizer projects isomorphically to its fixed natural summand.
It commutes with V and intersects V trivially, so ambient multiplication
identifies C_P(D)V with the direct product. Append the two-dimensional
centralizer coordinate to the four-dimensional tensor coordinate. For the
second block, transpose the tensor so that its natural summand is the row
index. This constructs an equivalence with the six-coordinate block model
and identifies V exactly with the zero-first-column subgroup.

The equivalence is specified on every source vector in V. In particular
it preserves the determinant quadratic form, and transports singular and
nonsingular source markings without an order-only identification.
The action of I on the lifted centralizer coordinate is not yet proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.54(4)
and 15.3.61(2), printed pp.1146 and 1150–1151.
-/

@[expose] public section
open Subgroup Matrix
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

/-- Turn the fixed summand into the row index for either of the two blocks. -/
def orientTensor (i : Fin 2) : TensorVector ≃* TensorVector where
  toFun x := if i = 0 then x else Multiplicative.ofAdd x.toAdd.transpose
  invFun x := if i = 0 then x else Multiplicative.ofAdd x.toAdd.transpose
  left_inv x := by fin_cases i <;> rfl
  right_inv x := by fin_cases i <;> rfl
  map_mul' x y := by fin_cases i <;> rfl

/-- Append the tensor columns to the natural first column. -/
def appendColumns : Plane × TensorVector ≃* BlockModel where
  toFun x := Multiplicative.ofAdd fun i => Fin.cons (x.1.toAdd i) (x.2.toAdd i)
  invFun x := (Multiplicative.ofAdd (first x), Multiplicative.ofAdd (matrix x))
  left_inv x := rfl
  right_inv x := by
    funext i j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  map_mul' x y := by
    funext i j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl

variable {G : Type*} [Group G] [Finite G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

/-- Split the actual block by multiplication of its commuting, disjoint factors. -/
noncomputable def splitBlock (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G)) (i : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    fusionBlock P V D ≃* (P ⊓ centralizer (D : Set G) : Subgroup G) × V := by
  let C := P ⊓ centralizer (D : Set G)
  have hc : ∀ c : C, ∀ v : V, Commute (c : G) (v : G) := by
    intro c v
    exact hcentral v.property c c.property.1
  have hd : Disjoint C V :=
    (centralizer_disjoint_lower d i D himage).mono_left inf_le_right
  let f := C.subtype.noncommCoprod V.subtype hc
  have hr : f.range = fusionBlock P V D := by
    exact (MonoidHom.noncommCoprod_range C.subtype V.subtype hc).trans
      (by rw [C.range_subtype, V.range_subtype]; rfl)
  let f' : C × V →* fusionBlock P V D :=
    f.codRestrict _ (fun x => hr ▸ (show f x ∈ f.range from ⟨x, rfl⟩))
  have hi : Function.Injective f' := by
    intro x y h
    exact Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective f' := by
    intro y
    have hy : (y : G) ∈ f.range := by rw [hr]; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact (MulEquiv.ofBijective f' ⟨hi, hs⟩).symm

omit [Finite G] in
theorem splitBlock_symm_coe (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G)) (i : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i)
    (x : (P ⊓ centralizer (D : Set G) : Subgroup G) × V) :
    ((splitBlock d hcentral i D himage).symm x : G) = (x.1 : G) * x.2 := rfl

/-- Canonical block coordinates using the actual centralizer, the quotient
projection on its fixed summand, and the given tensor coordinates on V. -/
noncomputable def blockEquiv (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    fusionBlock P V D ≃* BlockModel :=
  (splitBlock d hcentral i D himage).trans
    ((MulEquiv.prodCongr
      ((centralizerEquiv d hVP hcentral i D hDI hD himage).trans (naturalSummandEquiv i))
      (d.lowerCoordinates.trans (orientTensor i))).trans appendColumns)

/-- In these constructed coordinates, the marked subgroup is exactly the
zero-first-column subgroup. -/
theorem blockEquiv_distinguished (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i)
    (x : fusionBlock P V D) :
    (x : G) ∈ V ↔ blockEquiv d hVP hcentral i D hDI hD himage x ∈ modelV := by
  let s := splitBlock d hcentral i D himage
  let c := (centralizerEquiv d hVP hcentral i D hDI hD himage).trans (naturalSummandEquiv i)
  have he : (x : G) = ((s x).1 : G) * (s x).2 := by
    rw [← splitBlock_symm_coe d hcentral i D himage]
    exact congrArg Subtype.val (s.symm_apply_apply x).symm
  have hm : blockEquiv d hVP hcentral i D hDI hD himage x ∈ modelV ↔ (s x).1 = 1 := by
    change c (s x).1 = 1 ↔ (s x).1 = 1
    exact map_eq_one_iff c c.injective
  rw [hm]
  constructor
  · intro hx
    have hcV : ((s x).1 : G) ∈ V := by
      have h := V.mul_mem hx (V.inv_mem (s x).2.property)
      rwa [he, mul_inv_cancel_right] at h
    apply Subtype.ext
    exact (disjoint_def.mp (centralizer_disjoint_lower d i D himage))
      (s x).1.property.2 hcV
  · intro hc
    rw [he, hc, OneMemClass.coe_one, one_mul]
    exact (s x).2.property

/-- The group order is a consequence of the constructed multiplicative coordinates. -/
theorem fusionBlock_card (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    Nat.card (fusionBlock P V D) = 64 := by
  rw [Nat.card_congr (blockEquiv d hVP hcentral i D hDI hD himage).toEquiv,
    Nat.card_eq_fintype_card]
  decide

/-- Elementary abelianness is transported through the multiplicative coordinates. -/
theorem fusionBlock_elementary (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) :
    IsElementaryAbelian 2 (fusionBlock P V D) := by
  let e := blockEquiv d hVP hcentral i D hDI hD himage
  refine { toIsMulCommutative := IsMulCommutative.of_comm (fun x y => e.injective ?_)
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => ?_) }
  · simp only [map_mul, mul_comm]
  · apply e.injective
    rw [map_pow, map_one]
    have h : ∀ x : BlockModel, x ^ 2 = 1 := by decide +kernel
    exact h _


/-- The equivalence uses the supplied lower-layer coordinates on each
actual element of V, with the transpose needed for the second block. -/
theorem blockEquiv_lower (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) (v : V) :
    blockEquiv d hVP hcentral i D hDI hD himage
      ⟨v, (show V ≤ fusionBlock P V D from le_sup_right) v.property⟩ =
      appendColumns (1, orientTensor i (d.lowerCoordinates v)) := by
  let s := splitBlock d hcentral i D himage
  let x : fusionBlock P V D :=
    ⟨v, (show V ≤ fusionBlock P V D from le_sup_right) v.property⟩
  have hs : s x = (1, v) := by
    apply s.symm.injective
    rw [s.symm_apply_apply]
    apply Subtype.ext
    rw [splitBlock_symm_coe]
    exact (one_mul (v : G)).symm
  change appendColumns
    (((centralizerEquiv d hVP hcentral i D hDI hD himage).trans (naturalSummandEquiv i))
      (s x).1, (d.lowerCoordinates.trans (orientTensor i)) (s x).2) = _
  rw [hs, map_one]
  rfl

/-- The orthogonal determinant of a source vector is preserved in either block. -/
theorem blockEquiv_lower_det (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) (v : V) :
    (matrix (blockEquiv d hVP hcentral i D hDI hD himage
      ⟨v, (show V ≤ fusionBlock P V D from le_sup_right) v.property⟩)).det =
      (d.lowerCoordinates v).toAdd.det := by
  rw [blockEquiv_lower]
  change (orientTensor i (d.lowerCoordinates v)).toAdd.det = _
  fin_cases i
  · rfl
  · exact Matrix.det_transpose _

/-- A nonidentity singular source vector goes to the singular model locus. -/
theorem blockEquiv_singular (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i)
    (z : V) (hz : (z : G) ≠ 1) (hq : (d.lowerCoordinates z).toAdd.det = 0) :
    Singular (blockEquiv d hVP hcentral i D hDI hD himage
      ⟨z, (show V ≤ fusionBlock P V D from le_sup_right) z.property⟩) := by
  refine ⟨(blockEquiv_distinguished d hVP hcentral i D hDI hD himage _).mp z.property,
    ?_, (blockEquiv_lower_det d hVP hcentral i D hDI hD himage z).trans hq⟩
  intro he
  have hx := (map_eq_one_iff
    (blockEquiv d hVP hcentral i D hDI hD himage)
    (blockEquiv d hVP hcentral i D hDI hD himage).injective).mp he
  exact hz (congrArg Subtype.val hx)

/-- A nonsingular source vector goes to the nonsingular model locus. -/
theorem blockEquiv_nonsingular (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (i : Fin 2) (D : Subgroup G) (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i)
    (v : V) (hq : (d.lowerCoordinates v).toAdd.det ≠ 0) :
    Nonsingular (blockEquiv d hVP hcentral i D hDI hD himage
      ⟨v, (show V ≤ fusionBlock P V D from le_sup_right) v.property⟩) := by
  exact ⟨(blockEquiv_distinguished d hVP hcentral i D hDI hD himage _).mp v.property,
    (blockEquiv_lower_det d hVP hcentral i D hDI hD himage v) ▸ hq⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
