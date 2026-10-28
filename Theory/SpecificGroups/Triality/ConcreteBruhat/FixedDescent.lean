module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.InputRealization

/-!
# Fixed-point descent of the concrete triality cells

Uniqueness of the split normal form makes its positive, torus, Weyl, and
supported right factors graph-field fixed. Positive fixed elements have
characteristic-power order, and the proved folded torus and Weyl words are
elementary. Thus the full fixed group equals its original elementary subgroup.
The proved trivial central kernel then gives a faithful map of the original
carrier into the literal split matrices.

Under this map, each carrier Borel double coset is exactly the intersection
of the corresponding split cell with the fixed matrices. In particular the
twelve published relative cells cover the carrier and have unique indices.
Membership in the original root parabolic reads off the corresponding marked
split Weyl subgroup. No assertion that fixed points preserve generation is used.
Every positive binary exponent, including q = 2, is covered.

Source: the proofs of GLS3 2.3.4–5, 2.3.8(c), and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat.FixedDescent
open Parabolics
open Theory.AlgebraicGroup.StandardRootSystem

/-- The normal-form lift is the published folded matrix word. -/
theorem lift_rootRepresentative (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) :
    (InputRealization.inputs P hp).lift (rootRepresentative w) = splitRepresentative P hp w := by
  have he := congrArg (fun v : rootWeylGroup => ((splitWeylEquiv P hp).symm v).val)
    (splitWeylEquiv_representative P hp w)
  exact he.symm.trans (congrArg Subtype.val
    ((splitWeylEquiv P hp).symm_apply_apply (fixedSplitRepresentative P hp w).val))

/-- Fixed normal-form indices are precisely the twelve relative Weyl words. -/
theorem fixed_index (P : Parameters) (hp : P.prime = 2) (v : rootWeylGroup)
    (hv : (InputRealization.inputs P hp).weylTwist v = v) :
    ∃ w : DihedralGroup 6, rootRepresentative w = v := by
  let D := InputRealization.inputs P hp
  have hf : graphFieldAutomorphism P ((D).lift v) = (D).lift v :=
    (D.graphField_lift v).trans (congrArg (D).lift hv)
  let vf : fixedSplitWeylSubgroup P := ⟨(splitWeylEquiv P hp).symm v, hf⟩
  obtain ⟨w, hw⟩ := splitRepresentative_surjective_fixed P hp vf
  refine ⟨w, (D).lift_injective ?_⟩
  exact (lift_rootRepresentative P hp w).trans hw

/-- Every positive fixed element has characteristic-power order in the fixed group. -/
theorem positive_mem_elementary (P : Parameters) (hp : P.prime = 2)
    (g : fixedSubgroup P) (hg : g.val ∈ positiveSubgroup P) :
    g ∈ elementarySubgroup P := by
  obtain ⟨k, hk⟩ := isPGroup_positiveSubgroup P hp ⟨g.val, hg⟩
  exact mem_elementarySubgroup_of_pow P g k
    (Subtype.ext (congrArg (fun x : positiveSubgroup P => x.val) hk))

/-- All four factors of a fixed normal form lie in the actual elementary subgroup. -/
private theorem elementarySubgroup_eq_top_of_lifts (n : ℕ) (hn : 0 < n)
    (D : SplitNormalForm.Inputs (binaryParameters n hn))
    (hLift : ∀ w, D.weylTwist w = w →
      ∃ e : ElementaryGroup (binaryParameters n hn), elementaryInclusion _ e = (D).lift w) :
    elementarySubgroup (binaryParameters n hn) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨c, hc, _⟩ := SplitNormalForm.existsUnique_coordinates n hn D g.val
  have hf := (SplitNormalForm.evaluate_mem_fixed_iff n hn D c).mp
    (hc.symm ▸ g.property)
  obtain ⟨e, he⟩ := hLift c.weyl hf.2.2.1
  let u : fixedSubgroup (binaryParameters n hn) := ⟨c.left.val, hf.1⟩
  let t : fixedSubgroup (binaryParameters n hn) := ⟨c.torus.val, hf.2.1⟩
  let v : fixedSubgroup (binaryParameters n hn) := ⟨PositiveCoordinates.orderedProduct (binaryParameters n hn) c.right,
    (PositiveCoordinates.orderedProduct_mem_fixedSubgroup_iff_binary n hn c.right).mpr hf.2.2.2⟩
  have hu := positive_mem_elementary (binaryParameters n hn) rfl u c.left.property
  have ht := TorusCoordinates.fixedTorus_le_elementary (binaryParameters n hn) rfl
    (show t ∈ (splitTorus (binaryParameters n hn)).comap (fixedSubgroup (binaryParameters n hn)).subtype from c.torus.property)
  have hv : v ∈ elementarySubgroup (binaryParameters n hn) := by
    apply positive_mem_elementary (binaryParameters n hn) rfl
    exact (PositiveCoordinates.range_orderedProduct_binary n hn).le ⟨c.right, rfl⟩
  have hprod : u * t * e.val * v = g := by
    apply Subtype.ext
    change c.left.val * c.torus.val * elementaryInclusion (binaryParameters n hn) e *
      PositiveCoordinates.orderedProduct (binaryParameters n hn) c.right = g.val
    exact (congrArg (fun z : SplitGroup (binaryParameters n hn) =>
      c.left.val * c.torus.val * z * PositiveCoordinates.orderedProduct (binaryParameters n hn) c.right)
        he).trans hc
  exact hprod ▸ (elementarySubgroup (binaryParameters n hn)).mul_mem
    ((elementarySubgroup (binaryParameters n hn)).mul_mem ((elementarySubgroup (binaryParameters n hn)).mul_mem hu ht)
      e.property) hv

private theorem elementary_lift_fixed_index (P : Parameters) (hp : P.prime = 2)
    (v : rootWeylGroup) (hv : (InputRealization.inputs P hp).weylTwist v = v) :
    ∃ e : ElementaryGroup P, elementaryInclusion P e = (InputRealization.inputs P hp).lift v :=
  Exists.elim (fixed_index P hp v hv) (fun w hw =>
    ⟨weylElementary P hp w,
      (lift_rootRepresentative P hp w).symm.trans
        (congrArg (InputRealization.inputs P hp).lift hw)⟩)

/-- The fixed torus and the twelve folded words discharge all elementary lifts. -/
theorem elementarySubgroup_eq_top_binary (n : ℕ) (hn : 0 < n) :
    elementarySubgroup (binaryParameters n hn) = ⊤ :=
  elementarySubgroup_eq_top_of_lifts n hn (InputRealization.inputs _ rfl)
    (elementary_lift_fixed_index _ rfl)

/-- The elementary fixed-point subgroup is the full fixed group in characteristic two. -/
theorem elementarySubgroup_eq_top (P : Parameters) (hp : P.prime = 2) :
    elementarySubgroup P = ⊤ := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact elementarySubgroup_eq_top_binary n hn

/-- The original elementary inclusion onto the full graph-field fixed group. -/
def elementaryFixedEquiv (P : Parameters) (hp : P.prime = 2) :
    ElementaryGroup P ≃* fixedSubgroup P :=
  MulEquiv.ofBijective (elementarySubgroup P).subtype
    ⟨Subtype.val_injective, fun g => ⟨⟨g, (elementarySubgroup_eq_top P hp).ge trivial⟩, rfl⟩⟩

/-- The original central quotient identifies with the actual graph-field fixed group. -/
def carrierFixedEquiv (P : Parameters) (hp : P.prime = 2) :
    Carrier P ≃* fixedSubgroup P :=
  (MulEquiv.ofBijective (toCarrier P)
    ⟨ElementaryCentralKernel.toCarrier_injective P hp, toCarrier_surjective P⟩).symm.trans
      (elementaryFixedEquiv P hp)

@[simp] theorem carrierFixedEquiv_toCarrier (P : Parameters) (hp : P.prime = 2)
    (g : ElementaryGroup P) : carrierFixedEquiv P hp (toCarrier P g) = g.val := by
  exact congrArg (elementaryFixedEquiv P hp)
    ((MulEquiv.ofBijective (toCarrier P)
      ⟨ElementaryCentralKernel.toCarrier_injective P hp, toCarrier_surjective P⟩).symm_apply_apply g)


/-- The faithful map from the original carrier into the literal split matrices. -/
def carrierToSplit (P : Parameters) (hp : P.prime = 2) : Carrier P →* SplitGroup P :=
  (fixedSubgroup P).subtype.comp (carrierFixedEquiv P hp).toMonoidHom

@[simp] theorem carrierToSplit_toCarrier (P : Parameters) (hp : P.prime = 2)
    (g : ElementaryGroup P) : carrierToSplit P hp (toCarrier P g) = elementaryInclusion P g :=
  congrArg Subtype.val (carrierFixedEquiv_toCarrier P hp g)

theorem carrierToSplit_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (carrierToSplit P hp) :=
  Subtype.val_injective.comp (carrierFixedEquiv P hp).injective

theorem carrierToSplit_mem_fixed (P : Parameters) (hp : P.prime = 2) (g : Carrier P) :
    carrierToSplit P hp g ∈ fixedSubgroup P := (carrierFixedEquiv P hp g).property

theorem exists_carrier_of_fixed (P : Parameters) (hp : P.prime = 2)
    (x : SplitGroup P) (hx : x ∈ fixedSubgroup P) :
    ∃ g : Carrier P, carrierToSplit P hp g = x :=
  ⟨(carrierFixedEquiv P hp).symm ⟨x, hx⟩,
    congrArg Subtype.val ((carrierFixedEquiv P hp).apply_symm_apply ⟨x, hx⟩)⟩

theorem mem_descend_iff (P : Parameters) (hp : P.prime = 2)
    (H : Subgroup (SplitGroup P)) (g : Carrier P) :
    g ∈ descendSubgroup P H ↔ carrierToSplit P hp g ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (congrArg (fun z : SplitGroup P => z ∈ H)
      (carrierToSplit_toCarrier P hp x)).mpr hx
  · obtain ⟨x, rfl⟩ := toCarrier_surjective P g
    intro hx
    exact ⟨x, (congrArg (fun z : SplitGroup P => z ∈ H)
      (carrierToSplit_toCarrier P hp x)).mp hx, rfl⟩

@[simp] theorem carrierToSplit_representative (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) :
    carrierToSplit P hp (weylRepresentative P hp w) = splitRepresentative P hp w :=
  carrierToSplit_toCarrier P hp (weylElementary P hp w)

section Binary
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
local notation "D" => InputRealization.inputs P rfl

/-- The proved fixed normal form parametrizes the original central-quotient carrier. -/
def carrierNormalFormEquiv :
    {c : SplitNormalForm.Coordinates P // SplitNormalForm.twist D c = c} ≃ Carrier P :=
  (SplitNormalForm.fixedNormalFormEquiv n hn D).trans
    (carrierFixedEquiv P rfl).symm.toEquiv

@[simp] theorem carrierToSplit_normalForm
    (c : {c : SplitNormalForm.Coordinates P // SplitNormalForm.twist D c = c}) :
    carrierToSplit P rfl (carrierNormalFormEquiv n hn c) = SplitNormalForm.evaluate D c.val :=
  congrArg Subtype.val ((carrierFixedEquiv P rfl).apply_symm_apply _)

/-- Intersecting a split cell with the actual fixed matrices gives exactly the
carrier cell. Uniqueness forces both Borel factors to be fixed. -/
theorem mem_cell_iff_split (w : DihedralGroup 6) (g : Carrier P) :
    g ∈ cell P rfl w ↔
      carrierToSplit P rfl g ∈ SplitNormalForm.cell D (rootRepresentative w) := by
  constructor
  · intro hg
    obtain ⟨b, hb, c, hc, rfl⟩ := (mem_cell_iff P rfl w g).mp hg
    refine ⟨carrierToSplit P rfl b, (mem_descend_iff P rfl _ b).mp hb,
      carrierToSplit P rfl c, (mem_descend_iff P rfl _ c).mp hc, ?_⟩
    simp only [map_mul, carrierToSplit_representative P rfl w, lift_rootRepresentative P rfl w]
  · intro hg
    obtain ⟨c, hc, _⟩ := SplitNormalForm.existsUnique_coordinates n hn D (carrierToSplit P rfl g)
    have hf := (SplitNormalForm.evaluate_mem_fixed_iff n hn D c).mp
      (hc.symm ▸ carrierToSplit_mem_fixed P rfl g)
    have hw : c.weyl = rootRepresentative w :=
      (SplitNormalForm.evaluate_mem_cell_iff n hn D c _).mp (hc.symm ▸ hg)
    have hv : PositiveCoordinates.orderedProduct P c.right ∈ positiveSubgroup P :=
      (PositiveCoordinates.range_orderedProduct_binary n hn).le ⟨c.right, rfl⟩
    have hvf := (PositiveCoordinates.orderedProduct_mem_fixedSubgroup_iff_binary n hn c.right).mpr
      hf.2.2.2
    obtain ⟨b, hb⟩ := exists_carrier_of_fixed P rfl (c.left.val * c.torus.val)
      ((fixedSubgroup P).mul_mem hf.1 hf.2.1)
    obtain ⟨v, hv'⟩ := exists_carrier_of_fixed P rfl
      (PositiveCoordinates.orderedProduct P c.right) hvf
    apply (mem_cell_iff P rfl w g).mpr
    refine ⟨b, (mem_descend_iff P rfl _ b).mpr ?_,
      v, (mem_descend_iff P rfl _ v).mpr ?_, ?_⟩
    · exact hb.symm ▸ (splitBorel P).mul_mem
        (Subgroup.mem_sup_left c.left.property) (Subgroup.mem_sup_right c.torus.property)
    · exact hv'.symm ▸ Subgroup.mem_sup_left hv
    · apply carrierToSplit_injective P rfl
      have hword : (D).lift c.weyl = splitRepresentative P rfl w :=
        (congrArg (D).lift hw).trans (lift_rootRepresentative P rfl w)
      calc
        carrierToSplit P rfl g = c.left.val * c.torus.val * (D).lift c.weyl *
            PositiveCoordinates.orderedProduct P c.right := hc.symm
        _ = carrierToSplit P rfl b * splitRepresentative P rfl w * carrierToSplit P rfl v :=
          congrArg₂ (· * ·) (congrArg₂ (· * ·) hb.symm hword) hv'.symm
        _ = _ := by simp only [map_mul, carrierToSplit_representative P rfl w]

/-- The twelve actual relative cells cover the carrier. -/
theorem exists_mem_cell (g : Carrier P) : ∃ w : DihedralGroup 6, g ∈ cell P rfl w := by
  obtain ⟨c, hc, _⟩ := SplitNormalForm.existsUnique_coordinates n hn D (carrierToSplit P rfl g)
  have hf := (SplitNormalForm.evaluate_mem_fixed_iff n hn D c).mp
    (hc.symm ▸ carrierToSplit_mem_fixed P rfl g)
  obtain ⟨w, hw⟩ := fixed_index P rfl c.weyl hf.2.2.1
  refine ⟨w, (mem_cell_iff_split n hn w g).mpr ?_⟩
  have h := SplitNormalForm.evaluate_mem_cell n hn D c
  exact (congrArg₂ (fun x v => x ∈ SplitNormalForm.cell D v) hc hw.symm).mp h

/-- Different published relative words label disjoint carrier cells. -/
theorem cell_index_unique {v w : DihedralGroup 6} {g : Carrier P}
    (hv : g ∈ cell P rfl v) (hw : g ∈ cell P rfl w) : v = w :=
  rootRepresentative_injective (SplitNormalForm.cell_index_unique n hn D
    ((mem_cell_iff_split n hn v g).mp hv) ((mem_cell_iff_split n hn w g).mp hw))

/-- Coverage and index uniqueness refer to the original carrier double cosets. -/
theorem existsUnique_mem_cell (g : Carrier P) : ∃! w : DihedralGroup 6, g ∈ cell P rfl w := by
  obtain ⟨w, hw⟩ := exists_mem_cell n hn g
  exact ⟨w, hw, fun v hv => cell_index_unique n hn hv hw⟩

/-- The original root parabolic reads off the marked split Weyl subgroup. -/
theorem mem_parabolic_iff_of_mem_cell (a : Node) {w : DihedralGroup 6} {g : Carrier P}
    (hg : g ∈ cell P rfl w) :
    g ∈ parabolic P a ↔ rootRepresentative w ∈ SplitNormalForm.parabolicWeyl a :=
  (mem_descend_iff P rfl (splitParabolic P a) g).trans
    (SplitNormalForm.mem_splitParabolic_iff_of_mem_cell n hn D a
      ((mem_cell_iff_split n hn w g).mp hg))

/-- Cell coverage inside a root parabolic retains its original root support. -/
theorem mem_parabolic_iff_exists_cell (a : Node) (g : Carrier P) :
    g ∈ parabolic P a ↔ ∃ w : DihedralGroup 6,
      rootRepresentative w ∈ SplitNormalForm.parabolicWeyl a ∧ g ∈ cell P rfl w := by
  constructor
  · intro hg
    obtain ⟨w, hw⟩ := exists_mem_cell n hn g
    exact ⟨w, (mem_parabolic_iff_of_mem_cell n hn a hw).mp hg, hw⟩
  · rintro ⟨w, hw, hg⟩
    exact (mem_parabolic_iff_of_mem_cell n hn a hg).mpr hw

end Binary
end Triality.Standard.ConcreteBruhat.FixedDescent
