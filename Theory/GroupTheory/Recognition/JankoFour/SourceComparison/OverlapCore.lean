module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.ToddCorrection
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology.Original
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The original cubic and the Todd correction on I/(Q A)

Coprime decomposition and the extraspecial Frattini subgroup prove
[Q,A]=Q. The normal cubic lift Q A meets the intrinsic two-core of I in Q,
so [O2(I),A]=Q. Consequently every automorphism preserving the specified
cubic also preserves the original extraspecial core.

Apply the odd-word averaging construction to that same cubic inside M.
The resulting outer Todd correction on I fixes A, preserves Q and the full
Q A, and descends to an involutory automorphism of the literal quotient.
The restriction equation keeps every ambient embedding and quotient map.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This supplies the actual descending correction. Its noninnerness modulo
Q A and the remaining automorphism kernel calculation are not asserted.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- The original cubic acts onto the whole extraspecial core by commutators. -/
theorem core_eq_cubic_commutator :
    ⁅core z,cubicSylowImage a.e a.X⁆ = core z := by
  let := h.extraspecial
  let : Group.IsNilpotent (core z) := (IsExtraspecial.isPGroup 2 (core z)).isNilpotent
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime
    (core z) (cubicSylowImage a.e a.X) (by rw [(core z).normalizer_eq_top]; exact le_top)
    inferInstance (by rw [cubicSylowImage_card h a.e a.X,h.core_card]; norm_num)
  have hz : core z ⊓ Subgroup.centralizer (cubicSylowImage a.e a.X : Set (centralizer z)) =
      (frattini (core z)).map (core z).subtype := by
    rw [IsExtraspecial.frattini_eq_center (p := 2),←core_cubic_centralizer h a.e a.X,
      subgroupOf_map_subtype,inf_comm]
  rw [hz] at hd
  have hc : ⁅core z,cubicSylowImage a.e a.X⁆ ≤ core z := commutator_le_left _ _
  have ht : (⁅core z,cubicSylowImage a.e a.X⁆.subgroupOf (core z)) ⊔
      frattini (core z) = ⊤ := by
    apply Subgroup.map_injective (core z).subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hc,←hd,←MonoidHom.range_eq_map,range_subtype]
  have he := congrArg (Subgroup.map (core z).subtype) (frattini_nongenerating ht)
  rwa [map_subgroupOf_eq_of_le hc,←MonoidHom.range_eq_map,range_subtype] at he

/-- The same whole cubic lift lies in the original plane overlap. -/
theorem overlap_cubicLift_le : twoThreeCore (centralizer z) ≤ a.P.M.subgroupOf (centralizer z) :=
  twoThreeCore_le_overlap a.P.cubic _ _ a.P.overlap h

/-- Q is recovered from the intrinsic two-core of I and the specified cubic.
This is useful before an arbitrary automorphism of I has been normalized. -/
theorem overlap_core_eq_commutator :
    ⁅pCore 2 (a.P.M.subgroupOf (centralizer z)),
      (cubicSylowImage a.e a.X).subgroupOf (a.P.M.subgroupOf (centralizer z))⁆ =
        (core z).subgroupOf (a.P.M.subgroupOf (centralizer z)) := by
  let I := a.P.M.subgroupOf (centralizer z)
  let K := twoThreeCore (centralizer z)
  let Q := (core z).subgroupOf I
  let A := (cubicSylowImage a.e a.X).subgroupOf I
  have hKI : K ≤ I := overlap_cubicLift_le a
  have hQK : core z ≤ K := core_le_twoThreeCore h
  have hQI := hQK.trans hKI
  have hAK : cubicSylowImage a.e a.X ≤ K := by
    change cubicSylowImage a.e a.X ≤ twoThreeCore (centralizer z)
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  have hAI := hAK.trans hKI
  have hQ : Q ≤ pCore 2 I :=
    le_sSup ⟨inferInstance,(IsPGroup.of_card (p := 2) (n := 13) h.core_card).comap_subtype⟩
  have hQA : ⁅Q,A⁆ = Q := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hQI,map_subgroupOf_eq_of_le hAI,
      core_eq_cubic_commutator a]
  apply le_antisymm
  · intro x hx
    have hs : x ∈ pCore 2 I := commutator_le_left _ _ hx
    have hk : x ∈ K.subgroupOf I := by
      apply (commutator_mono le_top (show A ≤ K.subgroupOf I from fun _ hx => hAK hx)).trans
        (commutator_le_right _ _) hx
    let y : K.subgroupOf I := ⟨x,hk⟩
    have hy : y ∈ pCore 2 (K.subgroupOf I) := by
      rw [←(inferInstance : (K.subgroupOf I).Normal).isSubnormal.pCore_subgroupOf 2]
      exact hs
    let e : K.subgroupOf I ≃* K := subgroupOfEquivOfLe hKI
    have he : e y ∈ pCore 2 K := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hy
    rw [twoCore_twoThreeCore h] at he
    exact he
  · change Q ≤ ⁅pCore 2 I,A⁆
    rw [←hQA]
    exact commutator_mono hQ le_rfl

/-- Once the original cubic is preserved, its whole core is preserved as well. -/
theorem overlap_automorphism_core (f : MulAut (a.P.M.subgroupOf (centralizer z)))
    (hf : ((cubicSylowImage a.e a.X).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
      f.toMonoidHom = (cubicSylowImage a.e a.X).subgroupOf (a.P.M.subgroupOf (centralizer z))) :
    ((core z).subgroupOf (a.P.M.subgroupOf (centralizer z))).map f.toMonoidHom =
      (core z).subgroupOf (a.P.M.subgroupOf (centralizer z)) := by
  rw [←overlap_core_eq_commutator a,map_commutator,pCore_map_iso,hf]

/-- The point and plane descriptions of I use the same ambient elements. -/
noncomputable def overlapPlacement : pointOverlap a ≃* a.P.M.subgroupOf (centralizer z) where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual Todd correction, now on the plane-side overlap. -/
noncomputable def planeOverlapToddTwist (w : Full) :
    MulAut (a.P.M.subgroupOf (centralizer z)) :=
  MulAut.congr (overlapPlacement a) (overlapToddTwist a w)

theorem planeOverlapToddTwist_coe (w : Full) (x : a.P.M.subgroupOf (centralizer z)) :
    (planeOverlapToddTwist a w x).val.val =
      (pointTwist a w ⟨x.val.val,x.property⟩).val := rfl

theorem planeOverlapToddTwist_not_inner (w : Full) (hw : w ∉ Core) :
    ¬ ∃ x : a.P.M.subgroupOf (centralizer z), planeOverlapToddTwist a w = MulAut.conj x := by
  rintro ⟨x,hx⟩
  apply hw
  apply (overlapToddTwist_inner_iff a w).mp
  refine ⟨(overlapPlacement a).symm x,?_⟩
  apply (MulAut.congr (overlapPlacement a)).injective
  rw [MulAut.congr_conj,MulEquiv.apply_symm_apply]
  exact hx

/-- The chosen cubic inside M, retaining its original embedding from H. -/
noncomputable def pointCubic : Subgroup a.P.M :=
  ((cubicSylowImage a.e a.X).map (centralizer z).subtype).subgroupOf a.P.M

private theorem cubic_le_overlap :
    cubicSylowImage a.e a.X ≤ a.P.M.subgroupOf (centralizer z) := by
  apply le_trans ?_ (overlap_cubicLift_le a)
  rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
  exact le_sup_right

theorem pointCubic_card : Nat.card (pointCubic a) = 3 := by
  have hl : (cubicSylowImage a.e a.X).map (centralizer z).subtype ≤ a.P.M := by
    rintro _ ⟨x,hx,rfl⟩
    exact cubic_le_overlap a hx
  rw [pointCubic,Nat.card_congr (subgroupOfEquivOfLe hl).toEquiv,
    card_map_of_injective (centralizer z).subtype_injective,cubicSylowImage_card h a.e a.X]

/-- Fixing the selected cubic pointwise preserves Q and the full Q A kernel. -/
theorem planeOverlapToddTwist_kernels (w : Full)
    (hf : ∀ y : pointCubic a, pointTwist a w y.val = y.val) :
    ((core z).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
        (planeOverlapToddTwist a w).toMonoidHom =
      (core z).subgroupOf (a.P.M.subgroupOf (centralizer z)) ∧
    ((twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
        (planeOverlapToddTwist a w).toMonoidHom =
      (twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z)) := by
  let I := a.P.M.subgroupOf (centralizer z)
  let f := planeOverlapToddTwist a w
  have ha (x : I) (hx : x ∈ (cubicSylowImage a.e a.X).subgroupOf I) : f x = x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [planeOverlapToddTwist_coe]
    exact congrArg Subtype.val (hf ⟨⟨x.val.val,x.property⟩,⟨x.val,hx,rfl⟩⟩)
  have hA : ((cubicSylowImage a.e a.X).subgroupOf I).map f.toMonoidHom =
      (cubicSylowImage a.e a.X).subgroupOf I := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change f y ∈ (cubicSylowImage a.e a.X).subgroupOf I
      rw [ha y hy]
      exact hy
    · intro hx
      exact ⟨x,hx,ha x hx⟩
  have hQ := overlap_automorphism_core a f hA
  refine ⟨hQ,?_⟩
  have hsum : (twoThreeCore (centralizer z)).subgroupOf I =
      (core z).subgroupOf I ⊔ (cubicSylowImage a.e a.X).subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (overlap_cubicLift_le a),Subgroup.map_sup,
      map_subgroupOf_eq_of_le ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)),
      map_subgroupOf_eq_of_le (cubic_le_overlap a),core_sup_cubicSylow a.e h a.X,
      cubicLift_eq_twoThreeCore h a.e]
  rw [hsum,Subgroup.map_sup,hQ,hA]

/-- A constructed outer correction on I fixing the original cubic and
preserving both literal quotient kernels. -/
theorem exists_cubic_fixed_todd_correction :
    ∃ w : Full, w ∉ Core ∧
      (∀ y : pointCubic a, pointTwist a w y.val = y.val) ∧
      (¬ ∃ x : a.P.M.subgroupOf (centralizer z), planeOverlapToddTwist a w = MulAut.conj x) ∧
      ((core z).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
          (planeOverlapToddTwist a w).toMonoidHom =
        (core z).subgroupOf (a.P.M.subgroupOf (centralizer z)) ∧
      ((twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
          (planeOverlapToddTwist a w).toMonoidHom =
        (twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z)) := by
  obtain ⟨w,hw,hfix⟩ := exists_odd_fixed_word a (pointCubic a) (by rw [pointCubic_card]; decide)
  have hf (y : pointCubic a) := pointTwist_fixes_of_fixed_word a w y.val (hfix y)
  exact ⟨w,hw,hf,planeOverlapToddTwist_not_inner a w hw,planeOverlapToddTwist_kernels a w hf⟩

/-- The word is chosen by the proved averaging construction for the SAME cubic. -/
noncomputable def cubicFixedWord : Full := (exists_cubic_fixed_todd_correction a).choose

theorem cubicFixedWord_odd : cubicFixedWord a ∉ Core :=
  (exists_cubic_fixed_todd_correction a).choose_spec.1

theorem cubicFixedWord_fixes : ∀ y : pointCubic a,
    pointTwist a (cubicFixedWord a) y.val = y.val :=
  (exists_cubic_fixed_todd_correction a).choose_spec.2.1

/-- Descend the constructed original correction through the full Q A,
retaining the scalar cubic and the original marked quotient map. -/
noncomputable def cubicToddQuotientTwist : MulAut (OverlapCohomology.Original a.P) :=
  QuotientGroup.congr _ _ (planeOverlapToddTwist a (cubicFixedWord a))
    (planeOverlapToddTwist_kernels a _ (cubicFixedWord_fixes a)).2

theorem cubicToddQuotientTwist_mk (x : a.P.M.subgroupOf (centralizer z)) :
    cubicToddQuotientTwist a (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (planeOverlapToddTwist a (cubicFixedWord a) x) := rfl

theorem planeOverlapToddTwist_sq (w : Full) : planeOverlapToddTwist a w ^ 2 = 1 := by
  have ho : overlapToddTwist a w ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change pointTwist a w (pointTwist a w x.val) = x.val
    exact MulEquiv.congr_fun (pointTwist_sq a w) x.val
  change MulAut.congr (overlapPlacement a) (overlapToddTwist a w) ^ 2 = 1
  rw [←map_pow,ho,map_one]

theorem cubicToddQuotientTwist_sq : cubicToddQuotientTwist a ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change cubicToddQuotientTwist a (cubicToddQuotientTwist a (QuotientGroup.mk' _ x)) =
      QuotientGroup.mk' _ x
    rw [cubicToddQuotientTwist_mk,cubicToddQuotientTwist_mk]
    exact congrArg (QuotientGroup.mk' _) (MulEquiv.congr_fun
      (planeOverlapToddTwist_sq a (cubicFixedWord a)) x)

/-- The marked original cubic, the core and scalar kernel all survive the
constructed Todd correction. Outer restriction is asserted on I; outer
restriction on I/(Q A) remains the separate module-comparison step. -/
theorem cubic_todd_correction :
    (¬ ∃ x : a.P.M.subgroupOf (centralizer z),
      planeOverlapToddTwist a (cubicFixedWord a) = MulAut.conj x) ∧
    (∀ y : pointCubic a, pointTwist a (cubicFixedWord a) y.val = y.val) ∧
    ((core z).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
        (planeOverlapToddTwist a (cubicFixedWord a)).toMonoidHom =
      (core z).subgroupOf (a.P.M.subgroupOf (centralizer z)) ∧
    ((twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z))).map
        (planeOverlapToddTwist a (cubicFixedWord a)).toMonoidHom =
      (twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z)) ∧
    cubicToddQuotientTwist a ^ 2 = 1 ∧
    (∀ x : a.P.M.subgroupOf (centralizer z),
      cubicToddQuotientTwist a (QuotientGroup.mk' _ x) =
        QuotientGroup.mk' _ (planeOverlapToddTwist a (cubicFixedWord a) x)) :=
  ⟨planeOverlapToddTwist_not_inner a _ (cubicFixedWord_odd a),cubicFixedWord_fixes a,
    (planeOverlapToddTwist_kernels a _ (cubicFixedWord_fixes a)).1,
    (planeOverlapToddTwist_kernels a _ (cubicFixedWord_fixes a)).2,
    cubicToddQuotientTwist_sq a,cubicToddQuotientTwist_mk a⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
