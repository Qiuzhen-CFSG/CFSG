module

public import Theory.SpecificGroups.J2HSMultipliers.HSDoubleCover.Involution
public import Theory.Alternating.proposition_5_2_4
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelCard

/-!
# A genuine perfect central double cover of Higman–Sims

Pull back the established Schur double cover of A₁₀₀ along the literal
ATLAS degree-100 action. The kernel consists of the identity and the
nonidentity central sign. The checked HS word `(a * b²)⁵` is a product of
50 disjoint transpositions. Conjugacy in A₁₀₀ and the canonical lift-square
formula show that it has a lift whose square is the nonidentity sign.
The square obstruction then proves the pullback perfect.

The only base-group assumption is perfectness of the actual HS carrier;
the independent model comparison supplies this in the parent assembly.
The kernel is identified as a group, and its order divides the kernel order
of every chosen universal cover through a commuting triangle with the
literal projection. The constructed double cover is not assumed universal.
The independent upper bound remains with the parent multiplier calculation.

Source: Aschbacher–Smith, I.1.1 and the HS row of I.1.3(1), printed p.407
(PDF p.418), combined manuscript of 1 March 2004. The alternating lift-square
calculation is GLS3 Proposition 5.2.4(e), in the imported source development.
The ATLAS action attribution is retained in the involution certificate.
-/

public section

namespace Theory.SpecificGroups.J2HSMultipliers.HS
open Sporadic.LeechRelated.HS
open GLS3.Chapter5.SchurPresentation
open PerfectCentralCovering Subgroup

universe u

section PerfectBase
variable [Group.IsPerfect Carrier]

/-- The faithful degree-100 action, landing in A₁₀₀ because HS is perfect. -/
@[expose] def alternatingInclusion : Carrier →* alternatingGroup (Fin 100) :=
  inclusion.codRestrict _ fun x => by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp inclusion)
      (Group.IsPerfect.mem_commutator (g := x))

theorem alternatingInclusion_injective : Function.Injective alternatingInclusion := by
  intro x y h
  exact Sporadic.LeechRelated.HS.inclusion_injective
    (congrArg (fun t : alternatingGroup (Fin 100) => t.val) h)

/-- The literal pullback of the Schur double cover of A₁₀₀ along the HS action. -/
@[expose] def pullback : Subgroup (SchurAlternatingGroup 95 × Carrier) :=
  ((schurAlternatingProjection 95).comp (MonoidHom.fst _ _)).eqLocus
    (alternatingInclusion.comp (MonoidHom.snd _ _))

/-- The concrete finite central double extension of the degree-100 HS carrier. -/
abbrev DoubleCover := pullback

/-- Finiteness is inherited from the alternating double cover and the actual HS carrier. -/
instance doubleCover_finite : Finite DoubleCover := inferInstanceAs (Finite pullback)

/-- The second projection, with codomain the original permutation carrier. -/
@[expose] def projection : DoubleCover →* Carrier :=
  (MonoidHom.snd _ _).comp pullback.subtype

/-- The first projection into the established alternating double cover. -/
@[expose] def toAlternatingCover : DoubleCover →* SchurAlternatingGroup 95 :=
  (MonoidHom.fst _ _).comp pullback.subtype

/-- The defining triangle retains both literal projections. -/
theorem projection_square :
    (schurAlternatingProjection 95).comp toAlternatingCover =
      alternatingInclusion.comp projection := by
  apply MonoidHom.ext
  intro x
  exact x.property

theorem projection_surjective : Function.Surjective projection := by
  intro b
  obtain ⟨a, ha⟩ := schurAlternatingProjection_surjective 95 (alternatingInclusion b)
  exact ⟨⟨(a, b), ha⟩, rfl⟩

/-- The nonidentity sign of the alternating cover, paired with the identity of HS. -/
@[expose] def centralSign : DoubleCover :=
  ⟨(schurAlternatingCentral 95, 1), by
    change schurAlternatingProjection 95 (schurAlternatingCentral 95) =
      alternatingInclusion 1
    rw [map_one]
    exact MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker 95)⟩

theorem centralSign_ne_one : centralSign ≠ 1 := by
  intro h
  exact schurAlternatingCentral_ne_one 95
    (congrArg (fun x : DoubleCover => x.val.1) h)

theorem centralSign_sq : centralSign ^ 2 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact schurAlternatingCentral_sq 95
  · exact one_pow 2

theorem centralSign_mem_center : centralSign ∈ center DoubleCover := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact mem_center_iff.mp (schurAlternatingCentral_mem_center 95) x.val.1
  · exact (mul_one x.val.2).trans (one_mul x.val.2).symm

/-- The projection kernel consists of exactly the two displayed elements. -/
theorem projection_ker (x : DoubleCover) :
    x ∈ projection.ker ↔ x = 1 ∨ x = centralSign := by
  constructor
  · intro hx
    have hb : x.val.2 = 1 := hx
    have ha : x.val.1 ∈ (schurAlternatingProjection 95).ker := by
      change schurAlternatingProjection 95 x.val.1 = 1
      calc
        _ = alternatingInclusion x.val.2 := x.property
        _ = 1 := by rw [hb, map_one]
    rcases InvolutionPreimage.ker_mem_cases 95 ha with ha | ha
    · exact Or.inl (Subtype.ext (Prod.ext ha hb))
    · exact Or.inr (Subtype.ext (Prod.ext ha hb))
  · rintro (rfl | rfl)
    · exact projection.ker.one_mem
    · rfl

theorem projection_ker_le_center : projection.ker ≤ center DoubleCover := by
  intro x hx
  rcases (projection_ker x).mp hx with rfl | rfl
  · exact (center DoubleCover).one_mem
  · exact centralSign_mem_center

/-- The fixed-point-free involution has a lift squaring to the nonidentity sign.
It is conjugate in A₁₀₀ to the canonical product of 25 four-point blocks. -/
theorem exists_alternating_lift_square :
    ∃ x : SchurAlternatingGroup 95,
      schurAlternatingProjection 95 x = alternatingInclusion involution ∧
      x ^ 2 = schurAlternatingCentral 95 := by
  obtain ⟨x, hx⟩ := schurAlternatingProjection_surjective 95
    (alternatingInclusion involution)
  refine ⟨x, hx, ?_⟩
  let y := canonicalLift 95 25 (by decide)
  have hy2 : schurAlternatingProjection 95 y ^ 2 = 1 := by
    rw [← canonicalLift_proj_order_two 95 25 (by decide) (by decide)]
    exact pow_orderOf_eq_one _
  have hc : IsConj (schurAlternatingProjection 95 y)
      (alternatingInclusion involution) := by
    apply alternating_involution_isConj_of_card_support_eq
    · change ((alternatingGroup (Fin 100)).subtype
        (schurAlternatingProjection 95 y)) ^ 2 = 1
      rw [← map_pow, hy2, map_one]
    · change (Sporadic.LeechRelated.HS.inclusion involution) ^ 2 = 1
      rw [← map_pow, involution_square, map_one]
    · intro h
      apply canonicalPerm_ne_one 95 25 (by decide) (by decide)
      exact (canonicalLift_proj 95 25 (by decide)).symm.trans
        (congrArg Subtype.val h)
    · change (schurAlternatingProjection 95 y).val.support.card =
        (involution : Equiv.Perm (Fin 100)).support.card
      rw [canonicalLift_proj, canonicalPerm_support_card, involution_support_card]
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hs := DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
    (schurAlternatingCovering 95) (natCard_ker_schurAlternatingCovering 95)
    (x := y) (y := x) (c := c) hy2 (by
      change c * schurAlternatingProjection 95 y * c⁻¹ = schurAlternatingProjection 95 x
      rw [hx]
      exact hc)
  change canonicalLift 95 25 _ ^ 2 = x ^ 2 at hs
  rw [canonicalLift_sq, central_pow_of_odd 95 (by decide : Odd 25)] at hs
  exact hs.symm

/-- A lift of the actual HS involution in the literal pullback. -/
noncomputable def markedLift : DoubleCover :=
  ⟨(Classical.choose exists_alternating_lift_square, involution),
    (Classical.choose_spec exists_alternating_lift_square).1⟩

theorem markedLift_projection : projection markedLift = involution := by
  unfold projection markedLift
  rfl

theorem markedLift_sq : markedLift ^ 2 = centralSign := by
  apply Subtype.ext
  exact Prod.ext (Classical.choose_spec exists_alternating_lift_square).2 involution_square

/-- The genuine central square forces this double extension to be perfect. -/
instance doubleCover_perfect : Group.IsPerfect DoubleCover :=
  isPerfect_of_central_binary_kernel_of_square projection projection_surjective
    projection_ker_le_center centralSign centralSign_sq
    (fun k hk => (projection_ker k).mp hk) markedLift markedLift_sq

/-- The finite perfect central cover of the original HS permutation carrier. -/
@[expose] def cover : Cover DoubleCover Carrier where
  toMonoidHom := projection
  surjective := projection_surjective
  isPerfect := inferInstance
  ker_le_center := projection_ker_le_center

/-- The cardinality of the kernel of the literal projection. -/
theorem kernel_card : Nat.card projection.ker = 2 := by
  rw [Nat.card_eq_two_iff' (1 : projection.ker)]
  refine ⟨⟨centralSign, rfl⟩, ?_, ?_⟩
  · intro h
    exact centralSign_ne_one (congrArg Subtype.val h)
  · intro y hy
    apply Subtype.ext
    exact ((projection_ker y.val).mp y.property).resolve_left
      (fun h => hy (Subtype.ext h))

/-- A multiplicative equivalence from the actual kernel to the cyclic group of order two. -/
noncomputable def kernelEquivTwo : projection.ker ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq kernel_card (by simp)

/-- Every chosen universal perfect central cover has kernel order divisible by two.
Universality is assumed only for `f`, never for the constructed double cover. -/
theorem two_dvd_universal_kernel
    {U : Type u} [Group U] [Finite U]
    (f : Cover U Carrier) (hf : PerfectCentralCovering.IsUniversal.{u,0,0} f) :
    2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨a, ha, _⟩ := hf DoubleCover cover
  have hs : Function.Surjective a :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      projection a (ha ▸ f.surjective) projection_ker_le_center
  have h := Theory.GroupTheory.kernel_card_dvd_of_surjective_factor
    f.toMonoidHom projection a hs ha
  rwa [kernel_card] at h

/-- The lower bound for the concrete free-central universal projection. -/
theorem two_dvd_canonical_universal_kernel :
    2 ∣ Nat.card (universalProjection Carrier).ker :=
  two_dvd_universal_kernel (universalCover Carrier) universalCover_isUniversal

/-- The canonical multiplier has at least two elements. -/
theorem two_le_canonical_universal_kernel :
    2 ≤ Nat.card (universalProjection Carrier).ker :=
  Nat.le_of_dvd Nat.card_pos two_dvd_canonical_universal_kernel

end PerfectBase

/-- The same cover is quasisimple whenever the base is quasisimple. -/
instance doubleCover_isQuasisimple [Theory.GroupTheory.IsQuasisimple Carrier] :
    Theory.GroupTheory.IsQuasisimple DoubleCover := cover.isQuasisimple

/-- The identical projection in the quasisimple covering interface. -/
@[expose] def quasisimpleCover [Theory.GroupTheory.IsQuasisimple Carrier] :
    Theory.GroupTheory.Covering DoubleCover Carrier := cover.toCovering

/-- Consumer adapter for the parent multiplier calculation using quasisimple covers. -/
theorem two_dvd_quasisimple_universal_kernel
    [Theory.GroupTheory.IsQuasisimple Carrier]
    {U : Type u} [Group U] [Finite U] [Theory.GroupTheory.IsQuasisimple U]
    (f : Theory.GroupTheory.Covering U Carrier)
    (hf : Theory.GroupTheory.Covering.IsUniversal.{0,u,0} f) :
    2 ∣ Nat.card f.toMonoidHom.ker := by
  have h := Theory.GroupTheory.kernel_card_dvd_of_surjective_factor
    f.toMonoidHom quasisimpleCover.toMonoidHom
    (hf.lift quasisimpleCover).toMonoidHom (hf.lift quasisimpleCover).surjective
    (congrArg Theory.GroupTheory.Covering.toMonoidHom (hf.lift_fac quasisimpleCover))
  rwa [show Nat.card quasisimpleCover.toMonoidHom.ker = 2 from kernel_card] at h

end Theory.SpecificGroups.J2HSMultipliers.HS
