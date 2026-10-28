module
public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.LeviStructure.CharacterFunctional
public import Theory.AlgebraicGroup.RootSubgroups.PositiveContraction
public import Theory.AlgebraicGroup.Unipotent.Contraction.OppositeSeparation
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Reductive.Defs

/-!
# Standard Levi separation by cocharacters

The integral functional summing simple-root coordinates outside J produces an
actual algebraic cocharacter. Its inverse conjugation contracts the unipotent
factor and fixes the torus and Levi root groups. A point which is both
contracted and fixed is one, proving disjointness without a reductivity premise
on the Levi. Pointwise U L factorization then identifies the cocharacter's
centralizer inside P with the actual constructed Levi.

Ambient containment of the cocharacter centralizer in P is still required for
the ambient centralizer identification. With that containment and the earlier
universal toral-radical theorem for connected subtorus centralizers, the final
reduction proves Levi reductivity. The containment and full radical maximality
remain independent source obligations.

Sources: GLS3, 1.13.3(a--c); Borel, IV, 13.17 and 14.17--14.18. All contractions
use the inverse-conjugation convention of RootWeightEquation.
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

local notation "hD" => S.standardParabolic.left.right.left
local notation "hT" => S.standardParabolic.left.left.left
local notation "P" => parabolic S.D hD hT S.positiveRoots S.sigmaJ
local notation "U" => unipotent S.D hD S.positiveRoots S.sigmaJ
local notation "L" => levi S.D hD hT S.sigmaJ

private theorem root_centralizes_cocharacter
    (lambda : ClosedSubgroupTorusCocharacter S.T)
    (a : S.D.Root)
    (ha : WeightCocharacterEquation S.T (S.D.rootWeight a) lambda 0) :
    (S.D.rootSubgroup a).toSubgroup ≤
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup := by
  let X := S.D.rootSubgroup a
  let x : OneParameterParametrization X.carrierVariety :=
    Classical.choice (hD.2.2.1 a).1.2
  intro g hg
  let y := X.pointEquiv.symm ⟨g, hg⟩
  let z := x.inv.onPoints y
  let c : k := Multiplicative.toAdd (additiveGroupPointEquiv k z)
  have hc : X.includePoint (x.value c) = g := by
    change X.includePoint (x.hom.onPoints (kPlusPoint c)) = g
    rw [show kPlusPoint c = z from kPlusPoint_coordinate z]
    change X.includePoint (x.hom.onPoints (x.inv.onPoints y)) = g
    rw [x.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨g, hg⟩)
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨t, rfl⟩
  have heq := (hD.2.2.1 a).2 x c (lambda.onPoints t)
  rw [ha t, zpow_zero, one_mul, hc] at heq
  change S.T.includePoint (lambda.onPoints t) * g =
    g * S.T.includePoint (lambda.onPoints t)
  calc
    S.T.includePoint (lambda.onPoints t) * g =
        S.T.includePoint (lambda.onPoints t) *
          ((S.T.includePoint (lambda.onPoints t))⁻¹ * g *
            S.T.includePoint (lambda.onPoints t)) := congrArg _ heq.symm
    _ = _ := by group

/-- The Levi root groups and torus centralize a cocharacter with zero pairing on the Levi subsystem. -/
public theorem levi_le_cocharacter_centralizer
    (lambda : ClosedSubgroupTorusCocharacter S.T)
    (hzero : ∀ a ∈ S.sigmaJ,
      WeightCocharacterEquation S.T (S.D.rootWeight a) lambda 0) :
    (L).toSubgroup ≤
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup := by
  change S.T.toSubgroup ⊔ RootSubgroupGenerated S.D
    (S.sigmaJ ∪ S.D.neg '' S.sigmaJ) ≤ _
  refine sup_le ?_ ?_
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨t, rfl⟩
    let y := S.T.pointEquiv.symm ⟨g, hg⟩
    have hy : S.T.inclusion.onPoints y = g := rfl
    change S.T.inclusion.onPoints (lambda.onPoints t) * g =
      g * S.T.inclusion.onPoints (lambda.onPoints t)
    rw [← hy, ← map_mul, ← map_mul]
    rw [isMulCommutative_iff.mp (hT).isMulCommutative]
  · apply RootSubgroupGenerated_le_of_rootSubgroup_le
    intro a ha
    apply root_centralizes_cocharacter S lambda a
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact hzero a ha
    · have hbzero : characterCocharacterPairing S.T lambda
          (Additive.ofMul (S.D.rootWeight b)) = 0 :=
        (weightCocharacterEquation_existsUnique S.T (S.D.rootWeight b) lambda).unique
          (characterCocharacterPairing_spec S.T (S.D.rootWeight b) lambda) (hzero b hb)
      have hnegzero : characterCocharacterPairing S.T lambda
          (Additive.ofMul (S.D.rootWeight (S.D.neg b))) = 0 := by
        rw [hD.2.2.2.1 b]
        change characterCocharacterPairing S.T lambda
          (-Additive.ofMul (S.D.rootWeight b)) = 0
        rw [map_neg, hbzero, neg_zero]
      simpa only [hnegzero] using
        characterCocharacterPairing_spec S.T (S.D.rootWeight (S.D.neg b)) lambda

/-- Realize an integral separating functional by a cocharacter contracting U and centralizing L. -/
public theorem exists_levi_separating_cocharacter
    (phi : Additive (TorusWeight S.T) →+ ℤ)
    (hpos : ∀ a ∈ S.positiveRoots \ S.sigmaJ,
      0 < phi (Additive.ofMul (S.D.rootWeight a)))
    (hzero : ∀ a ∈ S.sigmaJ, phi (Additive.ofMul (S.D.rootWeight a)) = 0) :
    ∃ lambda : ClosedSubgroupTorusCocharacter S.T,
      (∀ chi, WeightCocharacterEquation S.T chi lambda (phi (Additive.ofMul chi))) ∧
      (∀ g ∈ U, IsCocharacterContracted (S.T.inclusion.comp lambda) g) ∧
      (L).toSubgroup ≤
        (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup := by
  obtain ⟨lambda, hlambda⟩ := exists_cocharacter_realizing_characterFunctional S.T hT phi
  refine ⟨lambda, hlambda, ?_, ?_⟩
  · intro g hg
    exact rootSubgroupGenerated_isCocharacterContracted S.D hD _ lambda
      (fun a => phi (Additive.ofMul (S.D.rootWeight a))) hpos
      (fun a _ => hlambda (S.D.rootWeight a)) hg
  · apply levi_le_cocharacter_centralizer S lambda
    intro a ha
    simpa only [hzero a ha] using hlambda (S.D.rootWeight a)

private theorem contracted_centralizer_eq_one
    (rho : AlgebraicGroup.Morphism (KMult k) K) {g : Variety.Point K}
    (hg : IsCocharacterContracted rho g)
    (hc : g ∈ rho.imageClosedSubgroup.centralizer) : g = 1 := by
  apply hg.eq_one_of_opposite_curve (Variety.Morphism.const _ _ g)
  intro t
  change g = rho.onPoints t * g * (rho.onPoints t)⁻¹
  have hcomm := Subgroup.mem_centralizer_iff.mp hc (rho.onPoints t) ⟨t, rfl⟩
  rw [hcomm, mul_inv_cancel_right]

/-- A separating character functional proves disjointness of the actual standard factors. -/
public theorem disjoint_of_characterFunctional
    (phi : Additive (TorusWeight S.T) →+ ℤ)
    (hpos : ∀ a ∈ S.positiveRoots \ S.sigmaJ,
      0 < phi (Additive.ofMul (S.D.rootWeight a)))
    (hzero : ∀ a ∈ S.sigmaJ, phi (Additive.ofMul (S.D.rootWeight a)) = 0) :
    Disjoint (U).toSubgroup (L).toSubgroup := by
  obtain ⟨lambda, _, hcontract, hcentral⟩ :=
    exists_levi_separating_cocharacter S phi hpos hzero
  rw [Subgroup.disjoint_def]
  intro g hgU hgL
  exact contracted_centralizer_eq_one _ (hcontract g hgU) (hcentral hgL)

/-- Inside the constructed parabolic, the cocharacter centralizer is exactly the Levi. -/
public theorem parabolic_inf_cocharacterCentralizer
    (lambda : ClosedSubgroupTorusCocharacter S.T)
    (hcontract : ∀ g ∈ U, IsCocharacterContracted (S.T.inclusion.comp lambda) g)
    (hcentral : (L).toSubgroup ≤
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup) :
    (P).toSubgroup ⊓
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup =
        (L).toSubgroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx, l, hl, rfl⟩ := (mem_parabolic_iff S g).mp hg.1
    have hxc : x ∈ (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup := by
      have h := (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup.mul_mem
        hg.2 ((S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup.inv_mem
          (hcentral hl))
      simpa only [mul_inv_cancel_right] using h
    have hxone := contracted_centralizer_eq_one _ (hcontract x hx) hxc
    change x * l ∈ L
    simpa only [hxone, one_mul] using hl
  · exact le_inf (factors_le S.D hD hT S.positiveRoots S.sigmaJ).2 hcentral

/-- Ambient centralizer containment upgrades the intersection computation to an equality of closed subgroups. -/
public theorem cocharacterCentralizer_eq_levi_of_le_parabolic
    (lambda : ClosedSubgroupTorusCocharacter S.T)
    (hcontract : ∀ g ∈ U, IsCocharacterContracted (S.T.inclusion.comp lambda) g)
    (hcentral : (L).toSubgroup ≤
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup)
    (hCP : (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer ≤ P) :
    (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer = L := by
  apply SetLike.coe_injective
  have h := parabolic_inf_cocharacterCentralizer S lambda hcontract hcentral
  rw [inf_eq_right.mpr hCP] at h
  exact congrArg (fun H : Subgroup (Variety.Point K) => (H : Set (Variety.Point K))) h

/-- The earlier universal toral-radical theorem gives reductivity once the actual ambient centralizer is contained in P. -/
public theorem levi_reductive_of_cocharacterCentralizer_containment
    (htoral : ∀ Q : ClosedSubgroup K, IsSubtorus Q →
      Variety.IsConnected Q.centralizer.carrierVariety →
      ∀ R : ClosedSubgroup Q.centralizer.carrierVariety,
        IsRadicalSubgroup R → IsSubtorus R)
    (lambda : ClosedSubgroupTorusCocharacter S.T)
    (hcontract : ∀ g ∈ U, IsCocharacterContracted (S.T.inclusion.comp lambda) g)
    (hcentral : (L).toSubgroup ≤
      (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup)
    (hCP : (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer ≤ P) :
    IsReductiveAlgebraicGroup (L).carrierVariety := by
  have hLc : Variety.IsConnected (L).carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph (L).isZariskiClosed
    let : ConnectedSpace {x : Variety.Point K // x ∈ (L : Set (Variety.Point K))} :=
      Subtype.connectedSpace (candidates_connected S.D hD hT S.positiveRoots S.sigmaJ).2.2
    let : ConnectedSpace (Variety.Point (L).carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  let Q := (S.T.inclusion.comp lambda).imageClosedSubgroup
  have hQ : IsSubtorus Q :=
    morphism_image_isTorus (S.T.inclusion.comp lambda) (dVariety_isTorus 1)
  have hQL : Q.centralizer = L :=
    cocharacterCentralizer_eq_levi_of_le_parabolic S lambda hcontract hcentral hCP
  have hQc : Variety.IsConnected Q.centralizer.carrierVariety := hQL.symm ▸ hLc
  have hred : IsReductiveAlgebraicGroup Q.centralizer.carrierVariety :=
    ⟨hQc, htoral Q hQ hQc⟩
  exact hQL ▸ hred

/-- The source setup itself supplies a separating algebraic cocharacter,
including its exact signs, contraction, and fixed Levi factor. -/
public theorem exists_standard_levi_cocharacter :
    ∃ lambda : ClosedSubgroupTorusCocharacter S.T,
      (∀ a ∈ S.positiveRoots \ S.sigmaJ,
        0 < characterCocharacterPairing S.T lambda (Additive.ofMul (S.D.rootWeight a))) ∧
      (∀ a ∈ S.sigmaJ,
        characterCocharacterPairing S.T lambda (Additive.ofMul (S.D.rootWeight a)) = 0) ∧
      (∀ g ∈ U, IsCocharacterContracted (S.T.inclusion.comp lambda) g) ∧
      (L).toSubgroup ≤
        (S.T.inclusion.comp lambda).imageClosedSubgroup.centralizer.toSubgroup := by
  obtain ⟨phi, hpos, hzero⟩ := exists_levi_separating_characterFunctional S
  obtain ⟨lambda, hlambda, hcontract, hcentral⟩ :=
    exists_levi_separating_cocharacter S phi hpos hzero
  have hpair (a : S.D.Root) :
      characterCocharacterPairing S.T lambda (Additive.ofMul (S.D.rootWeight a)) =
        phi (Additive.ofMul (S.D.rootWeight a)) :=
    (weightCocharacterEquation_existsUnique S.T (S.D.rootWeight a) lambda).unique
      (characterCocharacterPairing_spec S.T (S.D.rootWeight a) lambda)
      (hlambda (S.D.rootWeight a))
  exact ⟨lambda, (fun a ha => by rw [hpair]; exact hpos a ha),
    (fun a ha => by rw [hpair]; exact hzero a ha), hcontract, hcentral⟩

/-- GLS3 1.13.3(a), separation: the actual standard unipotent and Levi factors
are disjoint, with no extra geometric assumptions. -/
public theorem unipotent_disjoint_levi : Disjoint (U).toSubgroup (L).toSubgroup := by
  obtain ⟨phi, hpos, hzero⟩ := exists_levi_separating_characterFunctional S
  exact disjoint_of_characterFunctional S phi hpos hzero

end Theory.AlgebraicGroup.InvariantLeviGeometry
