import Submission.ZStar.BlockPrimitivity
import Submission.ZStar.LeftIdealHigman
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
The complementary idempotent used in the order-two Nagao argument.

This file starts with the coefficient-restriction calculation for multiplying
an ambient group-algebra element by an element supported on the centralizer.
-/

noncomputable section

namespace Submission.ZStar
namespace NagaoComplement

universe u v

attribute [local instance] Fintype.ofFinite

/-- Embed the group algebra of the centralizer in the ambient group
algebra. -/
noncomputable def centralizerSubtypeMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) :
    MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)) →+*
      MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingHom R
    (Subgroup.centralizer ({z} : Set G)).subtype

/-- The Nagao complement attached to an ambient idempotent `e` and a local
centralizer idempotent `b`. -/
noncomputable def complement
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (e : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    MonoidAlgebra R G :=
  e - e * centralizerSubtypeMap z b

/-- Every element supported on `C_G(z)` commutes with the group-algebra
element represented by `z`. -/
theorem commute_centralizerSubtypeMap_self
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    Commute (centralizerSubtypeMap z b) (MonoidAlgebra.of R G z) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero]
      exact Commute.zero_left _
  | add b c hb hc =>
      rw [map_add]
      exact hb.add_left hc
  | single h r =>
      rw [commute_iff_eq]
      rw [show centralizerSubtypeMap z (MonoidAlgebra.single h r) =
          MonoidAlgebra.single (h : G) r by
        simp [centralizerSubtypeMap,
          MonoidAlgebra.mapDomainRingHom_apply]]
      change
        MonoidAlgebra.single (h : G) r * MonoidAlgebra.single z 1 =
          MonoidAlgebra.single z 1 * MonoidAlgebra.single (h : G) r
      rw [MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      have hh : (h : G) * z = z * (h : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp h.property
      rw [hh]
      simp

/-- The embedded local idempotent is fixed under conjugation by `z`. -/
theorem conjugation_centralizerSubtypeMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerKernelRelativeTrace.conjugation R z
        (centralizerSubtypeMap z b) = centralizerSubtypeMap z b := by
  rw [LeftIdealHigman.conjugation_eq_group_elements_mul]
  have hcomm := commute_centralizerSubtypeMap_self z b
  calc
    MonoidAlgebra.of R G z * centralizerSubtypeMap z b *
          MonoidAlgebra.of R G z⁻¹ =
        centralizerSubtypeMap z b *
          (MonoidAlgebra.of R G z * MonoidAlgebra.of R G z⁻¹) := by
            rw [hcomm.eq.symm]
            exact mul_assoc _ _ _
    _ = centralizerSubtypeMap z b := by rw [← map_mul, mul_inv_cancel, map_one,
      mul_one]

/-- A central ambient group-algebra element is fixed under inner
conjugation. -/
theorem conjugation_eq_self_of_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    BrauerKernelRelativeTrace.conjugation R z e = e := by
  rw [LeftIdealHigman.conjugation_eq_group_elements_mul]
  have hcomm : Commute (MonoidAlgebra.of R G z) e :=
    Semigroup.mem_center_iff.mp he _
  calc
    MonoidAlgebra.of R G z * e * MonoidAlgebra.of R G z⁻¹ =
        e * (MonoidAlgebra.of R G z * MonoidAlgebra.of R G z⁻¹) := by
          rw [hcomm.eq]
          exact mul_assoc _ _ _
    _ = e := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]

/-- The Nagao complement is an idempotent whenever the ambient and local
selectors are idempotent and the ambient selector is central. -/
theorem complement_isIdempotent
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (e : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (he : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (hb : IsIdempotentElem b) :
    IsIdempotentElem (complement z e b) := by
  let B := centralizerSubtypeMap z b
  have hB : IsIdempotentElem B :=
    hb.map (centralizerSubtypeMap z)
  have heB : Commute e B :=
    (Semigroup.mem_center_iff.mp hecenter B).symm
  have heOneSubB : Commute e (1 - B) :=
    (Commute.one_right e).sub_right heB
  have hprod : IsIdempotentElem (e * (1 - B)) :=
    IsIdempotentElem.mul_of_commute heOneSubB he hB.one_sub
  simpa [complement, B, mul_sub] using hprod

/-- The Nagao complement is fixed by conjugation by the distinguished
centralizer element. -/
theorem conjugation_complement
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (e : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hecenter : e ∈ Set.center (MonoidAlgebra R G)) :
    BrauerKernelRelativeTrace.conjugation R z (complement z e b) =
      complement z e b := by
  rw [complement, map_sub, map_mul,
    conjugation_eq_self_of_mem_center z e hecenter,
    conjugation_centralizerSubtypeMap z b]

theorem centralizerRestriction_mul_subtypeMap
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (a : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMapScratch.centralizerRestriction R z
        (a * MonoidAlgebra.mapDomainRingHom R
          (Subgroup.centralizer ({z} : Set G)).subtype b) =
      BrauerMapScratch.centralizerRestriction R z a * b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, mul_zero, map_zero, mul_zero]
  | add b c hb hc => rw [map_add, mul_add, map_add, hb, hc, mul_add]
  | single h r =>
      ext x
      simp [BrauerMapScratch.centralizerRestriction_apply,
        MonoidAlgebra.mul_single_apply]

theorem centralizerRestriction_subtypeMap_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (a : MonoidAlgebra R G) :
    BrauerMapScratch.centralizerRestriction R z
        (MonoidAlgebra.mapDomainRingHom R
          (Subgroup.centralizer ({z} : Set G)).subtype b * a) =
      b * BrauerMapScratch.centralizerRestriction R z a := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, zero_mul, map_zero, zero_mul]
  | add b c hb hc => rw [map_add, add_mul, map_add, hb, hc, add_mul]
  | single h r =>
      ext x
      simp [BrauerMapScratch.centralizerRestriction_apply,
        MonoidAlgebra.single_mul_apply]

/-- Coefficient change commutes with the embedding of a centralizer group
algebra into the ambient group algebra. -/
theorem mapRingHom_centralizerSubtypeMap
    {R S : Type u} {G : Type v} [CommRing R] [CommRing S] [Group G]
    (phi : R →+* S) (z : G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    MonoidAlgebra.mapRingHom G phi (centralizerSubtypeMap z b) =
      centralizerSubtypeMap z
        (MonoidAlgebra.mapRingHom
          (Subgroup.centralizer ({z} : Set G)) phi b) := by
  have h := MonoidAlgebra.mapRingHom_comp_mapDomainRingHom phi
    (Subgroup.centralizer ({z} : Set G)).subtype
  exact DFunLike.congr_fun h b

/-- After changing coefficients, restriction of the Nagao complement is the
ambient restricted selector minus its product with the changed local
selector. -/
theorem centralizerRestriction_mapRingHom_complement
    {R S : Type u} {G : Type v} [CommRing R] [CommRing S] [Group G]
    (phi : R →+* S) (z : G) (e : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) :
    BrauerMapScratch.centralizerRestriction S z
        (MonoidAlgebra.mapRingHom G phi (complement z e b)) =
      BrauerMapScratch.centralizerRestriction S z
          (MonoidAlgebra.mapRingHom G phi e) -
        BrauerMapScratch.centralizerRestriction S z
            (MonoidAlgebra.mapRingHom G phi e) *
          MonoidAlgebra.mapRingHom
            (Subgroup.centralizer ({z} : Set G)) phi b := by
  rw [complement, map_sub, map_mul,
    mapRingHom_centralizerSubtypeMap phi z b, map_sub]
  change _ - BrauerMapScratch.centralizerRestriction S z
      (MonoidAlgebra.mapRingHom G phi e *
        MonoidAlgebra.mapDomainRingHom S
          (Subgroup.centralizer ({z} : Set G)).subtype
          (MonoidAlgebra.mapRingHom
            (Subgroup.centralizer ({z} : Set G)) phi b)) = _
  rw [centralizerRestriction_mul_subtypeMap]

/-- Under the justified local factor identity, the reduced coefficient
restriction of the local-principal complement is exactly the difference
between the full ambient Brauer image and its local principal factor.  In
particular, the factor identity alone does *not* make this restriction zero. -/
theorem centralizerRestriction_mapRingHom_complement_eq_sub
    {R S : Type u} {G : Type v} [CommRing R] [CommRing S] [Group G]
    (phi : R →+* S) (z : G) (e : MonoidAlgebra R G)
    (b : MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)))
    (hcenter : BrauerMapScratch.centralizerRestriction S z
          (MonoidAlgebra.mapRingHom G phi e) ∈
        Set.center (MonoidAlgebra S
          (Subgroup.centralizer ({z} : Set G))))
    (hfactor :
      MonoidAlgebra.mapRingHom
            (Subgroup.centralizer ({z} : Set G)) phi b *
          BrauerMapScratch.centralizerRestriction S z
            (MonoidAlgebra.mapRingHom G phi e) =
        MonoidAlgebra.mapRingHom
          (Subgroup.centralizer ({z} : Set G)) phi b) :
    BrauerMapScratch.centralizerRestriction S z
        (MonoidAlgebra.mapRingHom G phi (complement z e b)) =
      BrauerMapScratch.centralizerRestriction S z
          (MonoidAlgebra.mapRingHom G phi e) -
        MonoidAlgebra.mapRingHom
          (Subgroup.centralizer ({z} : Set G)) phi b := by
  rw [centralizerRestriction_mapRingHom_complement]
  have hcomm := Semigroup.mem_center_iff.mp hcenter
    (MonoidAlgebra.mapRingHom
      (Subgroup.centralizer ({z} : Set G)) phi b)
  rw [← hcomm, hfactor]

open PrincipalBlockConstruction

private instance principalPrime_isPrime
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

/-- The concrete complement between the ambient localized principal-block
selector and the compatible local principal selector. -/
noncomputable def principalComplement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G :=
  complement z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))

theorem principalComplement_isIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    IsIdempotentElem (principalComplement d z) := by
  exact complement_isIdempotent z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))
    (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d)
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)))

theorem conjugation_principalComplement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    BrauerKernelRelativeTrace.conjugation
        (Localization.AtPrime d.primeIdeal) z (principalComplement d z) =
      principalComplement d z := by
  exact conjugation_complement z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)

/-- Assuming only the valid local factor identity, reduction of the concrete
Nagao complement restricts to `eBrauer - eLocal`.  This records exactly the
additional-local-factor obstruction. -/
theorem centralizerRestriction_reduce_principalComplement_eq_sub
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    BrauerMapScratch.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (MonoidAlgebra.mapRingHom G
          (BrauerBlockReduction.localizationToResidue d)
          (principalComplement d z)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
  let e := BlockOrthogonality.localizedPrincipalBlockElement d
  let b :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G))
  have hE :
      BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (MonoidAlgebra.mapRingHom G
            (BrauerBlockReduction.localizationToResidue d) e) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z := by
    rfl
  have hb :
      MonoidAlgebra.mapRingHom
          (Subgroup.centralizer ({z} : Set G))
          (BrauerBlockReduction.localizationToResidue d) b =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
    exact CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_reduce
      d (Subgroup.centralizer ({z} : Set G))
  have h := centralizerRestriction_mapRingHom_complement_eq_sub
    (BrauerBlockReduction.localizationToResidue d) z e b
    (by simpa [hE] using
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z)
    (by simpa [hb, hE] using hfactor)
  simpa [principalComplement, e, b, hE, hb] using h

/-- Coefficientwise form of the preceding obstruction identity.  A group
element fixed under conjugation by `z` is canonically an element of
`C_G(z)`. -/
theorem localizationToResidue_principalComplement_coeff
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z x : G)
    (hfixed : z⁻¹ * x * z = x)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    let xC : Subgroup.centralizer ({z} : Set G) :=
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc
          x * z = z * (z⁻¹ * x * z) := by group
          _ = z * x := by rw [hfixed])⟩
    BrauerBlockReduction.localizationToResidue d (principalComplement d z x) =
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) xC := by
  let xC : Subgroup.centralizer ({z} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc
        x * z = z * (z⁻¹ * x * z) := by group
        _ = z * x := by rw [hfixed])⟩
  have h := congrArg (fun q : MonoidAlgebra
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) => q xC)
    (centralizerRestriction_reduce_principalComplement_eq_sub d z hfactor)
  simpa [xC, BrauerMapScratch.centralizerRestriction_apply,
    MonoidAlgebra.mapRingHom_apply] using h

/-- For the local-principal complement, the fixed-coefficient hypothesis
needed by `ExactRelativeTrace` is equivalent to the *full* equality between
the ambient Brauer image and the compatible local principal selector.  Thus
the weaker factor identity cannot by itself feed the exact-trace theorem. -/
theorem fixed_coeff_mem_maximalIdeal_principalComplement_iff
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    (∀ x : G, z⁻¹ * x * z = x →
        principalComplement d z x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal)) ↔
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
  constructor
  · intro hcoeff
    ext xC
    let x : G := xC
    have hxcomm : (xC : G) * z = z * (xC : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp xC.property
    have hfixed : z⁻¹ * x * z = x := by
      dsimp [x]
      calc
        z⁻¹ * (xC : G) * z = z⁻¹ * ((xC : G) * z) := mul_assoc _ _ _
        _ = z⁻¹ * (z * (xC : G)) := by rw [hxcomm]
        _ = (xC : G) := by simp
    have hmem := hcoeff x hfixed
    have hzero :
        BrauerBlockReduction.localizationToResidue d
            (principalComplement d z x) = 0 := by
      rw [BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit]
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    have hvalue := localizationToResidue_principalComplement_coeff
      d z x hfixed hfactor
    have hvalue' :
        BrauerBlockReduction.localizationToResidue d
            (principalComplement d z x) =
          (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.centralizer ({z} : Set G))) xC := by
      simpa [x] using hvalue
    have hsub :
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z xC -
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) xC = 0 := by
      calc
        _ = (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
              CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
                (Subgroup.centralizer ({z} : Set G))) xC :=
            (Finsupp.sub_apply _ _ xC).symm
        _ = BrauerBlockReduction.localizationToResidue d
              (principalComplement d z x) := hvalue'.symm
        _ = 0 := hzero
    exact sub_eq_zero.mp hsub
  · intro heq x hfixed
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (principalComplement d z x)
    rw [← BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit]
    rw [localizationToResidue_principalComplement_coeff d z x hfixed hfactor,
      heq, sub_self]
    rfl

end NagaoComplement
end Submission.ZStar
