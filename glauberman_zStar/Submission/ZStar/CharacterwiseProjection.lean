import Submission.ZStar.CanonicalLocalCoreSupportScratch
import Submission.ZStar.NagaoComplement
import Submission.ZStar.IsotypicLattice

/-!
# Characterwise coefficient/projection bridge

This file isolates the ordinary-character calculation used after the
projective-range trace vanishing.  The calculation is deliberately stated
over `ℂ`: coefficient change from the localized DVR is handled separately in
the Nagao file.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace CharacterwiseProjection

open PrincipalBlockConstruction
open LocalBlockSection

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

/-! A trace expansion with one fixed group element on the left. -/

theorem trace_left_groupAlgebra_mul
    {H : Type v} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ H V) (x : H)
    (a : MonoidAlgebra ℂ H) :
    LinearMap.trace ℂ V
        (rho x * rho.asAlgebraHom a) =
      ∑ h : H, a.coeff h * rho.character (x * h) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, mul_add, map_add, ha, hb]
      change
        (∑ h : H, a.coeff h * rho.character (x * h)) +
            ∑ h : H, b.coeff h * rho.character (x * h) =
          ∑ h : H,
            (a.coeff h + b.coeff h) * rho.character (x * h)
      simp only [add_mul, Finset.sum_add_distrib]
  | single h r =>
      have hmap :
          rho.asAlgebraHom (MonoidAlgebra.single h r) = r • rho h := by
        rw [show (MonoidAlgebra.single h r : MonoidAlgebra ℂ H) =
            r • MonoidAlgebra.single h (1 : ℂ) by simp]
        rw [map_smul, Representation.asAlgebraHom_single_one]
      rw [hmap, Algebra.mul_smul_comm, map_smul]
      change r * LinearMap.trace ℂ V (rho x * rho h) =
        ∑ y : H, (MonoidAlgebra.single h r).coeff y *
          LinearMap.trace ℂ V (rho (x * y))
      rw [show rho x * rho h = rho (x * h) by rw [← map_mul]]
      rw [Finset.sum_eq_single h]
      · rw [show (MonoidAlgebra.single h r).coeff h = r by
          change (Finsupp.single h r) h = r
          simp]
      · intro y _hy hyh
        rw [show (MonoidAlgebra.single h r).coeff y = 0 by
          change (Finsupp.single h r) y = 0
          exact Finsupp.single_eq_of_ne hyh]
        exact zero_mul _
      · simp

/-! Convolution by the ordinary principal-block idempotent is the
orthogonal projection on class functions. -/

theorem principalBlockElement_convolution_projection
    {H : Type v} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : Representation.ClassFunction H) (x : H) :
    ∑ h : H,
        (BlockOrthogonality.principalBlockElement e).coeff h *
          f (ConjClasses.mk (x * h)) =
      LocalBlockSection.localPrincipalBlockProjection e f
        (ConjClasses.mk x) := by
  classical
  rw [LocalBlockSection.localPrincipalBlockProjection_apply]
  have hexpand (y : H) :
      f (ConjClasses.mk y) =
        ∑ j : e.I,
          Representation.classFunctionInner f (e.chi j) *
            e.chi j (ConjClasses.mk y) := by
    simpa using Representation.completeFamily_apply_eq_sum_inner
      e.complete f (ConjClasses.mk y)
  have hchar_sum (j : e.I) :
      ∑ h : H,
          (BlockOrthogonality.principalBlockElement e).coeff h *
            e.chi j (ConjClasses.mk (x * h)) =
        (if j ∈ e.block then (1 : ℂ) else 0) *
          e.chi j (ConjClasses.mk x) := by
    rcases (e.complete.1 j).1 with ⟨n, rho, hrho⟩
    have htrace := trace_left_groupAlgebra_mul rho x
      (BlockOrthogonality.principalBlockElement e)
    have haction := BlockOrthogonality.principalBlockElement_action
      e j rho hrho
    have hchi (y : H) :
        e.chi j (ConjClasses.mk y) = rho.character y := by
      rw [hrho]
      rfl
    calc
      _ = LinearMap.trace ℂ (Fin n → ℂ)
            (rho x * rho.asAlgebraHom
              (BlockOrthogonality.principalBlockElement e)) := by
          simp_rw [hchi]
          exact htrace.symm
      _ = LinearMap.trace ℂ (Fin n → ℂ)
            (rho x * ((if j ∈ e.block then (1 : ℂ) else 0) •
              (1 : Module.End ℂ (Fin n → ℂ)))) := by rw [haction]
      _ = _ := by
        by_cases hj : j ∈ e.block
        · simp only [hj, if_true, one_smul, mul_one]
          exact (hchi x).symm.trans (one_mul _).symm
        · simp [hj]
  calc
    ∑ h : H,
          (BlockOrthogonality.principalBlockElement e).coeff h *
            f (ConjClasses.mk (x * h)) =
        ∑ j : e.I,
          Representation.classFunctionInner f (e.chi j) *
            (∑ h : H,
              (BlockOrthogonality.principalBlockElement e).coeff h *
                e.chi j (ConjClasses.mk (x * h))) := by
      simp_rw [hexpand, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ = ∑ j : e.I,
          if j ∈ e.block then
            Representation.classFunctionInner f (e.chi j) *
              e.chi j (ConjClasses.mk x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hchar_sum]
      by_cases hj : j ∈ e.block <;> simp [hj]
    _ = ∑ j ∈ e.block,
          Representation.classFunctionInner f (e.chi j) *
            e.chi j (ConjClasses.mk x) := by
      simpa using
        (Finset.sum_filter (s := Finset.univ)
          (fun j : e.I => j ∈ e.block)
          (fun j => Representation.classFunctionInner f (e.chi j) *
            e.chi j (ConjClasses.mk x))).symm

/-! Coefficient change sends the compatible local selector to its ordinary
complex principal-block idempotent. -/

private instance principalPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

set_option maxHeartbeats 1200000 in
theorem map_localPrincipalBlockElementInAmbientLocalization
    (d : PrincipalCongruenceBlockData G) (H : Subgroup G) :
    MonoidAlgebra.mapRingHom H (IsotypicLattice.localizationToComplex d)
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization
          d H) =
      BlockOrthogonality.principalBlockElement
        (CompatibleBrauerBlock.localData d H) := by
  let l : PrincipalCongruenceBlockData H :=
    CompatibleBrauerBlock.localData d H
  let phi : Localization.AtPrime d.primeIdeal →+* ℂ :=
    IsotypicLattice.localizationToComplex d
  let incl : Localization.AtPrime l.primeIdeal →+*
      Localization.AtPrime d.primeIdeal :=
    CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H
  let phiLocal : Localization.AtPrime l.primeIdeal →+* ℂ :=
    IsotypicLattice.localizationToComplex l
  have hf : ∀ a : Representation.cyclotomicOrder l.eta,
      phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        (a : ℂ) := by
    intro a
    exact IsotypicLattice.localizationToComplex_algebraMap l a
  have hlocal0 :=
    BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      (G := H) l phiLocal hf
  have hhom : phi.comp incl = phiLocal := by
    apply IsLocalization.ringHom_ext l.primeIdeal.primeCompl
    apply RingHom.ext
    intro a
    change phi (incl (algebraMap _ (Localization.AtPrime l.primeIdeal) a)) =
      phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a)
    rw [show incl (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        algebraMap _ (Localization.AtPrime d.primeIdeal)
          (CompatibleLocalBlock.cyclotomicOrderInclusion
            (CompatibleLocalBlock.subgroupRoot_mem d H) a) by
      exact CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion_algebraMap
        d H a]
    rw [show phi (algebraMap _ (Localization.AtPrime d.primeIdeal)
          (CompatibleLocalBlock.cyclotomicOrderInclusion
            (CompatibleLocalBlock.subgroupRoot_mem d H) a)) =
        ((CompatibleLocalBlock.cyclotomicOrderInclusion
          (CompatibleLocalBlock.subgroupRoot_mem d H) a :
            Representation.cyclotomicOrder d.eta) : ℂ) by
      exact IsotypicLattice.localizationToComplex_algebraMap d _]
    rw [show phiLocal (algebraMap _ (Localization.AtPrime l.primeIdeal) a) =
        (a : ℂ) by
      exact IsotypicLattice.localizationToComplex_algebraMap l a]
    exact Subring.coe_inclusion _ a
  rw [CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization]
  change MonoidAlgebra.mapRingHom H phi
      (MonoidAlgebra.mapRingHom H incl
        (BlockOrthogonality.localizedPrincipalBlockElement l)) =
    BlockOrthogonality.principalBlockElement l
  have hmap :
      MonoidAlgebra.mapRingHom H phi
          (MonoidAlgebra.mapRingHom H
            incl (BlockOrthogonality.localizedPrincipalBlockElement l)) =
        MonoidAlgebra.mapRingHom H phiLocal
          (BlockOrthogonality.localizedPrincipalBlockElement l) := by
    ext g
    simp only [MonoidAlgebra.mapRingHom_apply]
    exact DFunLike.congr_fun hhom
      ((BlockOrthogonality.localizedPrincipalBlockElement l) g)
  exact hmap.trans hlocal0

theorem map_principalComplement
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra.mapRingHom G (IsotypicLattice.localizationToComplex d)
        (NagaoComplement.principalComplement d z) =
      BlockOrthogonality.principalBlockElement d -
        BlockOrthogonality.principalBlockElement d *
          NagaoComplement.centralizerSubtypeMap z
            (BlockOrthogonality.principalBlockElement
              (CompatibleBrauerBlock.localData d
                (Subgroup.centralizer ({z} : Set G)))) := by
  rw [NagaoComplement.principalComplement, NagaoComplement.complement,
    map_sub, map_mul,
    NagaoComplement.mapRingHom_centralizerSubtypeMap,
    map_localPrincipalBlockElementInAmbientLocalization]
  rw [BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
    d (IsotypicLattice.localizationToComplex d)]
  intro a
  exact IsotypicLattice.localizationToComplex_algebraMap d a

/-! Multiplication by the denominator-cleared primitive projector reads off
the trace of the left factor in the chosen irreducible representation. -/

theorem mul_complexCharacterProjectorNumerator_coeff_one
    (d : PrincipalCongruenceBlockData G) (i : d.I)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hrho : d.chi i = rho.characterClassFunction)
    (a : MonoidAlgebra ℂ G) :
    (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
      d.chi i (ConjClasses.mk (1 : G)) *
        LinearMap.trace ℂ (Fin n → ℂ) (rho.asAlgebraHom a) := by
  classical
  have hcoeff :
      (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
        d.chi i (ConjClasses.mk (1 : G)) *
          ∑ g : G, a.coeff g * d.chi i (ConjClasses.mk g) := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
        rw [add_mul, MonoidAlgebra.coeff_add]
        change
          (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 +
              (b * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
            _
        rw [ha, hb]
        simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul,
          Finset.sum_add_distrib]
        ring
    | single g r =>
        change
          (MonoidAlgebra.single g r *
              IsotypicLattice.complexCharacterProjectorNumerator d i) 1 = _
        rw [MonoidAlgebra.single_mul_apply]
        rw [IsotypicLattice.complexCharacterProjectorNumerator_apply]
        simp only [mul_one, inv_inv]
        rw [Finset.sum_eq_single g]
        · change r *
              (d.chi i (ConjClasses.mk (1 : G)) *
                d.chi i (ConjClasses.mk g)) =
            d.chi i (ConjClasses.mk (1 : G)) *
              ((MonoidAlgebra.single g r).coeff g *
                d.chi i (ConjClasses.mk g))
          rw [show (MonoidAlgebra.single g r).coeff g = r by
            change (Finsupp.single g r) g = r
            simp]
          ring
        · intro y _hy hyg
          rw [show (MonoidAlgebra.single g r).coeff y = 0 by
            change (Finsupp.single g r) y = 0
            exact Finsupp.single_eq_of_ne hyg]
          simp
        · simp
  rw [hcoeff, IsotypicLattice.groupAlgebra_trace]
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [show d.chi i (ConjClasses.mk g) = rho.character g by
    rw [hrho]
    rfl]

/-! The ambient representation sees an embedded centralizer algebra through
its restricted representation. -/

theorem asAlgebraHom_centralizerSubtypeMap
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (z : G)
    (b : MonoidAlgebra ℂ (Subgroup.centralizer ({z} : Set G))) :
    rho.asAlgebraHom (NagaoComplement.centralizerSubtypeMap z b) =
      Representation.asAlgebraHom
        (rho.comp (Subgroup.centralizer ({z} : Set G)).subtype) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => rw [map_add, map_add, hb, hc, map_add]
  | single h r =>
      have hsubtype :
          NagaoComplement.centralizerSubtypeMap z
              (MonoidAlgebra.single h r) =
            (MonoidAlgebra.single (h : G) r : MonoidAlgebra ℂ G) := by
        simp [NagaoComplement.centralizerSubtypeMap,
          MonoidAlgebra.mapDomainRingHom_apply]
      rw [hsubtype]
      rw [show (MonoidAlgebra.single (h : G) r : MonoidAlgebra ℂ G) =
          r • MonoidAlgebra.single (h : G) 1 by simp]
      rw [show (MonoidAlgebra.single h r :
          MonoidAlgebra ℂ (Subgroup.centralizer ({z} : Set G))) =
          r • MonoidAlgebra.single h 1 by simp]
      rw [map_smul, map_smul,
        Representation.asAlgebraHom_single_one,
        Representation.asAlgebraHom_single_one]
      rfl

/-! The complex coefficient of the character projector against the Nagao
complement is the degree times the outside-local-block part of the section. -/

theorem complex_principalComplement_projector_coeff
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (x : Subgroup.centralizer ({z} : Set G))
    (hi : i ∈ d.block) :
    ((MonoidAlgebra.of ℂ G (z * (x : G))) *
          (BlockOrthogonality.principalBlockElement d -
            BlockOrthogonality.principalBlockElement d *
              NagaoComplement.centralizerSubtypeMap z
                (BlockOrthogonality.principalBlockElement
                  (CompatibleBrauerBlock.localData d
                    (Subgroup.centralizer ({z} : Set G))))) *
        IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
      d.chi i (ConjClasses.mk (1 : G)) *
        (LocalBlockSection.localSectionClassFunction d i z
              (ConjClasses.mk x) -
          LocalBlockSection.localPrincipalBlockProjection
              (CompatibleBrauerBlock.localData d
                (Subgroup.centralizer ({z} : Set G)))
              (LocalBlockSection.localSectionClassFunction d i z)
              (ConjClasses.mk x)) := by
  classical
  let H := Subgroup.centralizer ({z} : Set G)
  letI : Fintype H := Fintype.ofFinite H
  let e : PrincipalCongruenceBlockData H :=
    CompatibleBrauerBlock.localData d H
  let B : MonoidAlgebra ℂ H :=
    BlockOrthogonality.principalBlockElement e
  let E : MonoidAlgebra ℂ G :=
    BlockOrthogonality.principalBlockElement d
  let q : MonoidAlgebra ℂ G :=
    IsotypicLattice.complexCharacterProjectorNumerator d i
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  let rhoH : Representation ℂ H (Fin n → ℂ) := rho.comp H.subtype
  let zH : H := LocalBlockSection.selfInCentralizer z
  have hE : rho.asAlgebraHom E = 1 := by
    have haction := BlockOrthogonality.principalBlockElement_action
      d i rho hrho
    simpa [E, hi] using haction
  have hB :
      rho.asAlgebraHom (NagaoComplement.centralizerSubtypeMap z B) =
        rhoH.asAlgebraHom B := by
    simpa [rhoH] using asAlgebraHom_centralizerSubtypeMap rho z B
  have hsection (y : H) :
      rhoH.character (zH * y) =
        LocalBlockSection.localSectionClassFunction d i z
          (ConjClasses.mk y) := by
    rw [LocalBlockSection.localSectionClassFunction_mk, hrho]
    rfl
  have hprojection :
      LinearMap.trace ℂ (Fin n → ℂ)
          (rho (z * (x : G)) * rhoH.asAlgebraHom B) =
        LocalBlockSection.localPrincipalBlockProjection e
          (LocalBlockSection.localSectionClassFunction d i z)
          (ConjClasses.mk x) := by
    calc
      LinearMap.trace ℂ (Fin n → ℂ)
          (rho (z * (x : G)) * rhoH.asAlgebraHom B) =
        LinearMap.trace ℂ (Fin n → ℂ)
          (rhoH (zH * x) * rhoH.asAlgebraHom B) := by rfl
      _ = ∑ y : H, B.coeff y * rhoH.character ((zH * x) * y) :=
        trace_left_groupAlgebra_mul rhoH (zH * x) B
      _ = ∑ y : H, B.coeff y *
          LocalBlockSection.localSectionClassFunction d i z
            (ConjClasses.mk (x * y)) := by
        apply Finset.sum_congr rfl
        intro y _hy
        congr 1
        rw [← hsection (x * y)]
        congr 1
        exact mul_assoc zH x y
      _ = LocalBlockSection.localPrincipalBlockProjection e
          (LocalBlockSection.localSectionClassFunction d i z)
          (ConjClasses.mk x) :=
        principalBlockElement_convolution_projection e
          (LocalBlockSection.localSectionClassFunction d i z) x
  change
    ((MonoidAlgebra.of ℂ G (z * (x : G))) * (E - E *
        NagaoComplement.centralizerSubtypeMap z B) * q).coeff 1 = _
  rw [mul_complexCharacterProjectorNumerator_coeff_one d i rho hrho]
  congr 1
  have hmapFactor :
      rho.asAlgebraHom
          (MonoidAlgebra.of ℂ G (z * (x : G)) *
            (E - E * NagaoComplement.centralizerSubtypeMap z B)) =
        rho (z * (x : G)) * (1 - rhoH.asAlgebraHom B) := by
    calc
      rho.asAlgebraHom
          (MonoidAlgebra.of ℂ G (z * (x : G)) *
            (E - E * NagaoComplement.centralizerSubtypeMap z B)) =
          rho.asAlgebraHom (MonoidAlgebra.of ℂ G (z * (x : G))) *
            rho.asAlgebraHom
              (E - E * NagaoComplement.centralizerSubtypeMap z B) :=
        map_mul rho.asAlgebraHom _ _
      _ = rho (z * (x : G)) *
          (rho.asAlgebraHom E -
            rho.asAlgebraHom E *
              rho.asAlgebraHom
                (NagaoComplement.centralizerSubtypeMap z B)) := by
        simp only [Representation.asAlgebraHom_of, map_sub, map_mul]
      _ = rho (z * (x : G)) * (1 - rhoH.asAlgebraHom B) := by
        rw [hE, hB, one_mul]
  rw [hmapFactor, mul_sub, mul_one, map_sub, hprojection]
  change rho.character (z * (x : G)) - _ = _
  rw [← hsection x]
  rfl

/-- Localized coefficient form used directly after the integral Nagao trace
vanishing. -/
theorem localizationToComplex_principalComplement_projector_coeff
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (x : Subgroup.centralizer ({z} : Set G))
    (hi : i ∈ d.block) :
    IsotypicLattice.localizationToComplex d
        (((MonoidAlgebra.of (Localization.AtPrime d.primeIdeal) G
              (z * (x : G))) *
            NagaoComplement.principalComplement d z *
            IsotypicLattice.characterProjectorNumerator d i).coeff 1) =
      d.chi i (ConjClasses.mk (1 : G)) *
        (LocalBlockSection.localSectionClassFunction d i z
              (ConjClasses.mk x) -
          LocalBlockSection.localPrincipalBlockProjection
              (CompatibleBrauerBlock.localData d
                (Subgroup.centralizer ({z} : Set G)))
              (LocalBlockSection.localSectionClassFunction d i z)
              (ConjClasses.mk x)) := by
  let R := Localization.AtPrime d.primeIdeal
  let phi := IsotypicLattice.localizationToComplex d
  let a : MonoidAlgebra R G :=
    MonoidAlgebra.of R G (z * (x : G))
  let b : MonoidAlgebra R G := NagaoComplement.principalComplement d z
  let q : MonoidAlgebra R G :=
    IsotypicLattice.characterProjectorNumerator d i
  change (MonoidAlgebra.mapRingHom G phi (a * b * q)).coeff 1 = _
  have hmapProduct :
      MonoidAlgebra.mapRingHom G phi (a * b * q) =
        MonoidAlgebra.mapRingHom G phi a *
          MonoidAlgebra.mapRingHom G phi b *
            MonoidAlgebra.mapRingHom G phi q := by
    rw [map_mul, map_mul]
  rw [hmapProduct]
  have hmapA :
      MonoidAlgebra.mapRingHom G phi a =
        MonoidAlgebra.of ℂ G (z * (x : G)) := by
    ext g
    simp [phi, a, MonoidAlgebra.mapRingHom_apply, MonoidAlgebra.of]
  rw [hmapA]
  rw [show MonoidAlgebra.mapRingHom G phi b =
      BlockOrthogonality.principalBlockElement d -
        BlockOrthogonality.principalBlockElement d *
          NagaoComplement.centralizerSubtypeMap z
            (BlockOrthogonality.principalBlockElement
              (CompatibleBrauerBlock.localData d
                (Subgroup.centralizer ({z} : Set G)))) by
      simpa [phi, b] using map_principalComplement d z]
  rw [show MonoidAlgebra.mapRingHom G phi q =
      IsotypicLattice.complexCharacterProjectorNumerator d i by
      simpa [phi, q] using
        IsotypicLattice.map_characterProjectorNumerator d i]
  change
    ((MonoidAlgebra.of ℂ G (z * (x : G))) *
          (BlockOrthogonality.principalBlockElement d -
            BlockOrthogonality.principalBlockElement d *
              NagaoComplement.centralizerSubtypeMap z
                (BlockOrthogonality.principalBlockElement
                  (CompatibleBrauerBlock.localData d
                    (Subgroup.centralizer ({z} : Set G))))) *
        IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 = _
  exact complex_principalComplement_projector_coeff d i z x hi

/-- Vanishing of the integral coefficient forces the desired pointwise local
principal-block projection identity. -/
theorem localPrincipalBlockProjection_eq_of_projector_coeff_eq_zero
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (x : Subgroup.centralizer ({z} : Set G))
    (hi : i ∈ d.block)
    (hzero :
      (((MonoidAlgebra.of (Localization.AtPrime d.primeIdeal) G
              (z * (x : G))) *
            NagaoComplement.principalComplement d z *
            IsotypicLattice.characterProjectorNumerator d i).coeff 1) = 0) :
    LocalBlockSection.localPrincipalBlockProjection
          (CompatibleBrauerBlock.localData d
            (Subgroup.centralizer ({z} : Set G)))
          (LocalBlockSection.localSectionClassFunction d i z)
          (ConjClasses.mk x) =
      LocalBlockSection.localSectionClassFunction d i z
        (ConjClasses.mk x) := by
  have hmapped := congrArg (IsotypicLattice.localizationToComplex d) hzero
  rw [localizationToComplex_principalComplement_projector_coeff d i z x hi,
    map_zero] at hmapped
  have hdegree : d.chi i (ConjClasses.mk (1 : G)) ≠ 0 :=
    CharacterArgument.irreducibleCharacter_degree_ne_zero
      (d.chi i) (d.complete.1 i)
  have hsub :
      LocalBlockSection.localSectionClassFunction d i z
            (ConjClasses.mk x) -
          LocalBlockSection.localPrincipalBlockProjection
            (CompatibleBrauerBlock.localData d
              (Subgroup.centralizer ({z} : Set G)))
            (LocalBlockSection.localSectionClassFunction d i z)
            (ConjClasses.mk x) = 0 := by
    exact (mul_eq_zero.mp hmapped).resolve_left hdegree
  exact (sub_eq_zero.mp hsub).symm

end CharacterwiseProjection

end Submission.ZStar
