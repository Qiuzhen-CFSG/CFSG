module

public import Theory.Character.ModularBlock.CompatibleSelectorComplex
public import Theory.GroupTheory.ZStar.Nagao.SelectorConvolution
public import Theory.GroupTheory.ZStar.Nagao.Complement
public import Theory.GroupTheory.ZStar.CharacterKernel

/-!
# The characterwise coefficient-projection identity

Multiplying the principal Nagao complement by a denominator-cleared
character projector produces, at the identity coefficient, the character
degree times the difference between its involution section and its local
principal-block projection. First identify the compatible integral local
selector with the ordinary complex selector. The projector trace formula
and selector-convolution identity compute the complex coefficient; injective
coefficient change supplies the localized version. Nonzero irreducible degree
then turns coefficient vanishing into the desired projection identity.

This is the ordinary-character bridge following the projective Nagao trace
calculation. Its historical helper names are re-exported from the shared
algebra modules. Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseProjection.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace Glauberman.ZStar.CharacterwiseProjection

open ModularBlock PrincipalBlockConstruction LocalBlockSection

export ModularBlock.CharacterwiseProjection
  (trace_left_groupAlgebra_mul map_localPrincipalBlockElementInAmbientLocalization
    mul_complexCharacterProjectorNumerator_coeff_one asAlgebraHom_centralizerSubtypeMap)

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

private instance principalPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

theorem map_principalComplement
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra.mapRingHom G (IsotypicLattice.localizationToComplex d)
        (NagaoComplement.principalComplement d z) =
      BlockOrthogonality.principalBlockElement d -
        BlockOrthogonality.principalBlockElement d *
          ModularBlock.NagaoComplement.centralizerSubtypeMap z
            (BlockOrthogonality.principalBlockElement
              (CompatibleBrauerBlock.localData d
                (Subgroup.centralizer ({z} : Set G)))) := by
  rw [NagaoComplement.principalComplement, ModularBlock.NagaoComplement.complement,
    map_sub, map_mul,
    ModularBlock.NagaoComplement.mapRingHom_centralizerSubtypeMap,
    map_localPrincipalBlockElementInAmbientLocalization]
  rw [BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
    d (IsotypicLattice.localizationToComplex d)]
  intro a
  exact IsotypicLattice.localizationToComplex_algebraMap d a

/-! The complex coefficient of the character projector against the Nagao
complement is the degree times the outside-local-block part of the section. -/

theorem complex_principalComplement_projector_coeff
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (x : Subgroup.centralizer ({z} : Set G))
    (hi : i ∈ d.block) :
    ((MonoidAlgebra.of ℂ G (z * (x : G))) *
          (BlockOrthogonality.principalBlockElement d -
            BlockOrthogonality.principalBlockElement d *
              ModularBlock.NagaoComplement.centralizerSubtypeMap z
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
  let : Fintype H := Fintype.ofFinite H
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
      rho.asAlgebraHom (ModularBlock.NagaoComplement.centralizerSubtypeMap z B) =
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
        ModularBlock.NagaoComplement.centralizerSubtypeMap z B) * q).coeff 1 = _
  rw [mul_complexCharacterProjectorNumerator_coeff_one d i rho hrho]
  congr 1
  have hmapFactor :
      rho.asAlgebraHom
          (MonoidAlgebra.of ℂ G (z * (x : G)) *
            (E - E * ModularBlock.NagaoComplement.centralizerSubtypeMap z B)) =
        rho (z * (x : G)) * (1 - rhoH.asAlgebraHom B) := by
    calc
      rho.asAlgebraHom
          (MonoidAlgebra.of ℂ G (z * (x : G)) *
            (E - E * ModularBlock.NagaoComplement.centralizerSubtypeMap z B)) =
          rho.asAlgebraHom (MonoidAlgebra.of ℂ G (z * (x : G))) *
            rho.asAlgebraHom
              (E - E * ModularBlock.NagaoComplement.centralizerSubtypeMap z B) :=
        map_mul rho.asAlgebraHom _ _
      _ = rho (z * (x : G)) *
          (rho.asAlgebraHom E -
            rho.asAlgebraHom E *
              rho.asAlgebraHom
                (ModularBlock.NagaoComplement.centralizerSubtypeMap z B)) := by
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
    simp [phi, a, MonoidAlgebra.of]
  rw [hmapA]
  rw [show MonoidAlgebra.mapRingHom G phi b =
      BlockOrthogonality.principalBlockElement d -
        BlockOrthogonality.principalBlockElement d *
          ModularBlock.NagaoComplement.centralizerSubtypeMap z
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
              ModularBlock.NagaoComplement.centralizerSubtypeMap z
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


end Glauberman.ZStar.CharacterwiseProjection

