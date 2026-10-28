module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.PrimePowerGenerated

/-!
# The central parabolic three-residual has trivial unipotent centralizer

In the genuine characteristic-two triality carrier, the standard unipotent
subgroup has trivial intersection with the centralizer of the embedded
prime-to-three residual of the central parabolic. This includes q = 2.

The central rank-one subgroup supplies the literal order-three matrix
`!![0, 1; 1, 1]`. A Cartan column of the Geck representation shows that no
nonidentity highest-root element commutes with its image. The centralizer
of the residual is normal relative to the parabolic, so its intersection
with the unipotent subgroup is normal there. A nontrivial such subgroup
would meet the known highest-root center, giving a contradiction.

The source application is Aschbacher--Smith 15.3.43, printed pp.1139--1140,
using the Sylow and parabolic root geometry of F.1.12(I)(4), pp.263--264
(`refs/quasithin.pdf`). The concrete root conventions are those of GLS3
§§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices

namespace Triality.Standard.Parabolics.BinaryCentralResidual
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private lemma rankOne_entry (P : Parameters) (hp : P.prime = 2) (A : SL(2, ExtensionField P))
    (r s : BlockIndex) :
    matrixHom P ((pinnedRankOneMaps P hp).hom 1 A)
      (latticeEnumeration.symm (latticeEquiv 1 r))
      (latticeEnumeration.symm (latticeEquiv 1 s)) = blockMatrix 1 A r s := by
  let := rankOneExtensionCharTwo P hp
  change (ambientHom 1 A).val
    (latticeEnumeration (latticeEnumeration.symm (latticeEquiv 1 r)))
    (latticeEnumeration (latticeEnumeration.symm (latticeEquiv 1 s))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ambientHom_entry 1 A r s

private lemma flat_block (r : BlockIndex) :
  latticeEnumeration.symm (latticeEquiv 1 r) =
    match r with
    | .inl (.inl j) => .inl j
    | .inl (.inr j) => .inr (rootOrder 1 (rootBlockEnumeration (.inl j)))
    | .inr j => .inr (rootOrder 1 (rootBlockEnumeration (.inr j))) := by
  rcases r with (j | j) | j <;> simp [latticeEnumeration, latticeEquiv]

private lemma rankOne_column (P : Parameters) (hp : P.prime = 2) (A : SL(2, ExtensionField P))
    (r : Index) : matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) r (.inl 1) =
      (1 : Matrix Index Index (ExtensionField P)) r (.inl 1) := by
  obtain ⟨r, rfl⟩ := ((latticeEquiv 1).trans latticeEnumeration.symm).surjective r
  have he := rankOne_entry P hp A r (.inl (.inl 1))
  rcases r with (r | r) | (r | r)
  all_goals simpa [Equiv.trans_apply, flat_block, blockMatrix, specialBlock,
    adjacent, Matrix.one_apply] using he

private lemma rankOne_natural_entry (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) :
    matrixHom P ((pinnedRankOneMaps P hp).hom 1 A) (.inr 4) (.inr 0) = A 1 0 := by
  have he := rankOne_entry P hp A (.inr (.inl (1,0))) (.inr (.inl (0,0)))
  have h0 : latticeEnumeration.symm (latticeEquiv 1 (.inr (.inl (0,0)))) = .inr 0 := by
    rw [flat_block]; rfl
  have h1 : latticeEnumeration.symm (latticeEquiv 1 (.inr (.inl (1,0)))) = .inr 4 := by
    rw [flat_block]; rfl
  simpa only [h0, h1, blockMatrix, Matrix.fromBlocks_apply₂₂,
    Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply_eq] using he

private lemma highest_column (r : Index) :
    linearCoefficient 0 r (.inl 1) = (if r = .inr 0 then 1 else 0) ∧
    quadraticCoefficient 0 r (.inl 1) = 0 := by
  revert r
  decide +kernel

private lemma commuting_column {F : Type*} [Field F] [CharP F 2]
    (A : Matrix Index Index F) (t : F)
    (hc : ∀ r, A r (.inl 1) = (1 : Matrix Index Index F) r (.inl 1))
    (h : Commute A (matrixCurve 0 t)) (r : Index) :
    A r (.inr 0) * t = t * (1 : Matrix Index Index F) r (.inr 0) := by
  have he (s : Index) : matrixCurve 0 t s (.inl 1) =
      (1 : Matrix Index Index F) s (.inl 1) + if s = .inr 0 then t else 0 := by
    obtain ⟨hl,hq⟩ := highest_column s
    simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq]
  have hh := congrFun₂ h.eq r (.inl 1)
  simp only [Matrix.mul_apply, he, hc, mul_add, Finset.sum_add_distrib] at hh
  simp only [← Matrix.mul_apply, mul_one] at hh
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  rw [hc, he] at hh
  have hh' := add_left_cancel hh
  simpa only [Matrix.one_apply, mul_ite, mul_one, mul_zero] using hh'

private lemma central_rankOne_commuting_highest (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (t : ExtensionField P)
    (hA : A 1 0 = 1)
    (h : Commute ((pinnedRankOneMaps P hp).hom 1 A) (curve P 11 t)) : t = 0 := by
  let := rankOneExtensionCharTwo P hp
  have hh := h.map (matrixHom P)
  rw [matrixHom_curve P hp] at hh
  have he := commuting_column _ t (rankOne_column P hp A) hh (.inr 4)
  rw [rankOne_natural_entry P hp A, hA, one_mul] at he
  simpa only [Matrix.one_apply, Sum.inr.injEq, Fin.reduceEq, if_false, mul_zero] using he

private def cubic {F : Type*} [Field F] [CharP F 2] : SL(2,F) :=
  ⟨!![0,1;1,1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private lemma cubic_pow {F : Type*} [Field F] [CharP F 2] : (cubic (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private def centralFixed (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* fixedSubgroup P :=
  (pinnedRankOneMaps P hp).centralFixedEmbedding.codRestrict (fixedSubgroup P)
    (fun A => ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨A,rfl⟩).2)

@[irreducible] private def cubicElementary (P : Parameters) (hp : P.prime = 2) : ElementaryGroup P := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  exact sl2ElementaryLift P hp (centralFixed P hp) cubic

private lemma cubicElementary_pow (P : Parameters) (hp : P.prime = 2) :
    cubicElementary P hp ^ 3 = 1 := by
  unfold cubicElementary
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  exact (map_pow (sl2ElementaryLift P hp (centralFixed P hp)) cubic 3).symm.trans
    ((congrArg _ cubic_pow).trans (map_one _))

private lemma cubicElementary_mem (P : Parameters) (hp : P.prime = 2) :
    toCarrier P (cubicElementary P hp) ∈ parabolic P .central := by
  apply levi_le_parabolic P .central
  refine ⟨cubicElementary P hp, ?_, rfl⟩
  unfold cubicElementary
  exact ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨_,rfl⟩).1

private lemma cubicElementary_inclusion (P : Parameters) (hp : P.prime = 2) :
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
    elementaryInclusion P (cubicElementary P hp) =
      (pinnedRankOneMaps P hp).hom 1 cubic := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  unfold cubicElementary
  change (pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P cubic) = _
  congr 1
  apply Subtype.ext
  change (Matrix.map !![0,1;1,1] (baseFieldEmbedding P)) =
    (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) (ExtensionField P))
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma lift_commute (P : Parameters) (hp : P.prime = 2)
    (x y : ElementaryGroup P) (h : Commute (toCarrier P x) (toCarrier P y)) :
    Commute (elementaryInclusion P x) (elementaryInclusion P y) := by
  have he : Commute x y := Commute.of_map (ElementaryCentralKernel.toCarrier_injective P hp) h
  exact he.map (elementaryInclusion P)

private lemma commute_congr {G : Type*} [Group G] {a b c d : G}
    (ha : a = c) (hb : b = d) (h : Commute a b) : Commute c d := by
  subst c
  subst d
  exact h

private lemma highest_commuting_cubic (P : Parameters) (hp : P.prime = 2)
    (z : fixedField P)
    (h : Commute (toCarrier P (cubicElementary P hp))
      (highestHom P hp (Multiplicative.ofAdd z))) : z = 0 := by
  have hs := lift_commute P hp (cubicElementary P hp)
    (elementaryHighestHom P hp (Multiplicative.ofAdd z)) h
  have hs' := commute_congr (cubicElementary_inclusion P hp)
    (elementaryHighestHom_val P hp (Multiplicative.ofAdd z)) hs
  apply Subtype.ext
  exact central_rankOne_commuting_highest P hp _ _ rfl hs'

private lemma carrier_cube (P : Parameters) (hp : P.prime = 2) :
    toCarrier P (cubicElementary P hp) ^ 3 = 1 := by
  exact (map_pow (toCarrier P) (cubicElementary P hp) 3).symm.trans
    ((congrArg (toCarrier P) (cubicElementary_pow P hp)).trans (map_one _))

private lemma cubic_mem_threeResidual (P : Parameters) (hp : P.prime = 2) :
    (⟨toCarrier P (cubicElementary P hp), cubicElementary_mem P hp⟩ :
      parabolic P .central) ∈ Subgroup.primePowerGenerated 3 (parabolic P .central) := by
  apply Subgroup.mem_primePowerGenerated_of_pow (n := 1)
  apply Subtype.ext
  exact carrier_cube P hp

private lemma centralizer_eq_bot_of_center {G : Type*} [Group G] [Finite G]
    (U Q : Subgroup G) (hUQ : U ≤ Q) (hp : IsPGroup 2 U)
    (hfix : ∀ z : U, z ∈ Subgroup.center U →
      (∀ y : Q, y ∈ Subgroup.primePowerGenerated 3 Q → Commute y.val z.val) → z = 1) :
    U ⊓ Subgroup.centralizer
      ((Subgroup.primePowerGenerated 3 Q).map Q.subtype : Set G) = ⊥ := by
  let i : U →* Q := Subgroup.inclusion hUQ
  let D : Subgroup U := (Subgroup.centralizer
    (Subgroup.primePowerGenerated 3 Q : Set Q)).comap i
  have hD : D = ⊥ := by
    by_contra hne
    apply Subgroup.center_inf_ne_bot_of_normal hp D hne
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro z ⟨hz,hc⟩
    apply hfix z hz
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc _ hy)
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro z ⟨hz,hc⟩
  have hm : (⟨z,hz⟩ : U) ∈ D := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc _ ⟨y,hy,rfl⟩
  have he : (⟨z,hz⟩ : U) = 1 := by simpa only [hD, Subgroup.mem_bot] using hm
  exact congrArg Subtype.val he

/-- The literal central-parabolic three-residual has trivial centralizer in the
standard unipotent subgroup, including the binary endpoint. -/
public theorem unipotent_inf_centralizer_threeResidual_eq_bot
    (P : Parameters) (hp : P.prime = 2) :
    unipotent P ⊓ Subgroup.centralizer
      (((Subgroup.primePowerGenerated 3 (parabolic P .central)).map
        (parabolic P .central).subtype) : Set (Carrier P)) = ⊥ := by
  apply centralizer_eq_bot_of_center (unipotent P) (parabolic P .central)
    ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
    (unipotent_isPGroup_binary P hp)
  intro z hz hc
  have hzH : z.val ∈ highestRoot P := by
    rw [← embedded_center_unipotent P hp]
    exact ⟨z,hz,rfl⟩
  rw [← highestHom_range P hp] at hzH
  obtain ⟨t, ht⟩ := hzH
  have hcomm := hc _ (cubic_mem_threeResidual P hp)
  have ht0 := highest_commuting_cubic P hp t.toAdd (commute_congr rfl ht.symm hcomm)
  have ht1 : t = 1 := congrArg Multiplicative.ofAdd ht0
  apply Subtype.ext
  exact ht.symm.trans ((congrArg (highestHom P hp) ht1).trans (map_one _))

end
end Triality.Standard.Parabolics.BinaryCentralResidual
