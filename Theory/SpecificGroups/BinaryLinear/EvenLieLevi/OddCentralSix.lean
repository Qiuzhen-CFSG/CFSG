module

public import Theory.SpecificGroups.BinaryLinear.EvenLieLevi
import all Theory.SpecificGroups.BinaryLinear.EvenLieLevi
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Theory.GroupTheory.TwoLocalSurjective

/-!
# Odd central covers of PSL₆(2) are not quasithin

Three actual SL₂(2) factors embed in the stabilizer of a two-space. Their
cubic generators lift through an odd central kernel as products of lifted
involutions. Independent inversion forces the lifted generators to commute,
so the lifted two-local subgroup contains an elementary abelian subgroup of
order 27. This contradicts quasithinness in the original covering group.

The internal import reuses the cubic matrix marking of `EvenLieLevi`;
all public conclusions concern the literal PSL₆(2) quotient.
Source: Aschbacher--Smith A.2.18, printed p.40, Case II linear branch.
-/

noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.EvenLieLevi.OddCentralSix
open BinaryLinear.SmallParabolicLevi BinaryLinear.OuterCyclic
private abbrev U := Space 2
private abbrev V := U × U
private abbrev P := parabolic (leftSpace U V)
private abbrev D := Fin 3 → SL(2,ZMod 2)
private abbrev C := Fin 3 → Multiplicative (ZMod 3)

private noncomputable def doubleLinear : (SL(2,ZMod 2) × SL(2,ZMod 2)) →* BinaryLinear.GL V :=
  (parabolic (leftSpace U U)).subtype.comp
    ((embedding U U).comp ((slEquivLinear 2).prodCongr (slEquivLinear 2)).toMonoidHom)

private theorem doubleLinear_injective : Function.Injective doubleLinear :=
  (Subgroup.subtype_injective _).comp ((embedding_injective U U).comp
    ((slEquivLinear 2).prodCongr (slEquivLinear 2)).injective)

private noncomputable def factorLinear : (SL(2,ZMod 2) × (SL(2,ZMod 2) × SL(2,ZMod 2))) →*
    BinaryLinear.GL U × BinaryLinear.GL V :=
  (slEquivLinear 2).toMonoidHom.prodMap doubleLinear

private theorem factorLinear_injective : Function.Injective factorLinear := by
  intro a b h
  exact Prod.ext ((slEquivLinear 2).injective (congrArg Prod.fst h))
    (doubleLinear_injective (congrArg Prod.snd h))

private def pack : D →* SL(2,ZMod 2) × (SL(2,ZMod 2) × SL(2,ZMod 2)) where
  toFun a := (a 0, a 1, a 2)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem pack_injective : Function.Injective pack := by
  intro a b h
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg (fun x => x.2.1) h
  · exact congrArg (fun x => x.2.2) h

private noncomputable def factors : D →* P := (embedding U V).comp (factorLinear.comp pack)
private theorem factors_injective : Function.Injective factors :=
  (embedding_injective U V).comp (factorLinear_injective.comp pack_injective)

private def firstSmall : SL(2,ZMod 2) := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) 1
private def secondSmall : SL(2,ZMod 2) := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1

private def firstD (i : Fin 3) : D := Pi.mulSingle i firstSmall
private def secondD (i : Fin 3) : D := Pi.mulSingle i secondSmall
private def gammaD (i : Fin 3) : D := firstD i * secondD i

private theorem firstD_square : ∀ i, firstD i ^ 2 = 1 := by decide
private theorem secondD_square : ∀ i, secondD i ^ 2 = 1 := by decide
private theorem gammaD_cube : ∀ i, gammaD i ^ 3 = 1 := by decide
private theorem gammaD_commute : ∀ i j, Commute (gammaD i) (gammaD j) := by
  change ∀ i j, gammaD i * gammaD j = gammaD j * gammaD i
  decide
private theorem firstD_inverts : ∀ i, firstD i * gammaD i * (firstD i)⁻¹ = (gammaD i)⁻¹ := by decide
private theorem firstD_commutes : ∀ i j, i ≠ j → Commute (firstD i) (gammaD j) := by
  change ∀ i j, i ≠ j → firstD i * gammaD j = gammaD j * firstD i
  decide

private def tupleCubic : C →* D where
  toFun a i := cubicHom (a i)
  map_one' := by funext i; exact map_one _
  map_mul' a b := by funext i; exact map_mul _ _ _

private theorem tupleCubic_injective : Function.Injective tupleCubic := by
  have hc : Function.Injective cubicHom := by decide
  intro a b h
  funext i
  exact hc (congrFun h i)

private theorem cubicSmall_power : ∀ a : Multiplicative (ZMod 3),
    (firstSmall * secondSmall) ^ a.toAdd.val = cubicHom a := by decide

private theorem tupleCubic_product (a : C) :
    gammaD 0 ^ (a 0).toAdd.val * (gammaD 1 ^ (a 1).toAdd.val *
      gammaD 2 ^ (a 2).toAdd.val) = tupleCubic a := by
  funext i
  fin_cases i <;>
    simp [gammaD, firstD, secondD, tupleCubic,
      cubicSmall_power]

private noncomputable def originalEmbedding : C →* P := factors.comp tupleCubic

private theorem originalEmbedding_injective : Function.Injective originalEmbedding :=
  factors_injective.comp tupleCubic_injective

section Lift
variable {L : Type*} [Group L] (q : L →* P) (hq : Function.Surjective q)
  (hk : q.ker ≤ center L) (ho : Odd (Nat.card q.ker))

private noncomputable def liftedFirst (i : Fin 3) : L :=
  OddCentralLifting.involutionLift q hq ho (factors (firstD i))
    (by rw [← map_pow, firstD_square, map_one])
private noncomputable def liftedSecond (i : Fin 3) : L :=
  OddCentralLifting.involutionLift q hq ho (factors (secondD i))
    (by rw [← map_pow, secondD_square, map_one])
private noncomputable def liftedGenerator (i : Fin 3) : L :=
  liftedFirst q hq ho i * liftedSecond q hq ho i

private theorem liftedGenerator_image (i : Fin 3) :
    q (liftedGenerator q hq ho i) = factors (gammaD i) := by
  rw [liftedGenerator, map_mul, liftedFirst, liftedSecond,
    OddCentralLifting.involutionLift_image, OddCentralLifting.involutionLift_image,
    ← map_mul]
  rfl

include hk in
private theorem liftedGenerator_cube (i : Fin 3) : liftedGenerator q hq ho i ^ 3 = 1 := by
  apply OddCentralLifting.involution_product_relation q ho hk
    (OddCentralLifting.involutionLift_square q hq ho _ _)
    (OddCentralLifting.involutionLift_square q hq ho _ _)
  rw [← map_mul]
  change q (liftedGenerator q hq ho i) ^ 3 = 1
  rw [liftedGenerator_image, ← map_pow, gammaD_cube, map_one]

include hk in
private theorem liftedGenerators_commute (i j : Fin 3) :
    Commute (liftedGenerator q hq ho i) (liftedGenerator q hq ho j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · apply CentralExtension.commute_lifts_of_partial_inversion q hq hk
      (factors (gammaD i)) (factors (gammaD j)) (factors (firstD i))
      (by decide : Nat.Coprime 3 2)
      (by rw [← map_pow, gammaD_cube, map_one])
      ((gammaD_commute i j).map _) _ ((firstD_commutes i j hij).map _)
      _ _ (liftedGenerator_image _ _ _ _) (liftedGenerator_image _ _ _ _)
    simpa only [map_mul, map_inv] using congrArg factors (firstD_inverts i)

private noncomputable def liftedCycle (i : Fin 3) : Multiplicative (ZMod 3) →* L where
  toFun a := liftedGenerator q hq ho i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change liftedGenerator q hq ho i ^ (a.toAdd+b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (liftedGenerator_cube q hq hk ho i)

private theorem liftedCycles_commute : Pairwise (fun i j => ∀ a b,
    Commute (liftedCycle q hq hk ho i a) (liftedCycle q hq hk ho j b)) := by
  intro i j _ a b
  exact (liftedGenerators_commute q hq hk ho i j).pow_pow a.toAdd.val b.toAdd.val

private noncomputable def liftedEmbedding : C →* L :=
  MonoidHom.noncommPiCoprod (liftedCycle q hq hk ho) (liftedCycles_commute q hq hk ho)

private theorem liftedEmbedding_image (a : C) :
    q (liftedEmbedding q hq hk ho a) = originalEmbedding a := by
  rw [liftedEmbedding, MonoidHom.noncommPiCoprod_apply]
  have he : (Finset.univ : Finset (Fin 3)) = [0,1,2].toFinset := by decide
  rw [he, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change q (liftedGenerator q hq ho 0 ^ (a 0).toAdd.val *
    (liftedGenerator q hq ho 1 ^ (a 1).toAdd.val *
      liftedGenerator q hq ho 2 ^ (a 2).toAdd.val)) = factors (tupleCubic a)
  rw [← tupleCubic_product]
  simp only [map_mul, map_pow, liftedGenerator_image]

private theorem liftedEmbedding_injective : Function.Injective (liftedEmbedding q hq hk ho) := by
  intro a b hab
  apply originalEmbedding_injective
  rw [← liftedEmbedding_image q hq hk ho a, ← liftedEmbedding_image q hq hk ho b, hab]

include q hq hk ho in
private theorem lifted_rank_three [Finite L] : 3 ≤ primeRank 3 L := by
  have hp : ∀ a : C, a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  apply primeRank_ge_of_elementary_embedding hp _ (liftedEmbedding q hq hk ho)
    (liftedEmbedding_injective q hq hk ho)
  simp [Nat.card_eq_fintype_card]
end Lift

variable {G : Type*} [Group G] [Finite G]

private theorem not_quasithin_linearSpace_cover (q : G →* BinaryLinear.GL (U × V))
    (hq : Function.Surjective q) (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker)) :
    ¬ IsQuasithin G := by
  intro hG
  obtain ⟨L, hL, _, φ, hφ, hmark⟩ :=
    (parabolic_isTwoLocal U V).exists_surjective_of_surjective q hq
  have himage (x : L) (hx : φ x = 1) : q (x : G) = 1 := by
    rw [← hmark x, hx]
    rfl
  have hcentral : φ.ker ≤ center L := by
    intro x hx
    have hc := hk (himage x hx)
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp hc y
  let kmap : φ.ker →* q.ker :=
    { toFun := fun x => ⟨x.val.val, himage x.val x.prop⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hki : Function.Injective kmap := by
    intro x y h
    have hv : ((x.val : L) : G) = ((y.val : L) : G) :=
      congrArg (fun z : q.ker => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  have hodd : Odd (Nat.card φ.ker) := ho.of_dvd_nat (Subgroup.card_dvd_of_injective kmap hki)
  have hlo := lifted_rank_three φ hφ hcentral hodd
  have hhi := isQuasithin_iff_twoLocal.mp hG L hL 3 (by decide) (by decide)
  omega

private noncomputable def sixCoordinates : PSL(6,ZMod 2) ≃* BinaryLinear.GL (U × V) :=
  (projectiveCoordinates 4).trans
    (linearGroupCongr ((LinearEquiv.refl (ZMod 2) U).prodCongr (splitCoordinates 2)))

/-- An odd central cover of the literal binary PSL₆ model is not quasithin. -/
public theorem not_quasithin_of_odd_central_cover (q : G →* PSL(6,ZMod 2))
    (hq : Function.Surjective q) (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker)) :
    ¬ IsQuasithin G := by
  let f := sixCoordinates.toMonoidHom.comp q
  have hf : Function.Surjective f := sixCoordinates.surjective.comp hq
  have he : f.ker = q.ker := MonoidHom.ker_comp_of_injective q _ sixCoordinates.injective
  exact not_quasithin_linearSpace_cover f hf (by rwa [he]) (by rwa [he])

/-- The same obstruction on the original group's actual central quotient. -/
public theorem not_quasithin_of_odd_center
    (ho : Odd (Nat.card (center G))) (e : G ⧸ center G ≃* PSL(6,ZMod 2)) :
    ¬ IsQuasithin G := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have he : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact not_quasithin_of_odd_central_cover q hq (by rw [he]) (by rwa [he])

end BinaryLinear.EvenLieLevi.OddCentralSix
