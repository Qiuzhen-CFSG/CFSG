module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryPrimeDegree.Quotient
public import Theory.SpecificGroups.Janko3.Model.Relations
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeNormalGeneration.NineteenRelation
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations

/-!
# Elementary degree lower bounds for all six pariah central quotients

The actual catalogue carriers have elements of orders 19 (J₁, J₃ and O'N),
37 (J₄), 29 (Ru), and 67 (Ly). Their binary multiplicative orders give degree
bounds 18, 18, 18, 36, 28 and 66 for every faithful action of any finite central
cover. Neither irreducibility nor a classification of the covers is needed.

The O'Nan word is evaluated in the projective carrier. For Lyons, the certified
relations b⁵ = (ab)¹⁴ = 1 show that the 67th-power word is nonidentity: otherwise
ab has both fourteenth and fifteenth power one, contradicting noncommutativity.
All matrix/permutation certificates and their ATLAS attribution are inherited
from the imported model modules; no character-degree table is assumed.

Source application: Aschbacher–Smith B.1.13, printed pp.73–74; the degree
argument is G.7.1(1), printed p.347. These are lower bounds, not the sporadic
FF exclusions or a transcription of Guralnick–Malle Table 2.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Representation.BinaryPrimeDegree

private theorem orderOf_two_nineteen : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem orderOf_two_twentyNine : orderOf (2 : ZMod 29) = 28 := by
  apply (orderOf_eq_iff (by decide : 0 < 28)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem orderOf_two_thirtySeven : orderOf (2 : ZMod 37) = 36 := by
  apply (orderOf_eq_iff (by decide : 0 < 36)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem orderOf_two_sixtySeven : orderOf (2 : ZMod 67) = 66 := by
  apply (orderOf_eq_iff (by decide : 0 < 66)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem onan_word_order :
    orderOf (ONan.generatorA * ONan.generatorB ^ 2) = 19 := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  apply orderOf_eq_prime ONan.generatorAB2_pow_nineteen
  intro h
  have ha : ONan.generatorA = (ONan.generatorB ^ 2)⁻¹ := (eq_inv_iff_mul_eq_one).mpr h
  apply ONan.generatorA_mul_generatorB_ne
  rw [ha]
  exact ((Commute.refl ONan.generatorB).pow_left 2).inv_left.eq

private theorem lyons_word_order : orderOf Lyons.SimplicityCertificate.perfectWord = 67 := by
  let : Fact (Nat.Prime 67) := ⟨by decide⟩
  apply orderOf_eq_prime Lyons.SimplicityCertificate.perfectWord_pow_sixty_seven
  intro h
  have hw : (Lyons.generatorA * Lyons.generatorB) ^ 3 = Lyons.generatorB⁻¹ :=
    (eq_inv_iff_mul_eq_one).mpr h
  have h15 : (Lyons.generatorA * Lyons.generatorB) ^ 15 = 1 := by
    rw [show 15 = 3 * 5 from rfl, pow_mul, hw, inv_pow,
      Lyons.SimplicityCertificate.generatorB_pow_five, inv_one]
  have hab : Lyons.generatorA * Lyons.generatorB = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 14 15)).mp
      ⟨Lyons.SimplicityCertificate.generatorAB_pow_fourteen, h15⟩
  exact Lyons.generators_not_commute (hab.trans (mul_eq_one_comm.mp hab).symm)

variable {L W : Type*} [Group L] [Finite L]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) L W) (hf : Function.Injective σ)

include σ hf

/-- Every faithful binary action of a finite J₁ central cover has degree at least 18. -/
theorem j1_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.j1.Carrier) :
    18 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_nineteen]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ Janko1.orderOf_abab_sq

/-- Every faithful binary action of a finite J₃ central cover has degree at least 18. -/
theorem j3_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.j3.Carrier) :
    18 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_nineteen]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ Sporadic.Janko3.orderOf_ab

/-- Every faithful binary action of a finite J₄ central cover has degree at least 36. -/
theorem j4_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.j4.Carrier) :
    36 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_thirtySeven]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ Janko4.orderOf_a_mul_b

/-- Every faithful binary action of a finite Ru central cover has degree at least 28. -/
theorem ru_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.ru.Carrier) :
    28 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_twentyNine]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ Rudvalis.orderOf_w

/-- This bound uses the projective O'Nan carrier and covers all of its central covers. -/
theorem onan_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.onan.Carrier) :
    18 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_nineteen]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ onan_word_order

/-- Every faithful binary action of a finite Lyons central cover has degree at least 66. -/
theorem ly_degree (e : L ⧸ center L ≃* KnownSimple.SporadicName.ly.Carrier) :
    66 ≤ Module.finrank (ZMod 2) W := by
  rw [← orderOf_two_sixtySeven]
  exact orderOf_le_finrank_of_central_quotient σ hf e (by decide) (by decide)
    _ lyons_word_order

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
