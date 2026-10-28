module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SL2G2
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree

/-!
# Complete nonsplit SL₂ and G₂ branches of B.5.13

Clause (5) of the corrected B.5.1 conclusion supplies the fixed supplement:
its other natural rows cannot coincide with SL₂ or G₂. Natural-module
dimensions and the actual actor orders separate these markings. In the
symplectic comparison, equal dimensions identify a common order factor;
cancelling it forces incompatible field degrees. The binary derived G₂
endpoint has dimension six and order 6048, separating it from A₈.

A nontrivial perfect SL₂ actor excludes the field of order two by its
solvable S₃ model. The central-cover bounds therefore apply to the original
representation's literal dual with no supplementary geometric assumption.

Source: Aschbacher–Smith B.5.1(5) and B.5.13, printed pp.102–103 and 110–112,
combined manuscript (1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem field_degree (F : BinaryField) : Module.finrank (ZMod 2) F.Carrier = F.degree := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod,F.card_eq] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

private theorem linear_dimension (F : BinaryField) (d : ℕ)
    (e : ActionEquiv ρ (linearNatural F d)) : Module.finrank (ZMod 2) V = d * F.degree := by
  rw [e.linearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [field_degree]

private theorem sp_dimension (F : BinaryField)
    (e : ActionEquiv ρ (binarySymplectic F)) : Module.finrank (ZMod 2) V = 4 * F.degree := by
  rw [e.linearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [field_degree]

private theorem g2_dimension (F : BinaryField)
    (e : ActionEquiv ρ (binaryG2 F)) : Module.finrank (ZMod 2) V = 6 * F.degree := by
  rw [e.linearEquiv.finrank_eq, ← Module.finrank_mul_finrank (ZMod 2) F.Carrier
    (Atlas.G2.Natural.Space F.Carrier), field_degree, Atlas.G2.Natural.finrank_space]
  omega

private theorem g2_two_dimension
    (e : ActionEquiv ρ (g2DerivedNatural (ZMod 2))) : Module.finrank (ZMod 2) V = 6 := by
  rw [e.linearEquiv.finrank_eq, Atlas.G2.Natural.finrank_space]

private theorem alt_dimension (n : ℕ) (hn : n = 6 ∨ n = 8)
    (e : ActionEquiv ρ (alternatingNatural n)) : Module.finrank (ZMod 2) V = n - 2 := by
  rw [e.linearEquiv.finrank_eq]
  rcases hn with rfl | rfl <;> exact BinaryPermutation.finrank_natural_even _ (by decide)

private theorem linearTwo_sp_disjoint (F K : BinaryField)
    (e : ActionEquiv ρ (linearNatural F 2)) (f : ActionEquiv ρ (binarySymplectic K)) : False := by
  have hd : F.degree = 2 * K.degree := by have := linear_dimension F 2 e; have := sp_dimension K f; omega
  have hc := Nat.card_congr (e.groupEquiv.symm.trans f.groupEquiv).toEquiv
  rw [Atlas.card_sl_two, Theory.SpecificGroups.SymplecticFour.card_sp,
    F.card_eq, K.card_eq, hd, Nat.mul_comm 2 K.degree, pow_mul] at hc
  let q := 2 ^ K.degree
  have hq : 2 ≤ q := Nat.le_self_pow (Nat.ne_of_gt K.degree_pos) _
  have h4 : 16 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have hp : 0 < q ^ 4 - 1 := by omega
  change q^2 * ((q^2)^2-1) = q^4*(q^2-1)*(q^4-1) at hc
  rw [show (q^2)^2 = q^4 by ring] at hc
  have hc' : q^2 * (q^4-1) = (q^2 * (q^2*(q^2-1))) * (q^4-1) := by
    convert hc using 1; ring
  have he := Nat.eq_of_mul_eq_mul_right hp hc'
  have he' : 1 = q^2*(q^2-1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<q^2 by positivity)
    simpa using he
  have hl : 4 ≤ q^2 := by nlinarith
  have hs : 3 ≤ q^2-1 := by omega
  nlinarith

private theorem g2_sp_disjoint (F K : BinaryField)
    (e : ActionEquiv ρ (binaryG2 F)) (f : ActionEquiv ρ (binarySymplectic K)) : False := by
  have hd : 6 * F.degree = 4 * K.degree := by have := g2_dimension F e; have := sp_dimension K f; omega
  have hc := Nat.card_congr (e.groupEquiv.symm.trans f.groupEquiv).toEquiv
  rw [Atlas.G2.card_Model, Theory.SpecificGroups.SymplecticFour.card_sp,
    F.card_eq, K.card_eq] at hc
  have hp : (2 ^ F.degree)^6 = (2 ^ K.degree)^4 := by
    rw [← pow_mul, ← pow_mul]; congr 1; omega
  rw [hp] at hc
  have hc' : (2 ^ K.degree)^4 * ((2 ^ K.degree)^4-1) * ((2 ^ F.degree)^2-1) =
      (2 ^ K.degree)^4 * ((2 ^ K.degree)^4-1) * ((2 ^ K.degree)^2-1) := by
    convert hc using 1; ring
  have hK : 2 ≤ 2 ^ K.degree := Nat.le_self_pow (Nat.ne_of_gt K.degree_pos) _
  have hF : 2 ≤ 2 ^ F.degree := Nat.le_self_pow (Nat.ne_of_gt F.degree_pos) _
  have h4 : 16 ≤ (2 ^ K.degree)^4 := Nat.pow_le_pow_left hK 4
  have ht : 1 < (2 ^ K.degree)^4 := by omega
  have hz : 0 < (2 ^ K.degree)^4 * ((2 ^ K.degree)^4-1) := Nat.mul_pos (by omega) (by omega)
  have hs := Nat.eq_of_mul_eq_mul_left hz hc'
  have hf2 : 1 ≤ (2 ^ F.degree)^2 := Nat.succ_le_of_lt (by positivity)
  have hk2 : 1 ≤ (2 ^ K.degree)^2 := Nat.succ_le_of_lt (by positivity)
  have hs2 : (2 ^ F.degree)^2 = (2 ^ K.degree)^2 := by omega
  have he : F.degree = K.degree := by
    rw [← pow_mul, ← pow_mul] at hs2
    have := Nat.pow_right_injective (by decide : 1 < 2) hs2
    omega
  have := F.degree_pos
  omega

private theorem linearTwo_not_supplement (F : BinaryField)
    (e : ActionEquiv ρ (linearNatural F 2)) : ¬ SupplementNatural ρ := by
  intro hs
  cases hs with
  | symplectic K h => exact linearTwo_sp_disjoint F K e h.some
  | alternatingSix h =>
    have hd : F.degree = 2 := by
      have := linear_dimension F 2 e; have := alt_dimension 6 (Or.inl rfl) h.some; omega
    have hc := Nat.card_congr (e.groupEquiv.symm.trans h.some.groupEquiv).toEquiv
    rw [Atlas.card_sl_two, F.card_eq, hd, nat_card_alternatingGroup] at hc
    norm_num at hc
  | alternatingEight h =>
    have hd : F.degree = 3 := by
      have := linear_dimension F 2 e; have := alt_dimension 8 (Or.inr rfl) h.some; omega
    have hc := Nat.card_congr (e.groupEquiv.symm.trans h.some.groupEquiv).toEquiv
    rw [Atlas.card_sl_two, F.card_eq, hd, nat_card_alternatingGroup] at hc
    norm_num at hc
  | linearThree h =>
    have hd := linear_dimension F 2 e
    have hd' := linear_dimension BinaryField.two 3 h.some
    change Module.finrank (ZMod 2) V = 3*1 at hd'
    omega

private theorem g2_not_supplement (F : BinaryField)
    (e : ActionEquiv ρ (binaryG2 F)) : ¬ SupplementNatural ρ := by
  intro hs
  cases hs with
  | symplectic K h => exact g2_sp_disjoint F K e h.some
  | alternatingSix h =>
    have := g2_dimension F e; have := alt_dimension 6 (Or.inl rfl) h.some; omega
  | alternatingEight h =>
    have hd : F.degree = 1 := by
      have := g2_dimension F e; have := alt_dimension 8 (Or.inr rfl) h.some; omega
    have hc := Nat.card_congr (e.groupEquiv.symm.trans h.some.groupEquiv).toEquiv
    rw [Atlas.G2.card_Model, F.card_eq, hd, nat_card_alternatingGroup] at hc
    norm_num at hc
  | linearThree h =>
    have hd := g2_dimension F e
    have hd' := linear_dimension BinaryField.two 3 h.some
    change Module.finrank (ZMod 2) V = 3*1 at hd'
    omega

private theorem derivedG2_not_supplement
    (e : ActionEquiv ρ (g2DerivedNatural (ZMod 2))) : ¬ SupplementNatural ρ := by
  intro hs
  cases hs with
  | symplectic K h => have := g2_two_dimension e; have := sp_dimension K h.some; omega
  | alternatingSix h =>
    have := g2_two_dimension e; have := alt_dimension 6 (Or.inl rfl) h.some; omega
  | alternatingEight h =>
    have hc := Nat.card_congr (e.groupEquiv.symm.trans h.some.groupEquiv).toEquiv
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp), nat_card_alternatingGroup] at hc
    norm_num at hc
  | linearThree h =>
    have hd := g2_two_dimension e
    have hd' := linear_dimension BinaryField.two 3 h.some
    change Module.finrank (ZMod 2) V = 3*1 at hd'
    omega

/-- A nontrivial perfect natural SL₂ actor excludes the binary prime field. -/
theorem linearTwo_field_large [Group.IsPerfect D] [Nontrivial D]
    (F : BinaryField) (e : ActionEquiv ρ (linearNatural F 2)) : 1 < F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  let c := e.groupEquiv.trans
    ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable D
    (Group.isSolvable_of_surjective (f := c.symm.toMonoidHom) c.symm.surjective)

variable [Finite D] [FiniteDimensional (ZMod 2) V] {L : Subgroup D}

/-- The original nonsplit SL₂ row has quadratic ratio at most two. -/
theorem quadraticRatio_le_two_of_linearTwo_source [Group.IsPerfect L] [Nontrivial L]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField) (he : IsLinearNatural (c.sectionData.action.comp L.subtype) F 2) :
    quadraticRatio ρ ≤ 2 := by
  have hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤ := by
    rcases c.clause_five with hs | hx
    · exact hs
    · exact False.elim (linearTwo_not_supplement F he.some hx.2.1)
  exact quadraticRatio_le_two_of_linearTwo_source_supplement ρ c hn F
    (linearTwo_field_large F he.some) he hs

/-- The original nonsplit full G₂ row has quadratic ratio at most two. -/
theorem quadraticRatio_le_two_of_g2_source [Group.IsPerfect L]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField)
    (he : Nonempty (ActionEquiv (c.sectionData.action.comp L.subtype) (binaryG2 F))) :
    quadraticRatio ρ ≤ 2 := by
  have hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤ := by
    rcases c.clause_five with hs | hx
    · exact hs
    · exact False.elim (g2_not_supplement F he.some hx.2.1)
  exact quadraticRatio_le_two_of_g2_source_supplement ρ c hn F he hs

/-- The original nonsplit binary derived G₂ row has quadratic ratio at most two. -/
theorem quadraticRatio_le_two_of_derivedG2_source
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (he : Nonempty (ActionEquiv (c.sectionData.action.comp L.subtype)
      (g2DerivedNatural (ZMod 2)))) :
    quadraticRatio ρ ≤ 2 := by
  have hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤ := by
    rcases c.clause_five with hs | hx
    · exact hs
    · exact False.elim (derivedG2_not_supplement he.some hx.2.1)
  exact quadraticRatio_le_two_of_derivedG2_source_supplement ρ c hn he hs

end CFSG.Quasithin.ChapterB.SourceB513
