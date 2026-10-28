module
public import Theory.GroupTheory.CoprimeRealPrimeLift
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.InvertedSeven
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# The remaining seven-centralizer certificate for J4

A centralizer of order 840 forces the conjugation image of its cyclic
seven-subgroup to have order three. Indeed its order divides six, while
Sylow's normalizer congruence modulo 49 and the certified J4 order leave
only three. Such an element cannot be conjugate to its inverse.

The prime-seven part of the native J4 order is seven, so Sylow conjugacy
transfers a centralizer count at the existing ATLAS matrix word to every
seven-element. Both full binary automizers contain a real seven, which
lifts through their two-core quotient. Thus this one count suffices to
exclude these sections, without full Sylow placement or a stronger action
hypothesis.

The centralizer count remains an explicit unproved premise. This module
does not assert nonreality or the J4 section exclusion unconditionally.
Source: ATLAS J4 classes 7A--7B (centralizer order 840),
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ (consulted 20 October 2026),
and Aschbacher--Smith 12.1.1, printed p.788. The native matrix word and
kernel-checked order certificate retain their original imported attribution.
-/

open Subgroup
public noncomputable section
namespace Janko4.SevenNormalizers
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem normalizer_image_card (hG : Nat.card G = 86775571046077562880)
    (x : G) (hx : orderOf x = 7)
    (hc : Nat.card (centralizer (zpowers x : Set G)) = 840) :
    Nat.card (zpowers x).normalizerMonoidHom.range = 3 := by
  let P := zpowers x
  have hk : Nat.card P.normalizerMonoidHom.ker = 840 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv]
    exact hc
  have hd : Nat.card P.normalizerMonoidHom.range ∣ 6 := by
    have h := P.normalizerMonoidHom.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut,Nat.card_zpowers,hx,show Nat.totient 7 = 6 from by decide] at h
  have hm := P.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk] at hm
  have hn := Sylow.card_normalizer_modEq_card (p := 7) (n := 1)
    (H := P) (by rw [Nat.card_zpowers,hx,pow_one])
  rw [←hm,hG] at hn
  have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
  generalize Nat.card P.normalizerMonoidHom.range = k at *
  norm_num [Nat.ModEq, Nat.mul_mod] at hn
  omega

private theorem not_real (hG : Nat.card G = 86775571046077562880)
    (x : G) (hx : orderOf x = 7)
    (hc : Nat.card (centralizer (zpowers x : Set G)) = 840) : ¬ IsConj x x⁻¹ := by
  intro hr
  obtain ⟨a,ha⟩ := isConj_iff.mp hr
  let P := zpowers x
  have haN : a ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (a*x*a⁻¹) = zpowers x
    rw [ha,zpowers_inv]
  let α := P.normalizerMonoidHom ⟨a,haN⟩
  have he (z : P) : α z = z⁻¹ := by
    apply Subtype.ext
    obtain ⟨k,hk⟩ := z.property
    change a * (z : G) * a⁻¹ = (z : G)⁻¹
    rw [←hk]
    change MulAut.conj a (x ^ k) = (x ^ k)⁻¹
    rw [map_zpow]
    change (a*x*a⁻¹)^k = (x^k)⁻¹
    rw [ha,inv_zpow]
  have hs : α^2 = 1 := by
    rw [pow_two]
    ext z
    rw [MulAut.mul_apply,he,he,inv_inv]
    rfl
  have hne : α ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val (he (⟨x,mem_zpowers x⟩ : P))
    rw [h] at hh
    change x = x⁻¹ at hh
    have h2 : x^2 = 1 := by
      calc
        x^2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (x * ·) hh
        _ = 1 := mul_inv_cancel x
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at hd
    norm_num at hd
  let β : P.normalizerMonoidHom.range := ⟨α,⟨⟨a,haN⟩,rfl⟩⟩
  have ho : orderOf β = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hs hne
  have hd := orderOf_dvd_natCard β
  rw [ho,normalizer_image_card hG x hx hc] at hd
  norm_num at hd
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The already certified seventh-order power of the native 42-word. -/
@[expose] def representative : Janko4.Model :=
  Simplicity.primeRepresentative (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four) 4

/-- Its order follows from the existing packed matrix products. -/
theorem representative_order : orderOf representative = 7 :=
  Simplicity.orderOf_primeRepresentative_seven matrixA_mul_self matrixB_pow_four

omit [Finite G] in
private theorem centralizer_map_equiv (Q : Subgroup G) (e : G ≃* G) :
    centralizer (Q.map e.toMonoidHom : Set G) =
      (centralizer (Q : Set G)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro q hq
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e q) (mem_map_of_mem _ hq)
  · exact map_centralizer_le_centralizer_image _ _

/-- One concrete centralizer count controls every element of order seven.
The count is an explicit certificate obligation, not an asserted model fact. -/
theorem not_real_of_representative_centralizer_card
    (hc : Nat.card (centralizer (zpowers representative : Set Janko4.Model)) = 840)
    (x : Janko4.Model) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  have hs : ¬ 7^2 ∣ Nat.card Janko4.Model := by rw [Cardinality.model_card]; norm_num
  obtain ⟨k,g,he⟩ := Simplicity.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 7) hs hx representative_order
  have hle : zpowers representative ≤ (zpowers x).map (MulAut.conj g).toMonoidHom := by
    apply zpowers_le.mpr
    exact ⟨x^k,pow_mem (mem_zpowers x) k,he.symm⟩
  have heq : zpowers representative = (zpowers x).map (MulAut.conj g).toMonoidHom :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective,Nat.card_zpowers,Nat.card_zpowers,
        representative_order,hx])
  have hcx : Nat.card (centralizer (zpowers x : Set Janko4.Model)) = 840 := by
    rw [heq,centralizer_map_equiv,card_map_of_injective (MulAut.conj g).injective] at hc
    exact hc
  exact not_real Cardinality.model_card x hx hcx

/-- A full binary three- or four-dimensional automizer quotient in a J4
subgroup would lift its real seven. The only model premise is the literal
centralizer count at the certified representative. -/
theorem no_binary_automizer_section_of_representative_centralizer_card
    (hc : Nat.card (centralizer (zpowers representative : Set Janko4.Model)) = 840)
    (n : ℕ) (hn : n = 3 ∨ n = 4) (H : Subgroup Janko4.Model)
    (e : (H ⧸ pCore 2 H) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : False := by
  obtain ⟨y,hy,hr⟩ := BinaryLinear.OuterCyclic.aut_binary_real_seven n hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 7 (Nat.card f.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 7 2).pow_right m
  obtain ⟨x,hx,_,hreal⟩ := f.exists_real_prime_lift hf hk y hy hr
  apply not_real_of_representative_centralizer_card hc (x : Janko4.Model)
    (by rw [Subgroup.orderOf_coe]; exact hx)
  obtain ⟨a,ha⟩ := isConj_iff.mp hreal
  exact isConj_iff.mpr ⟨(a : Janko4.Model),congrArg Subtype.val ha⟩
end Janko4.SevenNormalizers
