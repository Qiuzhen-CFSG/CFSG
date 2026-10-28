module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.SubgroupConjugation

/-!
# Cubic fixed points under an extraspecial action

Let P be extraspecial at three and let X be an elementary abelian subgroup
of order nine containing Z(P). A cubic E in X distinct from Z(P) has the
following detection property: if Z(P) centralizes C_U(E), it centralizes U
for every finite two-group U acted on by P.

Coprime fixed-point generation reduces to the fixed group of each nonzero
actor in X. A central actor generates Z(P). Every other actor is conjugate
inside P to a nonidentity element of E, since noncentral central cosets of
an extraspecial group are conjugacy classes. Centrality of Z(P) transports
the assumed fixed-point containment to every generating fixed group.
The ambient corollary retains the literal subgroup commutator and does not
require U to be abelian or the action of P to be faithful.

Source application: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.763, the extraspecial Sylow-three argument for
1 ≠ [C_U(X₁),X_K]. Construction of that marked Sylow group is separate.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace IsExtraspecial
variable {P U : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [Group U] [Finite U] [MulDistribMulAction P U]

omit [Finite P] [IsExtraspecial 3 P] [Finite U] in
private theorem fixed_by_prime_generator (E : Subgroup P) (hE : Nat.card E = 3)
    {e : P} (he : e ∈ E) (hne : e ≠ 1) {u : U} (hfix : e • u = u) :
    u ∈ FixedPoints.subgroup E U := by
  have hg : (⟨e,he⟩ : E) ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hgen := zpowers_eq_top_of_prime_card hE hg
  have hh : zpowers (⟨e,he⟩ : E) ≤ MulAction.stabilizer E u := zpowers_le.mpr hfix
  intro x
  exact hh (hgen.ge (mem_top x))

private theorem noncentral_element_of_complement
    (E : Subgroup P) (hE : Nat.card E = 3) (hEZ : E ≠ center P)
    {e : P} (he : e ∈ E) (hne : e ≠ 1) : e ∉ center P := by
  intro hz
  apply hEZ
  apply eq_of_le_of_card_ge ?_ (by rw [hE,center_order_p 3 P])
  intro x hx
  have hgen := zpowers_eq_top_of_prime_card hE
    (show (⟨e,he⟩ : E) ≠ 1 from fun h => hne (congrArg Subtype.val h))
  have hz' : zpowers (⟨e,he⟩ : E) ≤ (center P).comap E.subtype := zpowers_le.mpr hz
  exact hz' (hgen.ge (mem_top ⟨x,hx⟩))

/-- Centralization on one noncentral cubic fixed group detects the whole two-group. -/
theorem center_fixed_eq_top_of_cubic_fixed
    (hU : IsPGroup 2 U) (A E : Subgroup P) [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) (hE : Nat.card E = 3)
    (hEA : E ≤ A) (hZA : center P ≤ A) (hEZ : E ≠ center P)
    (hfix : FixedPoints.subgroup E U ≤ FixedPoints.subgroup (center P) U) :
    FixedPoints.subgroup (center P) U = ⊤ := by
  have hdis : Disjoint E (center P) := by
    apply disjoint_def.mpr
    intro e he hz
    by_contra hn
    exact noncentral_element_of_complement E hE hEZ he hn hz
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint E (center P)
    ((center_le_centralizer E).trans (Subgroup.centralizer_le_normalizer _)) hdis
  have hsplit : E ⊔ center P = A := eq_of_le_of_card_ge (sup_le hEA hZA)
    (by rw [hc,hE,center_order_p 3 P,hA])
  let : Fact (IsPGroup 2 U) := ⟨hU⟩
  have hcop : Nat.Coprime (Nat.card A) 2 := by rw [hA]; decide
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := U) (A := A) (q := 2) hcop
  have hncyc : ¬ IsCyclic A :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 3) (by simpa using hA)
  apply top_unique
  rw [←hgen]
  apply iSup₂_le
  intro B hB u hu
  have hne : B ≠ ⊥ := by
    intro hb
    subst B
    let := hB
    exact hncyc (isCyclic_of_surjective (QuotientGroup.quotientBot (G := A))
      (QuotientGroup.quotientBot (G := A)).surjective)
  obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hbP : ((b : A) : P) ≠ 1 := fun h => hb (Subtype.ext (Subtype.ext h))
  have hbu : ((b : A) : P) • u = u := hu b
  by_cases hbZ : ((b : A) : P) ∈ center P
  · exact fixed_by_prime_generator (center P) (center_order_p 3 P) hbZ hbP hbu
  have hbA : ((b : A) : P) ∈ E ⊔ center P := hsplit.ge (b : A).property
  rw [mem_sup_of_normal_right] at hbA
  obtain ⟨e,he,z,hz,heb⟩ := hbA
  have heZ : e ∉ center P := by
    intro hh
    exact hbZ (heb ▸ (center P).mul_mem hh hz)
  have he1 : e ≠ 1 := fun he1 => heZ (he1 ▸ (center P).one_mem)
  have hcoset : QuotientGroup.mk' (center P) e = QuotientGroup.mk' (center P) ((b : A) : P) := by
    have hzq : QuotientGroup.mk' (center P) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [←heb,map_mul,hzq,mul_one]
  obtain ⟨g,hg⟩ := isConj_iff.mp (isConj_of_center_quotient_eq_prime (p := 3) heZ hcoset)
  have hefix : e • (g⁻¹ • u) = g⁻¹ • u := by
    have hh := congrArg (fun v : U => g⁻¹ • v) hbu
    rw [←hg] at hh
    have heq : g⁻¹ * (g * e * g⁻¹) = e * g⁻¹ := by group
    simpa only [←mul_smul,heq] using hh
  have hc := hfix (fixed_by_prime_generator E hE he he1 hefix)
  intro z
  have hcomm : (z : P) * g = g * z := (mem_center_iff.mp z.property g).symm
  have hzfix : (z : P) • (g⁻¹ • u) = g⁻¹ • u := hc z
  have hh := congrArg (fun v : U => g • v) hzfix
  have heq : g * (z : P) * g⁻¹ = z := by
    rw [←hcomm,mul_assoc,mul_inv_cancel,mul_one]
  change (z : P) • u = u
  simpa only [←mul_smul,←mul_assoc,heq,mul_inv_cancel,one_smul] using hh

end IsExtraspecial

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Nontrivial center action is visible on the fixed group of the marked cubic. -/
theorem extraspecial_cubic_fixed_commutator_ne_bot
    (P X E U : Subgroup G) [IsExtraspecial 3 P] [IsElementaryAbelian 3 X]
    (hU : IsPGroup 2 U) (hPU : P ≤ normalizer (U : Set G))
    (hXP : X ≤ P) (hEX : E ≤ X) (hX : Nat.card X = 9) (hE : Nat.card E = 3)
    (hZX : (center P).map P.subtype ≤ X) (hEZ : E ≠ (center P).map P.subtype)
    (hmove : ¬ (center P).map P.subtype ≤ centralizer (U : Set G)) :
    ⁅U ⊓ centralizer (E : Set G),(center P).map P.subtype⁆ ≠ ⊥ := by
  intro hzero
  let : Normalizes P U := ⟨hPU⟩
  let A := X.subgroupOf P
  let B := E.subgroupOf P
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hXP
  have hEP := hEX.trans hXP
  have hfixed : FixedPoints.subgroup B U ≤ FixedPoints.subgroup (center P) U := by
    intro u hu z
    have huE : (u : G) ∈ centralizer (E : Set G) := by
      intro e he
      have hh := congrArg Subtype.val (hu (⟨⟨e,hEP he⟩,he⟩ : B))
      change e * (u : G) * e⁻¹ = (u : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hh := (commutator_eq_bot_iff_le_centralizer.mp hzero) ⟨u.property,huE⟩
      (z : G) (mem_map_of_mem P.subtype z.property)
    apply Subtype.ext
    change (z : G) * (u : G) * (z : G)⁻¹ = (u : G)
    rw [hh,mul_inv_cancel_right]
  have htop := IsExtraspecial.center_fixed_eq_top_of_cubic_fixed hU A B
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv]; exact hX)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv]; exact hE)
    (fun e he => hEX he) (fun z hz => hZX (mem_map_of_mem P.subtype hz))
    (by
      intro he
      apply hEZ
      simpa only [B,map_subgroupOf_eq_of_le hEP] using congrArg (map P.subtype) he)
    hfixed
  apply hmove
  rintro z ⟨z,hz,rfl⟩ u hu
  have hh := congrArg Subtype.val
    (htop.ge (mem_top (⟨u,hu⟩ : U)) (⟨z,hz⟩ : center P))
  change (z : G) * u * (z : G)⁻¹ = u at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end Subgroup
