module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.SylowNormalizerCentralQuotient


/-!
# Abelian quotients of centrally covered PSL₃ Borels

For a central surjection onto PSL₃ over a finite binary field, the full
preimage of the diagonal torus is abelian. Choose lifts of its two cyclic
parameter generators. The actual reversal matrix swaps their images, so
centrality makes their commutator both fixed and inverted. Its order divides
two and the odd order of the field-unit group, hence it is trivial. Every
torus lift has the same commutators as a product of powers of these lifts.

The Borel preimage is the normalizer of a Sylow two-subgroup mapping onto
the concrete unitriangular subgroup. That Sylow lies in the Borel preimage's
two-core. The literal Borel factorization therefore makes the abelian torus
preimage surject onto the quotient by the two-core.

Source: Aschbacher--Smith, E.2.2(2b), printed pp.215--216, and the Borel
calculation in 4.4.13, printed pp.623--624 (combined manuscript, 1 March 2004).
The statement concerns arbitrary central covers; it retains the genuine
projective map and requires no multiplier or simplicity classification.
-/

public section

open scoped MatrixGroups commutatorElement
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.LinearThree.CentralBorelQuotient
variable (F : Type*) [Field F]
variable {L : Type*} [Group L]

private theorem reversal_torus [CharP F 2] (d : Fˣ × Fˣ) :
    projection F (reversalSL F) * torusMap F d * (projection F (reversalSL F))⁻¹ =
      torusMap F (d.2, d.1) := by
  have h := congrArg (fun e : MulAut PSL(3,F) => e (torusMap F d))
    (linearConj_toGL F (reversalSL F))
  rw [reversalSL_toGL] at h
  change _ = projection F (reversalSL F) * torusMap F d *
    (projection F (reversalSL F))⁻¹ at h
  rw [← h]
  change projection F (linearConjSL F (reversalGL F) (torusSL F d)) = _
  rw [linearConjSL_reversal_torusSL]
  rfl

variable [Finite F]

private theorem generator_lifts_commute [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (f : L →* PSL(3,F)) (hf : Function.Surjective f) (hk : f.ker ≤ center L)
    (u : Fˣ) (a b : L) (ha : f a = torusMap F (u,1))
    (hb : f b = torusMap F (1,u)) : Commute a b := by
  have hc : ⁅a,b⁆ ∈ center L := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨w, hw⟩ := hf (projection F (reversalSL F))
  -- Conjugation fixes the central commutator but swaps its arguments.
  have hswap : ⁅a,b⁆ = ⁅b,a⁆ := by
    calc
      ⁅a,b⁆ = w * ⁅a,b⁆ * w⁻¹ := by
        rw [mem_center_iff.mp hc w, mul_inv_cancel_right]
      _ = ⁅w*a*w⁻¹, w*b*w⁻¹⁆ := conjugate_commutatorElement a b w
      _ = ⁅b,a⁆ := CentralExtension.commutator_eq_of_image_eq f hk
        (by rw [map_mul, map_mul, map_inv, hw, ha, reversal_torus, hb])
        (by rw [map_mul, map_mul, map_inv, hw, hb, reversal_torus, ha])
  have htwo : ⁅a,b⁆ ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [hswap]
    rw [← commutatorElement_inv, inv_mul_cancel]
  have hpow (k : ℕ) : ⁅a ^ k,b⁆ = ⁅a,b⁆ ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp hc (a ^ k), mul_inv_cancel_right, ih, pow_succ']
  have hord : ⁅a,b⁆ ^ Nat.card Fˣ = 1 := by
    rw [← hpow]
    apply (commutatorElement_eq_one_iff_commute).mpr
    have ha0 : a ^ Nat.card Fˣ ∈ center L := by
      apply hk
      rw [MonoidHom.mem_ker, map_pow, ha, ← map_pow]
      rw [show (u,1) ^ Nat.card Fˣ = (1 : Fˣ × Fˣ) by ext <;> simp, map_one]
    exact (mem_center_iff.mp ha0 b).symm
  apply commutatorElement_eq_one_iff_commute.mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (units_odd F hF).coprime_two_left
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hord)

/-- The full inverse image of the actual diagonal torus is abelian. -/
theorem torus_preimage_isMulCommutative {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (f : L →* PSL(3,F)) (hf : Function.Surjective f) (hk : f.ker ≤ center L) :
    IsMulCommutative ((torus F).comap f) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨a, ha⟩ := hf (torusMap F (u,1))
  obtain ⟨b, hb⟩ := hf (torusMap F (1,u))
  have hab := generator_lifts_commute F hF f hf hk u a b ha hb
  -- Cyclicity supplies literal representatives modulo the central kernel.
  have hrep (x : (torus F).comap f) : ∃ i j : ℤ, f x = f (a ^ i * b ^ j) := by
    obtain ⟨d, hd⟩ := x.property
    obtain ⟨i, hi⟩ := hu d.1
    obtain ⟨j, hj⟩ := hu d.2
    refine ⟨i,j,?_⟩
    rw [map_mul, map_zpow, map_zpow, ha, hb, ← map_zpow, ← map_zpow, ← map_mul]
    rw [← hd]
    congr 1
    ext <;> simp [hi,hj]
  refine IsMulCommutative.of_comm ?_
  intro x y
  apply Subtype.ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  obtain ⟨i,j,hx⟩ := hrep x
  obtain ⟨k,l,hy⟩ := hrep y
  rw [CentralExtension.commutator_eq_of_image_eq f hk hx hy]
  exact (((Commute.refl a).zpow_zpow i k).mul_right (hab.zpow_zpow i l)).mul_left
    ((hab.symm.zpow_zpow j k).mul_right ((Commute.refl b).zpow_zpow j l)) |>.commutator_eq

/-- The central preimage of the split Borel has abelian quotient by its two-core. -/
theorem quotient_isMulCommutative [Finite L] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (f : L →* PSL(3,F))
    (hf : Function.Surjective f) (hk : f.ker ≤ center L) :
    IsMulCommutative (((borel F).comap f) ⧸ pCore 2 ((borel F).comap f)) := by
  let D := (borel F).comap f
  let T := (torus F).comap f
  let q := QuotientGroup.mk' (pCore 2 D)
  let j : T →* D := T.subtype.codRestrict D (fun t => torus_le_borel F t.property)
  let r := q.comp j
  -- The central kernel is already in every Sylow normalizer.
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2
    (unipotentSylow F (by omega) hF)
  have hD : D = normalizer (P : Set L) := by
    dsimp [D]
    rw [← normalizer_unipotent F (by omega) hF]
    have he := P.normalizer_comap_of_central_kernel f hf hk
    rw [hP] at he
    exact he
  have hPD : (P : Subgroup L) ≤ D := hD.symm ▸ (P : Subgroup L).le_normalizer
  have hPN : ((P : Subgroup L).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPD).mpr (le_of_eq hD)
  have hcore : (P : Subgroup L).subgroupOf D ≤ pCore 2 D :=
    le_sSup ⟨hPN, P.isPGroup'.of_equiv (subgroupOfEquivOfLe hPD).symm⟩
  have hmap : (P : Subgroup L).map f = unipotent F := congrArg Sylow.toSubgroup hP
  -- Remove the lifted unipotent factor inside the two-core.
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) z
    obtain ⟨d,u,hu,he⟩ := borel_factorization F (f x) x.property
    rw [← hmap] at hu
    obtain ⟨p,hp,hpu⟩ := hu
    have ht : p⁻¹ * x.val ∈ T := by
      change f (p⁻¹ * x.val) ∈ torus F
      rw [map_mul, map_inv, hpu, he, inv_mul_cancel_left]
      exact ⟨d,rfl⟩
    refine ⟨⟨p⁻¹ * x.val,ht⟩,?_⟩
    have hpq : q ⟨p,hPD hp⟩ = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact hcore hp
    change q (j ⟨p⁻¹ * x.val,ht⟩) = q x
    have hj : j ⟨p⁻¹ * x.val,ht⟩ = (⟨p,hPD hp⟩ : D)⁻¹ * x := rfl
    rw [hj, map_mul, map_inv, hpq, inv_one, one_mul]
  let := torus_preimage_isMulCommutative F hF f hf hk
  refine IsMulCommutative.of_comm ?_
  intro x y
  obtain ⟨a,rfl⟩ := hr x
  obtain ⟨b,rfl⟩ := hr y
  rw [← map_mul, ← map_mul, mul_comm']

end Matrix.PSL3.LinearThree.CentralBorelQuotient
