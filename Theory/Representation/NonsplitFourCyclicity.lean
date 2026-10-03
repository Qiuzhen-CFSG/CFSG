module

public import Theory.Representation.SingerFour
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Tactic

/-!
# Cyclic nonsplit subgroups in dimension four

Over a finite field of even order `q`, every subgroup of `GL(4,q)` whose
order divides `q² + 1` is cyclic. The center of each nontrivial Sylow subgroup
has a cyclic ambient centralizer, so the subgroup is a Z-group. Its commutator
is therefore cyclic. Singer normalizer conjugation has fourth power trivial
on this commutator, since `q⁴ ≡ 1` modulo `q² + 1`. Odd order makes fourth
powers surjective, so the commutator is central. Cyclic abelianization then
makes the group abelian, and an abelian Z-group is cyclic.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10(a), printed
pp. 190–191. The argument uses Z-group structure in place of Hall containment.
-/

noncomputable section

namespace Representation

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

private theorem cyclic_of_center_nontrivial {G : Type*} [Group G]
    (f : G →* GL (Fin 4) K) (hf : Function.Injective f)
    (hcard : Nat.card G ∣ Fintype.card K ^ 2 + 1)
    [Nontrivial (Subgroup.center G)] : IsCyclic G := by
  let C := (Subgroup.center G).map f
  have hC : C ≠ ⊥ := by
    exact fun h => (Subgroup.nontrivial_iff_ne_bot (Subgroup.center G)).mp
      inferInstance (((Subgroup.center G).map_eq_bot_iff_of_injective hf).mp h)
  have hCcard : Nat.card C ∣ Fintype.card K ^ 2 + 1 := by
    rw [Subgroup.card_map_of_injective hf]
    exact (Subgroup.card_subgroup_dvd_card _).trans hcard
  let := isCyclic_centralizer_of_card_dvd_sq_add_one C hC hCcard
  let j : G →* Subgroup.centralizer (C : Set (GL (Fin 4) K)) :=
    f.codRestrict _ (by
      intro g
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨z, hz, rfl⟩
      simpa only [map_mul] using (congrArg f (Subgroup.mem_center_iff.mp hz g)).symm)
  exact isCyclic_of_injective j (fun a b h => hf (congrArg Subtype.val h))

private theorem zGroup_of_card_dvd_sq_add_one
    (U : Subgroup (GL (Fin 4) K))
    (hcard : Nat.card U ∣ Fintype.card K ^ 2 + 1) : IsZGroup U := by
  refine ⟨fun p hp P => ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  rcases subsingleton_or_nontrivial P with hP | hP
  · infer_instance
  · let := P.2.center_nontrivial
    exact cyclic_of_center_nontrivial (U.subtype.comp P.1.subtype)
      (U.subtype_injective.comp P.1.subtype_injective)
      (P.card_subgroup_dvd_card.trans hcard)

private theorem normalizer_fourth_pow_centralizes
    (C : Subgroup (GL (Fin 4) K)) (hC : C ≠ ⊥) [IsCyclic C]
    (hcard : Nat.card C ∣ Fintype.card K ^ 2 + 1)
    (g : GL (Fin 4) K) (hg : g ∈ Subgroup.normalizer (C : Set (GL (Fin 4) K))) :
    g ^ 4 ∈ Subgroup.centralizer (C : Set (GL (Fin 4) K)) := by
  obtain ⟨i, _, hi⟩ := normalizer_eq_frobenius_pow_of_card_dvd_sq_add_one C hC hcard g hg
  let q := Fintype.card K
  have hmod : q ^ 4 ≡ 1 [MOD q ^ 2 + 1] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨1 - (q : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  have hmodi : (q ^ i) ^ 4 ≡ 1 [MOD q ^ 2 + 1] := by
    simpa only [← pow_mul, mul_comm i 4, one_pow] using hmod.pow i
  apply Subgroup.mem_centralizer_iff.mpr
  intro u hu
  have huq : u ^ (q ^ 2 + 1) = 1 := by
    obtain ⟨m, hm⟩ := hcard
    have hpow : u ^ Nat.card C = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : C)))
    rw [hm, pow_mul, hpow, one_pow]
  have hiter (n : ℕ) : (g ^ n)⁻¹ * u * g ^ n = u ^ ((q ^ i) ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (g ^ (n + 1))⁻¹ * u * g ^ (n + 1) =
            g⁻¹ * ((g ^ n)⁻¹ * u * g ^ n) * g := by group
        _ = g⁻¹ * u ^ ((q ^ i) ^ n) * g := by rw [ih]
        _ = (g⁻¹ * u * g) ^ ((q ^ i) ^ n) := by
          simpa using (map_pow (MulAut.conj g⁻¹) u ((q ^ i) ^ n))
        _ = u ^ ((q ^ i) ^ (n + 1)) := by rw [hi u hu, ← pow_mul, pow_succ']
  have heq : (g ^ 4)⁻¹ * u * g ^ 4 = u := by
    rw [hiter, pow_eq_pow_of_modEq hmodi huq, pow_one]
  have := congrArg (fun x => g ^ 4 * x) heq
  simpa [mul_assoc] using this

/-- A subgroup of `GL(4,q)` of order dividing `q²+1`, for even `q`, is cyclic. -/
public theorem isCyclic_of_card_dvd_sq_add_one
    (U : Subgroup (GL (Fin 4) K))
    (hcard : Nat.card U ∣ Fintype.card K ^ 2 + 1) : IsCyclic U := by
  let := zGroup_of_card_dvd_sq_add_one U hcard
  have hcentral : commutator U ≤ Subgroup.center U := by
    by_cases hD : commutator U = ⊥
    · rw [hD]
      exact bot_le
    let D := (commutator U).map U.subtype
    have hDne : D ≠ ⊥ := by
      exact fun h => hD (((commutator U).map_eq_bot_iff_of_injective U.subtype_injective).mp h)
    let := IsZGroup.isCyclic_commutator (G := U)
    let : IsCyclic D := isCyclic_of_surjective _ (U.subtype.subgroupMap_surjective (commutator U))
    have hDcard : Nat.card D ∣ Fintype.card K ^ 2 + 1 := by
      rw [Subgroup.card_map_of_injective U.subtype_injective]
      exact (Subgroup.card_subgroup_dvd_card _).trans hcard
    have heven : Even (Fintype.card K) :=
      Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq K 2))
    have hodd : Odd (Nat.card U) := ((heven.pow_of_ne_zero (by decide : 2 ≠ 0)).add_one).of_dvd_nat hcard
    have hcop : (Nat.card U).Coprime 4 := by
      simpa using hodd.coprime_two_right.pow_right 2
    intro u hu
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨r, hr⟩ := hcop.pow_left_bijective.surjective g
    have hrnorm : (r : GL (Fin 4) K) ∈ Subgroup.normalizer (D : Set (GL (Fin 4) K)) :=
      (commutator U).le_normalizer_map U.subtype
        (Subgroup.mem_map.mpr ⟨r, by simp [Subgroup.normalizer_eq_top], rfl⟩)
    have hc := normalizer_fourth_pow_centralizes D hDne hDcard r.val hrnorm
    have hc' := Subgroup.mem_centralizer_iff.mp hc u.val
      (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    apply Subtype.ext
    simpa only [← Subgroup.coe_pow, hr, Subgroup.coe_mul] using hc'.symm
  have hker : (Abelianization.of : U →* Abelianization U).ker ≤ Subgroup.center U := by
    rwa [Abelianization.ker_of]
  let _ := commGroupOfCyclicCenterQuotient Abelianization.of hker
  infer_instance

end Representation
