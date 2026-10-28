module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.GroupTheory.GeneralizedFitting.Solvable

/-!
# Starred offenders on a prime-free solvable centralizer

Let the finite binary representation be faithful and let the actor group
have trivial two-core. A starred cubic offender has trivial intersection
with every solvable normal subgroup of order prime to three and five.
D.2.13 makes the offender centralize each remaining odd prime core, hence
the Fitting subgroup. Solvable Fitting self-centralization and the trivial
two-core then kill the intersection.

Applied to the centralizer of a normal subgroup, this gives faithfulness
of the literal conjugation map. No equality between the generalized
Fitting subgroup and the prescribed normal subgroup is required.
Source: Aschbacher--Smith D.2.13(1) and D.3.21, printed pp.184--185 and204--207.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A starred offender meets a prime-to-fifteen solvable normal subgroup trivially. -/
theorem starred_inf_normal_solvable_eq_bot
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A N : Subgroup G} (hA : A ∈ QhatStar ρ) [N.Normal] [Group.IsSolvable N]
    (h3 : Nat.Coprime 3 (Nat.card N)) (h5 : Nat.Coprime 5 (Nat.card N)) :
    A ⊓ N = ⊥ := by
  have hmap (p : ℕ) : (pCore p N).map N.subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map N.subtype⟩
  have hcoreN : pCore 2 N = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ N.subtype_injective).mp
    exact le_bot_iff.mp ((hmap 2).trans_eq hcore)
  have hfit : A.subgroupOf N ≤ centralizer (fittingSubgroup N : Set N) := by
    apply le_centralizer_iff.mpr
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp : p.1.1.Prime := Fact.out
    by_cases hp2 : p.1.1 = 2
    · rw [hp2,hcoreN]
      exact bot_le
    by_cases hp3 : p.1.1 = 3
    · have htriv : pCore 3 N = ⊥ := by
        apply (eq_bot_iff_card _).mpr
        obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := N)).exists_card_eq
        have hd := (pCore 3 N).card_subgroup_dvd_card
        rw [hn] at hd ⊢
        exact Nat.eq_one_of_dvd_coprimes (h3.pow_left n) dvd_rfl hd
      rw [hp3,htriv]
      exact bot_le
    by_cases hp5 : p.1.1 = 5
    · have htriv : pCore 5 N = ⊥ := by
        let : Fact (Nat.Prime 5) := ⟨by decide⟩
        apply (eq_bot_iff_card _).mpr
        obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 5) (G := N)).exists_card_eq
        have hd := (pCore 5 N).card_subgroup_dvd_card
        rw [hn] at hd ⊢
        exact Nat.eq_one_of_dvd_coprimes (h5.pow_left n) dvd_rfl hd
      rw [hp5,htriv]
      exact bot_le
    have hc : pCore p.1.1 G ≤ centralizer (A : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      by_contra hm
      exact ((source_lemma_D_2_13_one_two ρ hf hA (hp.odd_of_ne_two hp2) hm).1).elim hp3 hp5
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    apply N.subtype_injective
    exact hc (hmap p.1.1 (mem_map_of_mem N.subtype hx)) a ha
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have htwo : IsPGroup 2 (A.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  have hbot := twoSubgroup_faithful_on_fitting
    (generalizedFitting_eq_fitting_of_solvable N) hcoreN (A.subgroupOf N) htwo
  have hb : A.subgroupOf N = ⊥ := by
    simpa only [inf_eq_left.mpr hfit] using hbot
  apply le_bot_iff.mp
  intro x hx
  have hh : (⟨x,hx.2⟩ : N) ∈ (⊥ : Subgroup N) := hb ▸ hx.1
  exact congrArg Subtype.val (mem_bot.mp hh)

/-- Every starred offender acts faithfully on a normal subgroup whose
centralizer is solvable and has order prime to three and five. -/
theorem starred_conjugation_injective_of_solvable_centralizer
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (J : Subgroup G) [J.Normal] [Group.IsSolvable (centralizer (J : Set G))]
    (h3 : Nat.Coprime 3 (Nat.card (centralizer (J : Set G))))
    (h5 : Nat.Coprime 5 (Nat.card (centralizer (J : Set G))))
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut J).comp A.subtype) := by
  have hi := starred_inf_normal_solvable_eq_bot ρ hf hcore hA h3 h5
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  have he : (MulAut.conjNormal (a : G) : MulAut J) = 1 := ha
  have hc : (a : G) ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    have he' := congrArg (fun e : MulAut J => ((e ⟨j,hj⟩ : J) : G)) he
    change (a : G) * j * (a : G)⁻¹ = j at he'
    have he'' := congrArg (fun z : G => z * (a : G)) he'
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he''.symm
  have hh : (a : G) ∈ (⊥ : Subgroup G) := hi ▸ ⟨a.property,hc⟩
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp hh))
end CFSG.Quasithin.ChapterD
