module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.TwoCore
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Context
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.GroupTheory.PrimeRankProduct


/-!
# Actual two-rank bounds for the two natural components

The natural marking identifies each component with SL₃ over its seed field.
Odd field degree makes its center trivial, so the canonical projective map
transfers the checked PSL₃ two-rank computation. Distinct components commute,
and centerlessness makes their intersection trivial. Their join therefore
has rank 2(m+k). The actual containment of the elementary offender in that
join gives the first source inequality, without assuming a rank estimate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, inequality (*). Its equality consequences for the projections
of A and the lower codimension estimates are separate remaining arguments.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem seed_two_rank {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    primeRank 2 L = 2 * seed.field.degree := by
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) seed.field.Carrier) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [← Nat.card_congr (Subgroup.centerCongr seed.natural.groupEquiv).toEquiv,
      seed_center_eq_bot ρ seed]
    simp
  let e := seed.natural.groupEquiv.trans
    (Matrix.SL3.equivProjectiveOfCenterEqBot seed.field.Carrier hz)
  rw [primeRank_equiv 2 e]
  exact Matrix.PSL3Even.two_rank seed.field.Carrier seed.field.degree_pos seed.field.card_eq

omit [Finite G] in
private theorem components_disjoint {L M : Subgroup G}
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (hz : center L = ⊥) : Disjoint L M := by
  have hc := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne))
  apply Subgroup.disjoint_def.mpr
  intro x hx hM
  have hxc : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc hM l l.property)
  have hxe : (⟨x, hx⟩ : L) = 1 := by simpa only [hz, mem_bot] using hxc
  exact congrArg Subtype.val hxe

theorem two_component_rank {A L M : Subgroup G}
    (sL : NaturalSeed ρ A L) (sM : NaturalSeed ρ A M)
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M) :
    primeRank 2 ↥(L ⊔ M) = 2 * (sL.field.degree + sM.field.degree) := by
  rw [Subgroup.primeRank_sup_eq_add_of_disjoint_commuting L M
    (components_disjoint hL hM hne (seed_center_eq_bot ρ sL))
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne)),
    seed_two_rank ρ sL, seed_two_rank ρ sM]
  omega

theorem SecondComponent.rank_bound {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (hA : IsElementaryTwo A)
    (d : SecondComponent ρ A L) : rank A ≤ 2 * (sL.field.degree + d.seed.field.degree) := by
  let : IsElementaryAbelian 2 A := hA.2
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hbound : rank A ≤ primeRank 2 ↥(L ⊔ d.second) := by
    apply primeRank_ge_of_elementary_embedding (p := 2)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a) hA.card_eq_two_pow_rank
      (Subgroup.inclusion d.offender_le)
    exact Subgroup.inclusion_injective d.offender_le
  rwa [two_component_rank ρ sL d.seed hL d.isComponent d.distinct] at hbound

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
