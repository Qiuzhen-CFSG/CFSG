module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# The critical order-two reduction for 14.7.69

The genuine quotient of the two-residual has order sixty. The relative Sylow
in 14.7.66 consequently has order four. The positive quotient rank in the
actual critical choice proves nontriviality of Uα*, leaving precisely the
order-two case or equality with Q*. No exclusion of that equality is assumed
by the reduction below.

`RankSelection` records only the rank inequalities from Notation 14.7.1, on
the literal intersection U ∩ Qα and the actual star map. Its producer is
qt-14-07 via the earlier critical selection. It is not a replacement for
that selection or for its additional quadratic-offender property.

The separate original-section transports establish the module calculations
and the three possible orders of U₀. The full exclusion Uα*=Q* remains the
assembly obligation of Source.OrderTwo: it requires the original V-line partition and the
critical-pair/duality intersection argument, followed by 14.7.68 fusion. In
particular this module does not yet assert Lemma 14.7.69.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Notation 14.7.1, printed p.1043; Lemmas 14.7.66 and 14.7.69,
printed pp.1070, 1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

include d in
theorem star_K_card : Nat.card (star F (K F)) = 60 := by
  have he : (star F (K F)).map d.model.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [star, map_map]
    exact d.K_image
  rw [← card_map_of_injective (K := star F (K F)) (f := d.model.toMonoidHom) d.model.injective, he,
    nat_card_alternatingGroup]
  norm_num [Nat.factorial]
end Data

namespace CriticalPath
variable (c : CriticalPath (L := L) F)

/-- The rank portion of the genuine critical choice in Notation 14.7.1.
The denominator is the literal D = U ∩ Qα. Its positivity is retained instead
of assuming nontriviality of the star image. -/
structure RankSelection : Prop where
  positive : 0 < Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U)
  comparison : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ≤
    Nat.log 2 (Nat.card (star F c.Uα))

omit [Finite G] in
theorem star_ne_bot (selection : c.RankSelection) : star F c.Uα ≠ ⊥ := by
  intro h
  have hp := lt_of_lt_of_le selection.positive selection.comparison
  rw [h, card_bot] at hp
  norm_num at hp

theorem star_Q_card (d : Data T L V F W) (earlier : c.EarlierImages) :
    Nat.card (star F (Q T L)) = 4 := by
  obtain ⟨P, hP⟩ := (c.lemma_14_7_66 earlier).2
  rw [← hP, card_subtype, P.card_eq_multiplicity, d.star_K_card]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl

/-- The genuine critical selection and 14.7.66 leave only the order-two
case and the equality Uα*=Q*. This is a reduction, not Lemma 14.7.69. -/
theorem order_two_or_full (d : Data T L V F W) (earlier : c.EarlierImages)
    (selection : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 ∨ star F c.Uα = star F (Q T L) := by
  have hle := (c.lemma_14_7_66 earlier).1
  have hdvd := card_dvd_of_le hle
  rw [c.star_Q_card d earlier] at hdvd
  have hn : 1 < Nat.card (star F c.Uα) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr (c.star_ne_bot selection)
  have hcases : Nat.card (star F c.Uα) = 2 ∨ Nat.card (star F c.Uα) = 4 := by
    have hdiv : Nat.card (star F c.Uα) ∣ 2 ^ 2 := hdvd
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    interval_cases k <;> simp_all
  rcases hcases with htwo | hfour
  · exact Or.inl htwo
  · right
    apply eq_of_le_of_card_ge hle
    rw [c.star_Q_card d earlier, hfour]
end CriticalPath
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
