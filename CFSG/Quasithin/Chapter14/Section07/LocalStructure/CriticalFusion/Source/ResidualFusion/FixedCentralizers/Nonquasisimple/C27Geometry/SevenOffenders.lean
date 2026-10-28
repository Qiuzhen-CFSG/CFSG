module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenGeometry

/-!
# The outer offender on the original fixed A₇ component

The transposition supplied by the literal fixed-component geometry acts
externally on A₇: injectivity of S₇ → Aut(A₇) and parity rule out an inner
actor. Its radical has order two. The nontrivial best offender furnished
by C.2.7(2) is therefore this entire radical, and it generates the whole
star group together with the component. In particular the offender group
is not contained in the component. SevenModule uses this to exclude the
exceptional four-dimensional branch, whose offender group equals A₇.

Source: Aschbacher--Smith C.2.7(2--3), pp.145--147, and 14.7.68(2),
pp.1071--1072. All groups and quotient maps are the original fixed ones.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Nonquasisimple.SevenGeometry
variable {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}

theorem generator_not_mem_component (geo : SevenGeometry d u Lu) :
    geo.generator ∉ starImage Lu (d.fixedCore u) Lu := by
  intro hr
  let r : starImage Lu (d.fixedCore u) Lu := ⟨geo.generator,hr⟩
  have he : (geo.component r : Equiv.Perm (Fin 7)) = geo.transposition := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).1
    apply MulEquiv.ext
    intro a
    obtain ⟨k,rfl⟩ := geo.component.surjective a
    apply Subtype.ext
    change (geo.component r : Equiv.Perm (Fin 7)) * geo.component k *
      (geo.component r : Equiv.Perm (Fin 7))⁻¹ =
        geo.transposition * geo.component k * geo.transposition⁻¹
    have hc := (geo.action k (r*k*r⁻¹)).mp rfl
    simpa only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv] using hc
  have hp := (geo.component r).property
  rw [he,Equiv.Perm.mem_alternatingGroup,geo.swap.sign_eq] at hp
  norm_num at hp

theorem radical_card (geo : SevenGeometry d u Lu) :
    Nat.card (starImage Lu (d.fixedCore u) (d.fixedCore u)) = 2 := by
  rw [geo.radical,←zpowers_eq_closure,Nat.card_zpowers,geo.order]
end Nonquasisimple.SevenGeometry
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_radical_le_offender
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    starImage Lu (d.fixedCore u) (d.fixedCore u) ≤
      offenderSubgroup (starRepresentation Lu (d.fixedCore u)) := by
  obtain ⟨geo⟩ := d.fixedComponent_C27_seven_geometry u h
  obtain ⟨A,hAR,hA⟩ := (ChapterC.C27Source.kernel_offender_from_source
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)).2.best
  have hc : Nat.card A = 2 := by
    have hh := card_dvd_of_le hAR
    rw [geo.radical_card] at hh
    exact ((Nat.dvd_prime Nat.prime_two).mp hh).resolve_left
      (fun hh => hA.1.1 ((eq_bot_iff_card A).mpr hh))
  have he : A = starImage Lu (d.fixedCore u) (d.fixedCore u) :=
    eq_of_le_of_card_ge hAR (by rw [geo.radical_card,hc])
  exact he ▸ hA.le_offenderSubgroup (starRepresentation Lu (d.fixedCore u))

theorem fixedComponent_C27_offender_eq_top
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    offenderSubgroup (starRepresentation Lu (d.fixedCore u)) = ⊤ := by
  apply top_unique
  rw [←starImage_sup_eq_top Lu (d.fixedCore u)]
  exact sup_le (ChapterC.C27Source.star_moved_section_from_source
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)).1 (d.fixedComponent_C27_radical_le_offender u h)

theorem fixedComponent_C27_offender_not_le_component
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    ¬ offenderSubgroup (starRepresentation Lu (d.fixedCore u)) ≤
      starImage Lu (d.fixedCore u) Lu := by
  obtain ⟨geo⟩ := d.fixedComponent_C27_seven_geometry u h
  intro hh
  apply geo.generator_not_mem_component
  apply hh ((d.fixedComponent_C27_radical_le_offender u h) ?_)
  rw [geo.radical]
  exact subset_closure (Set.mem_singleton geo.generator)
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
