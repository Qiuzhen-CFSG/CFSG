module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Reselecting the original faithful local component

The canonical Chapter1 local-family definition agrees with the forward
source family over the same ambient Sylow subgroup. Replacing the chosen
actor by a faithful member whose two-core quotient is not A₅ preserves
all assumptions of the original counterexample. The A₆ central quotient
has order 360 and is an actual quotient of the core quotient; it therefore
rules out the A₅ core quotient of order 60. This supplies the source
reselection used to apply 13.8.1 in 14.3.4.

A surjective central-cover map on C/O₂(C) constructs the literal quotient
C/O₂,Z(C), including the triple-cover case. The ordinary A₆ case uses
its trivial center. Neither normality nor a classification of arbitrary
faithful local components is assumed or concluded here.

Source: Aschbacher–Smith, 13.3.2(5), printed p.885; 14.3.4, printed p.990.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L C : Subgroup G}

omit [Finite G] in
theorem faithfulLocalComponents_iff (C : Subgroup G) :
    C ∈ MainForward.faithfulLocalComponents T ↔
      C ∈ Chapter1.L G (T : Subgroup G) ∧ IsFaithfulSignalizerType C := by
  constructor
  · rintro ⟨hC, hf⟩
    refine ⟨⟨hC.1, ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩, ?_⟩, hf⟩
    intro he
    apply hC.2
    exact (map_eq_bot_iff_of_injective _ (C ⊔ (T : Subgroup G)).subtype_injective).mp he
  · rintro ⟨hC, hf⟩
    refine ⟨⟨hC.1, ?_⟩, hf⟩
    intro he
    apply hC.2.2
    change (pCore 2 ↥(C ⊔ (T : Subgroup G))).map (C ⊔ (T : Subgroup G)).subtype = ⊥
    rw [he, Subgroup.map_bot]

/-- Reselecting any faithful actor other than A₅ preserves every original
ambient assumption; the source's A₅ minimality implication is vacuous. -/
theorem reselect (d : Counterexample T L)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C)
    (hne : ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))) :
    Counterexample T C where
  qtke := d.qtke
  local_component := (faithfulLocalComponents_iff C).mpr ⟨hC, hf⟩
  no_larger_field := d.no_larger_field
  no_linear := d.no_linear
  no_alternating_nine := d.no_alternating_nine
  no_sporadic := d.no_sporadic
  five_minimal := fun h => (hne h).elim
  no_symplectic_six := d.no_symplectic_six
  no_unitary_four := d.no_unitary_four

omit [Finite G] in
/-- The central quotient is a quotient of the literal two-core quotient.
In particular an A₆ central quotient cannot come from an A₅ core quotient. -/
theorem not_A5_of_A6_centralQuotient
    (hsix : Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6))) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e5⟩
  obtain ⟨e6⟩ := hsix
  have hle : pCore 2 C ≤ centralCore C := by
    intro x hx
    change QuotientGroup.mk' (pCore 2 C) x ∈ center (C ⧸ pCore 2 C)
    rw [show QuotientGroup.mk' (pCore 2 C) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let q : (C ⧸ pCore 2 C) →* (C ⧸ centralCore C) :=
    QuotientGroup.map _ _ (MonoidHom.id C) hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralCore C) x
    exact ⟨QuotientGroup.mk' (pCore 2 C) x, rfl⟩
  have hd := card_dvd_of_surjective q hq
  rw [Nat.card_congr e5.toEquiv, Nat.card_congr e6.toEquiv,
    nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_fin, Nat.card_fin] at hd
  norm_num [Nat.factorial] at hd

/-- Exact applicability of 13.8.1 to the newly chosen faithful component. -/
theorem reselect_A6 (d : Counterexample T L)
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hf : IsFaithfulSignalizerType C)
    (hsix : Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6))) :
    Counterexample T C :=
  reselect d hC hf (not_A5_of_A6_centralQuotient hsix)

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Subgroup Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] (C : Subgroup G)

/-- An actual central cover on the original core quotient gives precisely the
central quotient in source 13.8.1. This includes both A₆ and its triple cover. -/
noncomputable def centralQuotient_equiv_of_cover
    (f : (C ⧸ pCore 2 C) →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hk : f.ker = center (C ⧸ pCore 2 C)) :
    (C ⧸ centralCore C) ≃* alternatingGroup (Fin 6) := by
  let q := f.comp (QuotientGroup.mk' (pCore 2 C))
  apply QuotientGroup.liftEquiv (centralCore C) (φ := q)
    (hf.comp (QuotientGroup.mk'_surjective _))
  dsimp only [q]
  rw [← MonoidHom.comap_ker, hk]

/-- The A₆ core-quotient branch yields the same actual central quotient. -/
theorem A6_centralQuotient_of_coreQuotient
    (h : Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6))) :
    Nonempty ((C ⧸ centralCore C) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h
  have hc : center (C ⧸ pCore 2 C) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      exact (map_mul e z x).symm.trans ((congrArg e (hx z)).trans (map_mul e x z))
    rw [alternatingGroup.center_eq_bot (by simp)] at he
    exact e.injective (he.trans e.map_one.symm)
  exact ⟨centralQuotient_equiv_of_cover C e.toMonoidHom e.surjective (by
    rw [hc]
    exact MonoidHom.ker_eq_bot _ e.injective)⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
