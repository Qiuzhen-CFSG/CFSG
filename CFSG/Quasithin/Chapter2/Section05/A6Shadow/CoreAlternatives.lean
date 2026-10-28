module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport

/-!
# The rank-one core alternatives in the original A₆ shadow

The disjoint crossing conjugate of the actual core acts faithfully in the
actual Sylow image in Aut(A₆). Transport rank and the Frattini subgroup across
this embedding and apply the proved Sylow subgroup classification. This proves
source 2.5.27 from the preceding 2.5.24 and 2.5.26, without a core model premise.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 2.5.27,
printed p.569.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Source 2.5.27, on the literal earlier core and its crossing action. -/
theorem EarlierSetup.core_alternatives_of_rank_one (d : EarlierSetup κ G)
    (hrank : primeRank 2 d.SC = 1) (hphi : frattini d.SC ≠ ⊥) :
    Nonempty (d.SC ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (d.SC ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (d.SC ≃* QuaternionGroup 2) := by
  let e := (MulAut.conj d.x⁻¹).subgroupMap d.SC
  let f := d.toImageSylow.comp (inclusion (d.rightConjugate_le d.sc_le_s))
  let j := f.comp e.toMonoidHom
  have hj : Function.Injective j := d.crossing_action_injective.comp e.injective
  let ej : d.SC ≃* j.range := MonoidHom.ofInjective hj
  have hr : primeRank 2 j.range = 1 := (primeRank_congr 2 ej).symm.trans hrank
  have hf : frattini j.range ≠ ⊥ := by
    intro he
    apply hphi
    have hm := ej.mapSubgroup.map_radical
    change (frattini d.SC).map ej.toMonoidHom = frattini j.range at hm
    exact ((frattini d.SC).map_eq_bot_iff_of_injective ej.injective).mp (hm.trans he)
  rcases AlternatingSix.ShadowLocal.SylowGeometry.rank_one_subgroup_classification
    d.imageSylow j.range hr hf with h | h | h
  · obtain ⟨a⟩ := h
    exact Or.inl ⟨ej.trans a⟩
  · obtain ⟨a⟩ := h
    exact Or.inr (Or.inl ⟨ej.trans a⟩)
  · obtain ⟨a⟩ := h
    exact Or.inr (Or.inr ⟨ej.trans a⟩)

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
