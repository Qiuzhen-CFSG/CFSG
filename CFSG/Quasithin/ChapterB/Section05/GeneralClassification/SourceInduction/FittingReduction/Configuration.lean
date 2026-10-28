module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.EarlierSources
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.SymmetricThreeModule

/-!
# The selected S₃ configuration in B.5.8

This is the intermediate output to be derived from complete B.1.9. It records
the original inclusions, their multiplication, the two-dimensional moved space,
and its fixed complement. The trivial complementary factor gives B.5.6(2)
on the original action; the nontrivial factor admits the already proved
strict-order descent with all B.5.3 hypotheses.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.8, p.106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- A construction target, never an earlier-source theorem assumption. -/
structure Configuration (ρ : Representation (ZMod 2) G V) (A : Subgroup G) where
  first : Subgroup G
  second : Subgroup G
  contains : A ≤ first
  product : InternalProduct first second
  firstEquiv : first ≃* Equiv.Perm (Fin 3)
  firstSpace : Subrepresentation ρ
  firstSpace_eq : firstSpace.toSubmodule = moved ρ first
  dimension : Module.finrank (ZMod 2) firstSpace.toSubmodule = 2
  secondSpace : Subrepresentation ρ
  secondSpace_eq : secondSpace.toSubmodule = fixedSpace ρ first
  decomposition : IsCompl firstSpace.toSubmodule secondSpace.toSubmodule
  cross_fixed : firstSpace.toSubmodule ≤ fixedSpace ρ second

variable {A : Subgroup G} (c : Configuration ρ A)

abbrev Configuration.secondAction := c.secondSpace.toRepresentation.comp c.second.subtype

theorem Configuration.invariants_le_second : ρ.invariants ≤ c.secondSpace.toSubmodule := by
  rw [c.secondSpace_eq]
  exact fun _ hv g => hv g

theorem Configuration.second_invariants_iff (v : c.secondSpace) :
    v ∈ (Representation.invariants c.secondAction) ↔ (v : V) ∈ ρ.invariants := by
  constructor
  · intro hv g
    obtain ⟨a,b,rfl⟩ := c.product.exists_mul g
    have ha : ρ (a : G) v = v := by
      have hm := v.property
      change (v : V) ∈ c.secondSpace.toSubmodule at hm
      rw [c.secondSpace_eq] at hm
      exact hm a
    have hb : ρ (b : G) v = v := congrArg Subtype.val (hv b)
    rw [map_mul, Module.End.mul_apply, hb, ha]
  · intro hv b
    exact Subtype.ext (hv b)

/-- If the second factor vanishes, the original actor and module have
the exact S₃ alternative, including the moved/fixed direct sum. -/
noncomputable def Configuration.symmetricThree (h : c.second = ⊥) : SymmetricThreeCase ρ := by
  have ht : c.first = ⊤ := by simpa only [h,sup_bot_eq] using c.product.sup_eq_top
  have hw : c.secondSpace.toSubmodule = ρ.invariants := by
    rw [c.secondSpace_eq,ht]
    ext v
    exact ⟨fun hv g => hv ⟨g,trivial⟩, fun hv g => hv g⟩
  have hu : c.firstSpace.toSubmodule = moved ρ ⊤ := by rw [c.firstSpace_eq,ht]
  let e : (⊤ : Subgroup G) ≃* Equiv.Perm (Fin 3) := ht ▸ c.firstEquiv
  exact ⟨Subgroup.topEquiv.symm.trans e, hu ▸ hw ▸ c.decomposition, hu ▸ c.dimension⟩

theorem Configuration.second_ne_bot (hn : ¬ AdequateAlternative ρ) : c.second ≠ ⊥ := by
  intro hz
  exact hn (Or.inr (.symmetricThree (c.symmetricThree hz)))

theorem Configuration.first_ne_bot : c.first ≠ ⊥ := by
  have hn : Nontrivial c.first := c.firstEquiv.symm.injective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot c.first).mp hn

/-- The recursive action is on the actual fixed complement and has
strictly smaller group order. No rank or classification premise is used. -/
theorem Configuration.descent [Finite G] {K : GroupClass.{u}} (hyp : FFHypothesis K ρ) :
    Nat.card c.second < Nat.card G ∧ FFHypothesis K c.secondAction := by
  apply hyp.descent_to_second ρ c.product c.first_ne_bot c.firstSpace c.secondSpace
    c.cross_fixed
  · exact c.secondSpace_eq.le
  · exact Or.inl c.decomposition.sup_eq_top

/-- The only classification invoked here is at the strictly smaller order. -/
theorem Configuration.classify_second [Finite G] {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    AdequateAlternative c.secondAction := by
  apply hyp.classify_second ρ ih c.product c.first_ne_bot c.firstSpace c.secondSpace
    c.cross_fixed
  · exact c.secondSpace_eq.le
  · exact Or.inl c.decomposition.sup_eq_top

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
