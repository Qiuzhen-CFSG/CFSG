module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupAction.SylowFixedInvolutionOddCore
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner

/-!
# Odd cores of Sylow-central involution centralizers in Sp₄(4)

The moved-space calculation puts an inner involution centralizer in an
actual point or plane parabolic. When the involution fixes a Sylow subgroup
pointwise, its centralizer contains that Sylow subgroup, so inherits the
parabolic's self-centralizing two-core. Its odd core is therefore trivial.
This argument uses neither root-type conjugacy nor the c₂ centralizer table.

The faithful automorphism-overgroup conclusion uses the established
Sylow-pointwise innerness theorem. Its diagram-preserving semilinear
classification premise remains explicit and must be discharged before this
can be used as the unconditional model inspection in E.6.19.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248 (PDF pp.258–259), E.6.19, printed p.252 (PDF p.263),
and 16.1.6, printed p.1172.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.FieldFourOddCore
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A Sylow-central involution in Sp₄(4) has a centralizer of characteristic two. -/
theorem centralizer_selfCentralizing_core (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (z : Sp F) (hz : orderOf z = 2)
    (hfix : ∀ x ∈ (S : Subgroup (Sp F)), MulAut.conj z x = x) :
    centralizer (pCore 2 (centralizer ({z} : Set (Sp F))) :
      Set (centralizer ({z} : Set (Sp F)))) ≤
      pCore 2 (centralizer ({z} : Set (Sp F))) := by
  obtain ⟨P, hP, _, _, hCP⟩ := InvolutionCentralizers.involution_centralizer_parabolic z hz
  have hPcore : centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
    obtain ⟨g, hP | hP⟩ := hP
    · rw [hP]
      exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g)
        pointParabolic).mpr (pointParabolic_selfCentralizing_core (f := 2) hF (by decide))
    · rw [hP]
      exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g)
        planeParabolic).mpr (planeParabolic_selfCentralizing_core (f := 2) hF (by decide))
  have hSC : (S : Subgroup (Sp F)) ≤ centralizer ({z} : Set (Sp F)) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hfix x hx)).symm
  have hrel := centralizer_pCore_le_of_sylow_le (S.subtype (hSC.trans hCP))
    ((centralizer ({z} : Set (Sp F))).subgroupOf P)
    (fun x hx => hSC hx) hPcore
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hCP)).mp hrel

/-- The normal odd core of a Sylow-central involution centralizer is trivial. -/
theorem centralizer_oddCore_eq_bot (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (z : Sp F) (hz : orderOf z = 2)
    (hfix : ∀ x ∈ (S : Subgroup (Sp F)), MulAut.conj z x = x) :
    pPrimeCore 2 (centralizer ({z} : Set (Sp F))) = ⊥ :=
  Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (centralizer_selfCentralizing_core hF S z hz hfix)

/-- The full surrounding action is controlled once diagram-preserving
semilinear classification is supplied. This premise is not a source hypothesis
of E.6.19 and remains a separate model theorem to be proved. -/
theorem action_centralizer_oddCore_eq_bot_of_semilinear
    (hF : Nat.card F = 4)
    (hclass : ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F,
        a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut (Sp F)} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  apply d.oddCore_eq_bot_of_inner EvenProjective.center_eq_bot
  · exact DiagramAutomorphisms.aut_fixing_sylow_inner (n := 2) hF (by decide) hclass
  · exact centralizer_oddCore_eq_bot hF

end Theory.SpecificGroups.SymplecticFour.FieldFourOddCore
