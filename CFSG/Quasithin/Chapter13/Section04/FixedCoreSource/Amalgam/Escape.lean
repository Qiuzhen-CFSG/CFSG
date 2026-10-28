module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.ThetaSixSource
public import Theory.GroupTheory.SymmetricThreeTwoCoreCubic

/-!
# Escape of every admitted original amalgam

A parabolic contained in N_G(L) has its two-residual in L: its cubic
generators lie in theta(N_G(L)), which equals L for the actual central
A₆ quotient, including the covered row. Its fixed subgroup in Ω₁Z(T)
therefore contains C_Z(L). The two index-two conditions make them equal.

Locality activates the conditional relative-centralizer clause (c).
That clause makes the two fixed subgroups distinct, so both parabolics
cannot lie in N_G(L). This constructs membership in H(T,M) for every
admitted original pair, without a supplied escape or residual identity.
ApplicableNonsolvable applies this to both the general and plane cases.

Source: Aschbacher--Smith, Proposition 13.4.7, printed pp.899--900.
The genuine Hypothesis1221 and original five-dimensional marking are
retained; no ordinary quotient marking or universal structural theorem
is needed for escape itself.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- A contained S₃ parabolic has the same omega fixed hyperplane as L. -/
theorem original_contained_parabolic_fixed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAM : A ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  have htheta := h.source_theta_eq_of_six_action_quotient D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) m.quotient
  have hr : (pResidual 2 A).map A.subtype ≤ L := by
    rw [SymmetricThreeTwoCore.twoResidual_eq_cubic_closure eA,MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro a ⟨a,ha,rfl⟩
    rw [←htheta]
    exact subset_closure ⟨hAM a.property,(A.orderOf_coe a).trans ha⟩
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hf : Z ⊓ centralizer (L : Set G) ≤ Z ⊓ centralizer (A : Set G) := by
    rw [←omega_fixed_twoResidual A hTA]
    exact inf_le_inf_left _ (centralizer_le hr)
  have hi := relIndex_mul_relIndex (Z ⊓ centralizer (L : Set G))
    (Z ⊓ centralizer (A : Set G)) Z hf inf_le_left
  rw [hindexA,hindexL] at hi
  have hi1 : (Z ⊓ centralizer (L : Set G)).relIndex
      (Z ⊓ centralizer (A : Set G)) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hi1) hf

variable
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
include h D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral

/-- Locality activates the literal conditional clause (c), which forces escape. -/
theorem original_pair_outside :
    A ⊔ B ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) := by
  have hl := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  refine ⟨hl,?_⟩
  intro hXM
  have hr := (hcentral hl).2.2
  apply pair_fixed_subgroups_ne hTA hTB eA eB hne hr
  exact (original_contained_parabolic_fixed h D m hTA eA (le_sup_left.trans hXM)
    hindexL hindexA).trans
      (original_contained_parabolic_fixed h D m hTB eB (le_sup_right.trans hXM)
        hindexL hindexB).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
