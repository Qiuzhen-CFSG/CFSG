module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Enlargement
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.Setup
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.FixedSubgroup
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.SymplecticFixed
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models

/-!
# The model-inspection configuration for exceptional E.6.25

In a two-factor exceptional decomposition, construct the actual enlarged
C-component, its corank-three fixed subgroup, and a nontrivial involution
on it fixing a Sylow two-subgroup pointwise. The involution centralizer
contains the original C-component with its relative subnormality retained.

The precise E.6.8 alternatives at corank three reduce to the Borel case with
parameter three or the symplectic root-parabolic case with parameter three.
This deduction uses the complete alternative specifications, including their
actual model equivalences, rather than a supplied incompatibility certificate.

The component and block model inspections are still required. This module
does not yet assert the exceptional two-factor exclusion or E.6.25.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8,
printed pp.247–248 (PDF pp.258–259), and E.6.25, printed pp.255–256
(PDF pp.266–267).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U X L : Subgroup G}

/-- The constructed local configuration. Every component is relative to the
indicated centralizer; the involution acts on the actual enlarged subgroup. -/
structure TwoCentralEnlargement (M V U L W J : Subgroup G) : Prop where
  subspace_le : W ≤ U
  index_two : W.relIndex U = 2
  obstruction : W ∈ obstructionFamily M V
  component : J ∈ Chapter1.cComponentsIn (centralizer (W : Set G))
  proper : L < J
  fixed : V ⊓ centralizer (J : Set G) = W
  corank : subgroupCorank V (V ⊓ centralizer (J : Set G)) = 3
  action : ∃ t ∈ U, t ∉ W ∧ orderOf t = 2 ∧
    t ∈ normalizer (J : Set G) ∧
    centralizer (U : Set G) =
      centralizer (W : Set G) ⊓ centralizer ({t} : Set G) ∧
    L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)) ∧
    ∃ a : MulAut J, orderOf a = 2 ∧
      (∀ x : J, (a x : G) = t * (x : G) * t⁻¹) ∧
      (∃ S : Sylow 2 J, ∀ x ∈ (S : Subgroup J), a x = x) ∧
      a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J

/-- Construct the complete involution configuration from the exceptional
decomposition with two factors. No bound on the total number of factors is used. -/
theorem exceptional_two_factor_configuration [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V)
    (containment : EarlierLocalContainment K)
    (normalization : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hsize : D.size = 2)
    (hC : Nat.card (inducedAutomizer V X) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf
      (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hact : ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand (otherIndex hsize D.distinguished)) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hXL : X ≤ L) (hfixed : V ⊓ centralizer (L : Set G) = U) :
    ∃ J : Subgroup G,
      TwoCentralEnlargement M V U L
        (subspaceGroup (D.summand (otherIndex hsize D.distinguished))) J ∧
      generatedFactorLift V X (D.factor D.distinguished) ≤ J := by
  let j := otherIndex hsize D.distinguished
  obtain ⟨hWU, hi, hW, J, hJ, hLJ, hYJ, hf, hr⟩ :=
    exceptional_enlargement h containment normalization hU hX D j
      (otherIndex_ne hsize D.distinguished) (eq_or_otherIndex hsize D.distinguished)
      hC hmodel hgen hdim hact hL hXL hfixed
  exact ⟨J, ⟨hWU, hi, hW, hJ, hLJ, hf, hr,
    exceptional_involution_action h containment hU hW hWU hi hL hJ hLJ.le hf⟩, hYJ⟩

omit [Finite G] in
/-- At corank three the precise E.6.8 alternatives retain only parameter
three; in the symplectic case the actual root-parabolic clause must hold. -/
theorem component_alternatives_at_corank_three {Q J W : Subgroup G}
    (h8 : Components.ComponentAlternatives M V W Q J)
    (hr : Components.actionCorank V J = 3) :
    Components.BorelAlternative M V W J 3 ∨
      (Components.SymplecticAlternative M V W J 3 ∧
        Components.MaximalParabolic J (J ⊓ M) ∧
        Components.SymplecticRootAction J V 3) := by
  rcases h8 with ⟨n, hb⟩ | ⟨n, hs⟩ | hl | ha | ho
  · have hn : n = 3 := hb.dimension.trans hr
    subst n
    exact Or.inl hb
  · rcases hs.local_structure with ⟨_, ⟨hd, _⟩ | ⟨_, hd⟩⟩ | ⟨hp, hroot, hd⟩
    · omega
    · omega
    · have hn : n = 3 := hd.symm.trans hr
      rw [hn] at hs hroot
      exact Or.inr ⟨hs, hp, hroot⟩
  · have := hl.dimension
    omega
  · have := ha.dimension
    omega
  · have := ho.dimension
    omega

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
