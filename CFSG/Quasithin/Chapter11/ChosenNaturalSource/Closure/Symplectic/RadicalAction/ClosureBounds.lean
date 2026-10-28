module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.LocalClosure

/-!
# The literal closure subgroups before the radical-action calculation

The strict marked flag supplies the nonzero point and proper interval needed
by 11.5.5. Applying its proved G.2 argument to G₁ gives the commutator bound
[U,O₂(G₁)]≤V₁. Together with the Cartan calculation, this places V, W_H
and U in the same core. All containment and normalization statements below
refer to these original subgroups.

For the subsequent model calculation, noncommutativity of U is reduced to
nontrivial movement on V₃ while [V,U]≤V₁. The original normalizer action
also detects noncommutativity of W_H. No radical-action alternative or
abelianness assertion is assumed or asserted here.
Source: Aschbacher--Smith 11.5.5 and 11.5.7, printed pp.780,782--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Nonzero field dimension, rather than nontriviality of a central kernel,
supplies the point hypothesis in the preceding closure theorem. -/
theorem MarkedFlag.point_ne_bot (m : MarkedFlag E) : E.point ≠ ⊥ := by
  intro hp
  have hz : m.flag.space 0 = ⊥ := by
    apply bot_unique
    apply ((LocalGeometry.Coordinates.sp4 m.action).binarySubspace_le_iff _ ⊥).mp
    rw [← m.point_eq, hp]
    exact bot_le
  have hd := m.flag.dimension 0
  rw [hz] at hd
  norm_num at hd

/-- Both closures are taken in G₁, and the smaller seed gives U≤W_H. -/
theorem closure_containments (m : MarkedFlag E) :
    E.V₃ ≤ E.U ∧ E.U ≤ E.W ∧ V ≤ E.W ∧ E.W ≤ E.G₁ := by
  exact ⟨le_conjugateSpanBy _ _,
    conjugateSpanBy_mono (D.centralQuotientPreimage_le E.threeSpace) le_rfl,
    le_conjugateSpanBy _ _,
    conjugateSpanBy_le_self (D.le_sylow.trans m.sylow_le_point_normalizer)⟩

/-- Normalization is relative to G₁, not to the ambient simple group. -/
theorem closure_normalizations :
    E.G₁ ≤ normalizer (E.U : Set G) ∧ E.G₁ ≤ normalizer (E.W : Set G) :=
  ⟨le_normalizer_conjugateSpanBy _ _, le_normalizer_conjugateSpanBy _ _⟩

/-- Applying the preceding closure theorem to G₁ itself supplies the bound
used in the nonabelian-U contradiction, with the strict flag discharged. -/
theorem marked_U_core_and_commutator (m : MarkedFlag E)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃) :
    E.U ≤ E.G₁.pCoreIn 2 ∧
      (frattini E.U).map E.U.subtype ≤ E.V₁ ∧ ⁅E.U, E.G₁.pCoreIn 2⁆ ≤ E.V₁ := by
  have h := E.localClosure_core_and_frattini (m.point_ne_bot E)
    m.point_lt_threeSpace.le m.point_lt_threeSpace.ne m.sylow_le_point_normalizer
    hlocal hirr E.G₁ le_rfl (sup_le E.L₁_le_G₁ m.sylow_le_point_normalizer)
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-- All initial core bounds from the exact preceding geometry and 11.5.6.
This is an application to the original source groups, including U's actual seed V₃. -/
theorem initial_core_bounds (m : MarkedFlag E)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hVX : ⁅V, E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P, E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ E.U ≤ E.G₁.pCoreIn 2 ∧
      (frattini E.U).map E.U.subtype ≤ E.V₁ ∧ ⁅E.U, E.G₁.pCoreIn 2⁆ ≤ E.V₁ := by
  have hv := marked_seed_and_closure_le_core_of_parts_four_five E m hti hgen hVX hfour hfive
  exact ⟨hv.1, hv.2, marked_U_core_and_commutator E m hlocal hirr⟩

/-- The original core lies in the original Sylow, so its subgroups act on V
whenever the preceding T-invariance of V is supplied. -/
theorem core_normalizes_seed (m : MarkedFlag E)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    E.G₁.pCoreIn 2 ≤ normalizer (V : Set G) := by
  have hcore : E.G₁.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer]
      using pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  exact hcore.trans hT

omit E [Finite G] in
/-- The bar notation detects the full action on V, not just a replacement quotient. -/
theorem actionImage_eq_bot_iff (A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) :
    actionImage (V := V) A = ⊥ ↔ A ≤ centralizer (V : Set G) := by
  change (A.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom = ⊥ ↔ _
  rw [Subgroup.map_eq_bot_iff, normalizerMonoidHom_ker]
  constructor
  · intro h a ha
    exact h (show (⟨a, hA ha⟩ : normalizer (V : Set G)) ∈
      A.subgroupOf (normalizer (V : Set G)) from ha)
  · intro h a ha
    exact h ha

/-- Nonabelian U really moves its own original seed V₃. -/
theorem U_nonabelian_movement
    (hV : V ≤ E.G₁.pCoreIn 2) (hc : ⁅E.U, E.G₁.pCoreIn 2⁆ ≤ E.V₁)
    (hu : ¬ IsMulCommutative E.U) :
    ⁅E.V₃, E.U⁆ ≠ ⊥ ∧ ⁅V, E.U⁆ ≤ E.V₁ := by
  constructor
  · intro hz
    apply hu
    exact (conjugateSpanBy_commutative_iff E.V₃ E.G₁).mpr
      (commutator_eq_bot_iff_le_centralizer.mp hz)
  · rw [commutator_comm]
    exact (commutator_mono le_rfl hV).trans hc

/-- Nonabelian W_H has nontrivial original action image, after the core bound. -/
theorem W_actionImage_ne_bot_of_nonabelian (m : MarkedFlag E)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hW : E.W ≤ E.G₁.pCoreIn 2) (hne : ¬ IsMulCommutative E.W) :
    actionImage (V := V) E.W ≠ ⊥ := by
  intro hz
  have hc := (actionImage_eq_bot_iff E.W
    (hW.trans (core_normalizes_seed E m hT))).mp hz
  exact hne ((conjugateSpanBy_commutative_iff V E.G₁).mpr (le_centralizer_iff.mp hc))

/-- If U centralizes V, its normality propagates centralization to W_H,
and hence the original V₃ centralizes W_H. -/
theorem threeSpace_centralizes_W_of_U_centralizes_seed
    (hc : ⁅V, E.U⁆ = ⊥) : ⁅E.V₃, E.W⁆ = ⊥ := by
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((le_conjugateSpanBy E.V₃ E.G₁).trans (U_centralizes_W E hc))

/-- Both choices of the source's temporary W retain G₁-normalization and
containment in W_H. Its two-core containment therefore uses the same Cartan bound. -/
theorem auxiliaryW_containment_and_normalization (hW : E.W ≤ E.G₁.pCoreIn 2) :
    auxiliaryW E ≤ E.W ∧ auxiliaryW E ≤ E.G₁.pCoreIn 2 ∧
      E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  classical
  have hu : E.U ≤ E.W :=
    conjugateSpanBy_mono (D.centralQuotientPreimage_le E.threeSpace) le_rfl
  unfold auxiliaryW
  split_ifs
  · exact ⟨le_rfl, hW, (closure_normalizations E).2⟩
  · exact ⟨hu, hu.trans hW, (closure_normalizations E).1⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
