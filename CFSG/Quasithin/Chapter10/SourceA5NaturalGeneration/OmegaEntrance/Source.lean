module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.OmegaEntrance.CubicCore
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedSpan
/-!
# The original natural A₅ Hall action on the Sylow omega-center

The half-Sylow fixed vectors generate the original moved factor. Their
index-two diagonals detect every cubic actor of the actual component orbit.
Consequently an elementary-three Hall subgroup has trivial pointwise
centralizer on the omega-center, and a nontrivial such subgroup in H forces
the nontrivial commutator required by the subsequent E.2.3 source selection.
This proof precedes that selection and uses only the original natural marking.

Source: Aschbacher–Smith10.1.2(5) and10.2.3, printed pp.742 and745.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
  (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
  {K : Type*} [Field K] [CharP K 2]
local instance omegaEntranceSourceAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance omegaEntranceSourceElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (f : alternatingGroup (Fin 5) ≃* SL(2,K))
  (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
  (hi : (originalMovedQuotientAction D e).IsIrreducible)
include D e hn ht htn hcross f n hi

set_option backward.isDefEq.respectTransparency false in
/-- Every original cubic orbit element moves the Sylow omega-center. -/
theorem source_natural_cubic_not_centralizes_omegaCenter
    (b : localOrbit T L) (hb : orderOf b = 3) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  exact source_original_cubic_not_centralizes_omegaCenter D e hn ht htn hcross f n
    (source_a5_moved_fixed_span D e hi ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
      (T.isPGroup'.to_le inf_le_left)) b hb

set_option backward.isDefEq.respectTransparency false in
/-- The actual elementary-three Hall subgroup has no nontrivial element
centralizing the original Sylow omega-center. -/
theorem source_natural_three_hall_omega_centralizer_eq_bot
    (B : Subgroup G) [IsElementaryAbelian 3 B] (hBR : B ≤ localOrbit T L) :
    B ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ := by
  exact source_original_elementary_three_omega_centralizer_eq_bot D e hn ht htn hcross f n
    (source_a5_moved_fixed_span D e hi ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
      (T.isPGroup'.to_le inf_le_left)) B hBR

set_option backward.isDefEq.respectTransparency false in
/-- A nontrivial actual Hall subgroup in H supplies the original
noncentral omega-center entrance, before any E.2.3 source selection. -/
theorem source_natural_omega_commutator_ne_bot_of_three_hall
    (B H : Subgroup G) [IsElementaryAbelian 3 B]
    (hBR : B ≤ localOrbit T L) (hBH : B ≤ H) (hB : B ≠ ⊥) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥ := by
  exact source_original_omega_commutator_ne_bot_of_three_hall D e hn ht htn hcross f n
    (source_a5_moved_fixed_span D e hi ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
      (T.isPGroup'.to_le inf_le_left)) B H hBR hBH hB
end CFSG.Quasithin.Chapter10
