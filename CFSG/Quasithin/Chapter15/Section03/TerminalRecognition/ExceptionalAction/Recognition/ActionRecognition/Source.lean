module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.Target
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.SourceGeometry
public import CFSG.Quasithin.ChapterF.Section06.Basic

/-!
# Intrinsic source data for the terminal FF action

All subgroups here live in the actual local group `H = G₀`. The record
retains the two generating local groups, their common Sylow subgroup,
relative normalization, the two-cores and two-residuals, and the marked
commutator `F`. Its clauses precede the final representation recognition;
it contains no classification or hexacode-equivalence conclusion. Only the
global-core centrality conclusion of 15.3.68(2) is used here; no equality
between the intersection of the local cores and the centralizer is required.

We derive the faithful-action kernel hypotheses, the commutator-generation
identity for `V₀`, and the four-dimensional fixed space with the strict
local-core inclusion. These are the constraints used to exclude ordinary
FF modules. Restriction of the original ambient configuration to `G₀`
and construction of this record remain with the source assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.66–68 and the non-`S₃` branch of the final proof of 15.3.1,
printed pp.1152–1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition

variable {H : Type*} [Group H] [Finite H]

/-- Earlier local facts, after restricting to `H = G₀`. In particular,
`J(T_E)` is normalized by `G₁`, not assumed normal in the ambient group. -/
structure SourceInput (V : Subgroup H) where
  T : Sylow 2 H
  YF : Subgroup H
  XE : Subgroup H
  G1 : Subgroup H
  G2 : Subgroup H
  R : Subgroup H
  F : Subgroup H
  /-- Definitions immediately before 15.3.68. -/
  first_local : G1 = YF ⊔ (T : Subgroup H)
  second_local : G2 = XE ⊔ (T : Subgroup H)
  generated : G1 ⊔ G2 = ⊤
  common_sylow : G1 ⊓ G2 = (T : Subgroup H)
  first_quotient : Nonempty (G1 ⧸ pCore 2 G1 ≃* Equiv.Perm (Fin 3))
  second_quotient : Nonempty (G2 ⧸ pCore 2 G2 ≃* Equiv.Perm (Fin 3))
  /-- Relative normality inherited from 15.3.67(3) and its conjugate. -/
  first_normalized : G1 ≤ normalizer (YF : Set H)
  second_normalized : G2 ≤ normalizer (XE : Set H)
  /-- The residuals defining the local odd factors. -/
  first_perfect : IsPPerfect 2 YF
  second_perfect : IsPPerfect 2 XE
  first_residual : (pResidual 2 G1).map G1.subtype = YF
  second_residual : (pResidual 2 G2).map G2.subtype = XE
  /-- The cyclic quotients in 15.3.67(3), also transported to `Y_F`. -/
  first_odd_quotient : Nonempty (YF ⧸ pCore 2 YF ≃* Multiplicative (ZMod 3))
  second_odd_quotient : Nonempty (XE ⧸ pCore 2 XE ≃* Multiplicative (ZMod 3))
  /-- The genuine centralizer identities from 15.3.67(1). -/
  centralizer_eq : R = centralizer (V : Set H)
  sylow_centralizer_eq : R = (T : Subgroup H) ⊓ centralizer (V : Set H)
  /-- 15.3.68(2), with the other half of centrality following from the bound below. -/
  vector_le_core : V ≤ pCore 2 H
  /-- The bound explicitly used in the final paragraph on p.1155. -/
  core_bound : pCore 2 H ⊔ YF.pCoreIn 2 ≤ R
  /-- 15.3.68(5). -/
  three_prime_core : pPrimeCore 3 H = pCore 2 H
  /-- The equality in the non-`S₃` branch: both sides are two-residuals. -/
  thompson_residual : (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
    pResidual 2 H
  /-- 15.3.67(4) and `J(T_E) = J(R)` from its proof. -/
  second_commutator : XE = ⁅XE, Stellmacher.elementaryAbelianMaxJ (T : Subgroup H)⁆
  sylow_thompson : Stellmacher.elementaryAbelianMaxJ (T : Subgroup H) =
    Stellmacher.elementaryAbelianMaxJ R
  /-- The normality used at the top of p.1155. -/
  thompson_normalized : G1 ≤
    normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup H) : Set H)
  /-- The conjugate of 15.3.66(5). -/
  vector_commutator : V = ⁅V, YF⁆
  /-- The standing natural orthogonal module has order sixteen. -/
  vector_card : Nat.card V = 16
  /-- The marked commutator used in the final exclusion. -/
  local_commutator : ⁅V, G1.pCoreIn 2⁆ = F
  singular_nontrivial : F ≠ ⊥

namespace SourceInput

variable {V : Subgroup H} (d : SourceInput V)
include d

/-- The marked pair satisfies the genuine Goldschmidt definition. -/
theorem goldschmidt : ChapterF.IsGoldschmidtTriple d.G1 d.G2 :=
  ⟨d.generated, d.first_quotient, d.second_quotient, d.T, d.common_sylow⟩

omit [Finite H] in
/-- The given centralizer lies in the actual common Sylow subgroup. -/
theorem centralizer_le_sylow : centralizer (V : Set H) ≤ (d.T : Subgroup H) := by
  rw [← d.centralizer_eq, d.sylow_centralizer_eq]
  exact inf_le_left

omit [Finite H] in
/-- The centralizer hypothesis for `quotientAction` follows from the local configuration. -/
theorem centralizer_isTwoGroup : IsPGroup 2 (centralizer (V : Set H)) :=
  d.T.isPGroup'.of_injective (inclusion d.centralizer_le_sylow)
    (inclusion_injective _)

omit [Finite H] in
/-- The two-core centralizes `V`, giving the other half of `V ≤ Z(O₂(H))`. -/
theorem core_centralizes : pCore 2 H ≤ centralizer (V : Set H) :=
  le_sup_left.trans (d.core_bound.trans d.centralizer_eq.le)

omit [Finite H] in
/-- The residual identity puts the actual two-perfect local factor in `J(H)`. -/
theorem thompson_contains : d.YF ≤ thompsonGroup H :=
  perfect_le_of_residual_eq (thompsonGroup H) d.YF
    d.first_perfect d.thompson_residual

omit [Finite H] in
/-- The source commutator identity forces the whole module to be generated by `X`. -/
theorem closure_commutator : moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆ :=
  moduleClosure_eq_commutator V (thompsonGroup H) d.YF
    d.thompson_contains d.vector_commutator

/-- The image local core is strictly smaller than the core of the first local group. -/
theorem image_core_strict :
    (d.YF.map (coreProjection (H := H))).pCoreIn 2 <
      (d.G1.map (coreProjection (H := H))).pCoreIn 2 := by
  apply localCore_strict d.YF d.G1 V d.R d.F
    (d.first_local.symm ▸ le_sup_left) d.first_normalized d.core_bound
    d.centralizer_eq.le d.local_commutator d.singular_nontrivial

variable [IsElementaryAbelian 2 (moduleClosure V)]

/-- The particular source subspace, not all of `V₀`, has binary dimension four. -/
theorem vector_finrank : Module.finrank (ZMod 2) (planeSubspace V V) = 4 :=
  planeSubspace_finrank_of_card V V le_normalClosure 4 d.vector_card

/-- The core of the image of `Y_F` fixes that actual four-dimensional subspace. -/
theorem vector_fixed : planeSubspace V V ≤
    fixedSpace (quotientAction V d.centralizer_isTwoGroup d.core_centralizes)
      ((d.YF.map coreProjection).pCoreIn 2) :=
  localCore_fixes_subspace V d.centralizer_isTwoGroup d.core_centralizes
    d.YF d.R d.core_bound d.centralizer_eq.le

end SourceInput

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
