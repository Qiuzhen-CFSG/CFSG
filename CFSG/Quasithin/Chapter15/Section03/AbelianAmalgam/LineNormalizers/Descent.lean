module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Frattini
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Products
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.LocalCollapse
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.ResidualDefinitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.ResidualComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification

/-!
# Descent in the proof of 15.3.67

This is the conditional descent after the recognition of the original `I₀`.
`Inputs` contains only preceding geometric, local, Sylow and recognition
conclusions. In particular it contains neither `C_G(V) = C_T(V)` nor either
terminal product or quotient identification. Only the recognized index of
`I₀` is needed from recognition; no action kernel is identified with `Q_E`.

The Frattini correction gives index three in the original `G_E`. Comparing
prime-to-six generators through the three-coset and natural orthogonal
actions gives the common `{2,3}`-residual. Characteristic two and maximal
two-locality kill it, and the earlier `3'` centralizer conclusion gives
`C_G(V) = C_T(V)` and the products `M = Y T` and `M_E = Y_E T_E`.
`Inputs.quotientInputs` discharges this last, additional premise of the
quotient-identification helper. Its second factor is then recognized using
the original index, two-core and maximum-elementary Thompson subgroup.

`source_descent` assembles clauses (1), (3), (4) of 15.3.67, conditional on
the earlier source conclusions. `quotient_compatibility` preserves the
initial first coordinate and identifies the two residual images and their
cores using that same product map. It supplies more than an abstract order
calculation. The parent line-normalizer development must construct `Inputs`
and supply clause (2); no temporary replacement of `G_E` occurs here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1154, PDF p.1171.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent

variable {G : Type*} [Group G] [Finite G]

/-- The earlier source conclusions consumed by descent. The marked decomposition
is the initial `S₃ × Ċ_E` decomposition on p.1153, whose second factor is the
actual centralizer image and has no assumed isomorphism type. Normality here
is relative, and `local_core` is precisely the action-kernel clause of 15.3.66(5).
The source recognition of `I₀` supplies `I0_index` for the original subgroups. -/
structure Inputs (M Y : Subgroup G) (T : Sylow 2 G) (V E : Subgroup G) where
  line_le : E ≤ V
  escapes : ¬ lineNormalizer E ≤ M
  normalizer_V_le_M : normalizer (V : Set G) ≤ M
  natural_action : NaturalOrthogonalAction M V
  maximal_two_local : IsMaximalTwoLocal M
  characteristic_two : centralizer (pCore 2 M : Set M) ≤ pCore 2 M
  centralizer_three_prime : ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer (V : Set G))
  T_le_M : (T : Subgroup G) ≤ M
  Y_le_M : Y ≤ M
  Y_normal_in_M : (Y.subgroupOf M).Normal
  earlier_product : (M : Set G) =
    (Y : Set G) * (M ⊓ centralizer (V : Set G) : Set G) * (T : Set G)
  sylow : Sylow 2 (lineNormalizer E)
  sylow_map : (sylow : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype =
    lineT (T : Subgroup G) E
  thompson_eq : elementaryAbelianMaxJ (lineT (T : Subgroup G) E) =
    elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (V : Set G))
  core_centralizes_line : lineQ E ≤ centralizer (E : Set G)
  geometric_product : (lineNormalizer E : Set G) =
    (lineY Y E : Set G) * (lineT (T : Subgroup G) E : Set G) *
      (centralizer (E : Set G) : Set G)
  product_with_I : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G)
  I0_index : (lineI0 (T : Subgroup G) V E ⊓ lineM M E).relIndex
    (lineI0 (T : Subgroup G) V E) = 3
  local_core : (lineY Y E ⊔ lineT (T : Subgroup G) E : Subgroup G).pCoreIn 2 =
    (lineY Y E ⊔ lineT (T : Subgroup G) E) ⊓ centralizer (E : Set G)
  Y_normal : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal
  marked : QuotientIdentification.MarkedDecomposition Y (T : Subgroup G) E

variable {M Y : Subgroup G} {T : Sylow 2 G} {V E : Subgroup G}
variable [IsMulCommutative V]

omit [Finite G] [IsMulCommutative V] in
private theorem sylow_normalizes_Y (s : Inputs M Y T V E) :
    (T : Subgroup G) ≤ normalizer (Y : Set G) :=
  s.T_le_M.trans ((normal_subgroupOf_iff_le_normalizer s.Y_le_M).mp s.Y_normal_in_M)

/-- Frattini correction, absorption, and index transfer for the original `G_E`.
The correction uses the quotient centralizer in `G_E/E` defined in `Frattini`. -/
theorem correction (s : Inputs M Y T V E) :
    (lineI E : Set G) = (lineI0 (T : Subgroup G) V E : Set G) *
      (thompsonKernel V E : Set G) ∧
    thompsonKernel V E ≤ lineI E ⊓ normalizer (V : Set G) ∧
    lineI E ⊓ normalizer (V : Set G) ≤ lineM M E ∧
    (lineNormalizer E : Set G) =
      (lineM M E : Set G) * (lineI0 (T : Subgroup G) V E : Set G) ∧
    (lineM M E).relIndex (lineNormalizer E) = 3 :=
  ⟨frattini_correction _ V E s.line_le s.sylow s.sylow_map,
    thompsonKernel_le_normalizer V E s.line_le,
    thompsonNormalizer_le_lineM M V E s.normalizer_V_le_M,
    original_product M _ V E s.line_le s.sylow s.sylow_map
      s.normalizer_V_le_M s.product_with_I,
    original_index_three M _ V E s.line_le s.sylow s.sylow_map
      s.normalizer_V_le_M s.product_with_I s.I0_index⟩

/-- The actual common `{2,3}`-residual, its relative normalities, and its collapse.
This derives the common-normal-subgroup obstruction from the local source data. -/
theorem common_residual (s : Inputs M Y T V E) :
    twoThreeResidual (lineNormalizer E) = twoThreeResidual (centralizer (V : Set G)) ∧
    twoThreeResidual (centralizer (V : Set G)) = twoThreeResidual M ∧
    ((twoThreeResidual (lineNormalizer E)).subgroupOf M).Normal ∧
    ((twoThreeResidual (lineNormalizer E)).subgroupOf (lineNormalizer E)).Normal ∧
    twoThreeResidual (lineNormalizer E) = ⊥ ∧
    twoThreeResidual (centralizer (V : Set G)) = ⊥ ∧ twoThreeResidual M = ⊥ :=
  residual_comparison M V E s.line_le s.normalizer_V_le_M s.natural_action
    (correction s).2.2.2.2 s.maximal_two_local s.characteristic_two s.escapes

/-- Residual collapse removes the centralizer from the whole and line products.
The line product uses the already established Sylow subgroup of the original `G_E`. -/
theorem centralizer_and_products (s : Inputs M Y T V E) :
    centralizer (V : Set G) = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    (M : Set G) = (Y : Set G) * (T : Set G) ∧
    (lineM M E : Set G) =
      (lineY Y E : Set G) * (lineT (T : Subgroup G) E : Set G) := by
  have hi := (correction s).2.2.2.2
  obtain ⟨hC, hM⟩ := centralizer_and_whole_product M Y V E s.line_le
    s.normalizer_V_le_M s.natural_action hi s.maximal_two_local s.characteristic_two
    s.escapes s.centralizer_three_prime T s.T_le_M s.Y_le_M s.earlier_product
  exact ⟨hC, hM, line_product_of_original_sylow M Y V E s.line_le
    s.normalizer_V_le_M s.natural_action hi s.maximal_two_local s.characteristic_two
    s.escapes s.centralizer_three_prime T s.T_le_M s.Y_le_M s.Y_normal_in_M
    s.earlier_product s.sylow s.sylow_map⟩

/-- Discharge the terminal line-product premise of quotient identification.
All the other fields are earlier source conclusions; none is a terminal quotient
or a commutator-generation hypothesis. -/
noncomputable def Inputs.quotientInputs (s : Inputs M Y T V E) :
    QuotientIdentification.Inputs M Y (T : Subgroup G) V E where
  line_le := s.line_le
  sylow := s.sylow
  sylow_map := s.sylow_map
  T_le_M := s.T_le_M
  thompson_eq := s.thompson_eq
  core_centralizes_line := s.core_centralizes_line
  normalizer_V_le_M := s.normalizer_V_le_M
  product_with_I := s.product_with_I
  I0_index := s.I0_index
  local_product := by
    exact SetLike.coe_injective ((centralizer_and_products s).2.2.trans
      (lineY_sup_lineT_product Y (T : Subgroup G) E (sylow_normalizes_Y s)).symm)
  local_core := s.local_core
  Y_normal := s.Y_normal
  marked := s.marked

/-- Conditional assembly of 15.3.67(1),(3),(4) after the original `I₀` recognition.
Every group and two-core in this statement belongs to the original normalizer.
The equivalences are the actual compatible maps constructed from `s.quotientInputs`. -/
theorem source_descent (s : Inputs M Y T V E) :
    centralizer (V : Set G) = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    (M : Set G) = (Y : Set G) * (T : Set G) ∧
    (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT (T : Subgroup G) E : Set G) ∧
    ((lineY Y E).subgroupOf (lineNormalizer E)).Normal ∧
    ((lineX E).subgroupOf (lineNormalizer E)).Normal ∧
    Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((lineY Y E ⧸ pCore 2 (lineY Y E)) ≃* Multiplicative (ZMod 3)) ∧
    ¬ lineX E ≤ M ∧
    Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    lineX E = ⁅lineX E,
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (V : Set G))⁆ := by
  obtain ⟨hC, hM, _⟩ := centralizer_and_products s
  exact ⟨hC, hM,
    original_residual_product Y _ E s.sylow s.sylow_map
      (sylow_normalizes_Y s) s.geometric_product,
    s.Y_normal, lineX_normal_in_lineNormalizer E,
    ⟨QuotientIdentification.lineXCoreEquivCyclic s.quotientInputs⟩,
    ⟨QuotientIdentification.lineYCoreEquivCyclic s.quotientInputs⟩,
    lineX_not_le_of_escape M Y _ E s.sylow s.sylow_map (sylow_normalizes_Y s)
      s.Y_le_M s.T_le_M s.escapes s.geometric_product,
    ⟨QuotientIdentification.originalProductEquiv s.quotientInputs⟩,
    QuotientIdentification.lineX_eq_commutator_thompson s.quotientInputs⟩

/-- Compatibility of the terminal product with the initial marking and original
subgroups. Both residual images use this same map, and their intrinsic cores
are their intersections with the original `Q_E`. -/
theorem quotient_compatibility (s : Inputs M Y T V E) :
    let q := QuotientIdentification.originalProductMap s.quotientInputs
    let e := QuotientIdentification.originalProductEquiv s.quotientInputs
    q.ker.map (lineNormalizer E).subtype = lineQ E ∧
    (∀ z, (e z).1 = (s.marked.equiv z).1) ∧
    ((lineY Y E ⊔ zpowers s.marked.tau).subgroupOf (lineNormalizer E)).map q =
      (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ ∧
    ((centralizer (E : Set G)).subgroupOf (lineNormalizer E)).map q =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ ∧
    ((lineX E).subgroupOf (lineNormalizer E)).map q =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) ∧
    ((lineY Y E).subgroupOf (lineNormalizer E)).map q =
      (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) ∧
    (lineX E).pCoreIn 2 = lineX E ⊓ lineQ E ∧
    (lineY Y E).pCoreIn 2 = lineY Y E ⊓ lineQ E ∧
    lineY Y E ⊓ lineX E = (lineY Y E).pCoreIn 2 ⊓ (lineX E).pCoreIn 2 := by
  exact ⟨QuotientIdentification.originalProductMap_ker_ambient s.quotientInputs,
    QuotientIdentification.originalProductEquiv_first_coordinate s.quotientInputs,
    QuotientIdentification.originalProductMap_first_factor s.quotientInputs,
    QuotientIdentification.originalProductMap_second_factor s.quotientInputs,
    QuotientIdentification.originalProductMap_lineX s.quotientInputs,
    QuotientIdentification.originalProductMap_lineY s.quotientInputs,
    QuotientIdentification.lineX_twoCore E,
    QuotientIdentification.lineY_twoCore Y E s.Y_normal,
    QuotientIdentification.lineY_inf_lineX_eq_core_intersection s.quotientInputs⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
