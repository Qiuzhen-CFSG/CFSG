module

public import Theory.SpecificGroups.Triality.ParabolicLocalDefinitions
public import Theory.GroupTheory.PResidual.PrimeToCoreMap
public import Theory.SpecificGroups.Triality.RadicalCoordinates
public import Theory.GroupTheory.RelativeComplementProjection
public import Theory.GroupTheory.SolvableResidual
public import Theory.Frattini.OmegaProducts
public import Theory.ElementaryAbelian.Quotient

/-!
# Local structure of the genuine characteristic-two triality parabolics

The arms node is the first parabolic in F.1.12(I)(4), and the central node is
the second. Their local factors are the embedded prime-to-two residuals.
The actual root radicals and Levi subgroups split these local factors, giving
surjective Levi projections with precisely the relative radicals as kernels.
The Levi two-cores vanish, so these kernels are the intrinsic two-cores;
their images also equal the two-cores of the full parabolics.

The first two-core quotient is PSL₂ over the q³-element extension field, and
the second is PSL₂ over the q-element base field. The first core has order q⁹
and elementary abelian center of order q, equal to both its derived and
Frattini subgroups. The second core has order q¹¹. The first local factor
centralizes the embedded center of the positive unipotent subgroup.

For q > 2, both Levi groups are perfect and their commutators with the
radicals generate the radicals. Hence the local factors are perfect and
equal their solvable residuals. The quotient and radical calculations include
q = 2; the residual assertion retains q > 2, as required by the source.

The twisted root formulas, fixed-field restriction, and elementary central
quotient computations are supplied by `RadicalCoordinates` and
`LeviIdentification`, all on the genuine Geck D₄ graph-field carrier.

Sources: Aschbacher–Smith F.1.11–12, printed pp.262–264
(`refs/quasithin.pdf`); GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.Parabolics
open scoped MatrixGroups

/-- The local factor and its parabolic have identical embedded p-cores. -/
theorem localFactor_core_map (P : Parameters) (a : Node) :
    (pCore P.prime (localFactor P a)).map (localFactor P a).subtype =
      (pCore P.prime (parabolic P a)).map (parabolic P a).subtype := by
  let K := (localFactor P a).subgroupOf (parabolic P a)
  have h : (pCore P.prime K).map K.subtype = pCore P.prime (parabolic P a) := by
    exact (congrArg (fun J : Subgroup (parabolic P a) =>
      (pCore P.prime J).map J.subtype) (localFactor_subgroupOf P a)).trans
        (Subgroup.map_pCore_primeToResidual P.prime)
  let e := Subgroup.subgroupOfEquivOfLe (localFactor_le_parabolic P a)
  have he : (localFactor P a).subtype.comp e.toMonoidHom =
      (parabolic P a).subtype.comp K.subtype := rfl
  rw [← pCore_map_iso P.prime e, Subgroup.map_map, he, ← Subgroup.map_map, h]

/-- Every element of a p-group radical belongs to the actual local factor. -/
theorem radical_le_localFactor_of_isPGroup (P : Parameters) (a : Node)
    (hU : IsPGroup P.prime (radical P a)) : radical P a ≤ localFactor P a := by
  intro x hx
  obtain ⟨n, hn⟩ := hU ⟨x, hx⟩
  exact mem_localFactor_of_pow P a x (radical_le_parabolic P a hx) n
    (congrArg Subtype.val hn)

/-- Relative normality, rather than ambient normality, gives this containment. -/
theorem radical_le_parabolic_core_of_isPGroup (P : Parameters) (a : Node)
    (hU : IsPGroup P.prime (radical P a)) :
    radical P a ≤ (pCore P.prime (parabolic P a)).map (parabolic P a).subtype := by
  have h : (radical P a).subgroupOf (parabolic P a) ≤
      pCore P.prime (parabolic P a) :=
    le_sSup ⟨inferInstance, hU.comap_subtype⟩
  simpa only [Subgroup.map_subgroupOf_eq_of_le (radical_le_parabolic P a)] using
    Subgroup.map_mono (f := (parabolic P a).subtype) h

theorem radical_le_localFactor_core_of_isPGroup (P : Parameters) (a : Node)
    (hU : IsPGroup P.prime (radical P a)) :
    radical P a ≤ (pCore P.prime (localFactor P a)).map (localFactor P a).subtype := by
  rw [localFactor_core_map]
  exact radical_le_parabolic_core_of_isPGroup P a hU


/-- The root radical lies in the actual local factor, including q = 2. -/
theorem radical_le_localFactor (P : Parameters) (hp : P.prime = 2) (a : Node) :
    radical P a ≤ localFactor P a :=
  radical_le_localFactor_of_isPGroup P a (hp ▸ RadicalCoordinates.radical_isPGroup P hp a)

/-- The radical is normal relative to the local factor, not to the ambient carrier. -/
instance radical_localFactor_normal (P : Parameters) (a : Node) :
    ((radical P a).subgroupOf (localFactor P a)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer ((localFactor_le_parabolic P a).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P a)).mp
      (radical_normal P a)))

/-- The projection onto the exact root-defined Levi subgroup. -/
@[expose] def localLeviProjection (P : Parameters) (hp : P.prime = 2) (a : Node) :
    localFactor P a →* levi P a :=
  Subgroup.relativeComplementProjection (radical_le_localFactor P hp a)
    (RadicalCoordinates.levi_le_localFactor P hp a)
    (RadicalCoordinates.localFactor_eq_radical_sup_levi P hp a).symm
    (RadicalCoordinates.disjoint_radical_levi P hp a)

theorem localLeviProjection_surjective (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Function.Surjective (localLeviProjection P hp a) :=
  Subgroup.relativeComplementProjection_surjective _ _ _ _

/-- The kernel is the radical restricted to its actual local factor. -/
theorem localLeviProjection_ker (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (localLeviProjection P hp a).ker = (radical P a).subgroupOf (localFactor P a) :=
  Subgroup.relativeComplementProjection_ker _ _ _ _

theorem localLeviProjection_inclusion (P : Parameters) (hp : P.prime = 2) (a : Node)
    (x : levi P a) :
    localLeviProjection P hp a
      (Subgroup.inclusion (RadicalCoordinates.levi_le_localFactor P hp a) x) = x :=
  Subgroup.relativeComplementProjection_inclusion _ _ _ _ x

/-- The root radical is the embedded two-core of the local factor. -/
theorem localFactor_twoCore_map (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (pCore 2 (localFactor P a)).map (localFactor P a).subtype = radical P a :=
  Subgroup.embedded_pCore_eq_of_leviProjection _ _ (radical_le_localFactor P hp a)
    (localLeviProjection P hp a) (localLeviProjection_surjective P hp a)
    (localLeviProjection_ker P hp a) (RadicalCoordinates.radical_isPGroup P hp a)
    (levi_twoCore_eq_bot P a hp)

/-- The same radical is the embedded two-core of the full parabolic. -/
theorem parabolic_twoCore_map (P : Parameters) (hp : P.prime = 2) (a : Node) :
    (pCore 2 (parabolic P a)).map (parabolic P a).subtype = radical P a := by
  have h := localFactor_core_map P a
  rw [hp] at h
  exact h.symm.trans (localFactor_twoCore_map P hp a)

theorem localFactor_twoCore_eq (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (localFactor P a) = (radical P a).subgroupOf (localFactor P a) := by
  apply Subgroup.map_injective (localFactor P a).subtype_injective
  rw [localFactor_twoCore_map P hp a,
    Subgroup.map_subgroupOf_eq_of_le (radical_le_localFactor P hp a)]

/-- Identify the intrinsic local two-core with the concrete root radical. -/
@[expose] def localFactorTwoCoreEquivRadical (P : Parameters) (hp : P.prime = 2) (a : Node) :
    pCore 2 (localFactor P a) ≃* radical P a :=
  (MulEquiv.subgroupCongr (localFactor_twoCore_eq P hp a)).trans
    (Subgroup.subgroupOfEquivOfLe (radical_le_localFactor P hp a))

/-- The genuine two-core quotient is the actual root-defined Levi. -/
@[expose] def localFactorQuotientEquivLevi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    localFactor P a ⧸ pCore 2 (localFactor P a) ≃* levi P a :=
  (QuotientGroup.quotientMulEquivOfEq (localFactor_twoCore_eq P hp a)).trans
    (Subgroup.relativeQuotientEquiv (radical_le_localFactor P hp a)
      (RadicalCoordinates.levi_le_localFactor P hp a)
      (RadicalCoordinates.localFactor_eq_radical_sup_levi P hp a).symm
      (RadicalCoordinates.disjoint_radical_levi P hp a))

/-- The first local quotient is PSL₂(q³), also at q = 2. -/
@[expose] def localFactorArmsQuotientEquivPSL2 (P : Parameters) (hp : P.prime = 2) :
    localFactor P .arms ⧸ pCore 2 (localFactor P .arms) ≃* PSL(2, ExtensionField P) :=
  (localFactorQuotientEquivLevi P hp .arms).trans (leviArmsEquivPSL2 P hp)

/-- The second local quotient is PSL₂(q), also at q = 2. -/
@[expose] def localFactorCentralQuotientEquivPSL2 (P : Parameters) (hp : P.prime = 2) :
    localFactor P .central ⧸ pCore 2 (localFactor P .central) ≃*
      PSL(2, GaloisField P.prime P.exponent) :=
  (localFactorQuotientEquivLevi P hp .central).trans (leviCentralEquivPSL2 P hp)

theorem localFactor_arms_twoCore_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (pCore 2 (localFactor P .arms)) = P.q ^ 9 :=
  (Nat.card_congr (localFactorTwoCoreEquivRadical P hp .arms).toEquiv).trans
    (RadicalCoordinates.radical_arms_card P hp)

theorem localFactor_central_twoCore_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (pCore 2 (localFactor P .central)) = P.q ^ 11 :=
  (Nat.card_congr (localFactorTwoCoreEquivRadical P hp .central).toEquiv).trans
    (RadicalCoordinates.radical_central_card P hp)

theorem localFactor_arms_twoCore_center_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (Subgroup.center (pCore 2 (localFactor P .arms))) = P.q :=
  (Nat.card_congr (Subgroup.centerCongr
    (localFactorTwoCoreEquivRadical P hp .arms)).toEquiv).trans
      (RadicalCoordinates.card_center_radical_arms P hp)

/-- The derived subgroup equals the center, as required by specialness. -/
theorem localFactor_arms_twoCore_center_eq_commutator
    (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (pCore 2 (localFactor P .arms)) =
      _root_.commutator (pCore 2 (localFactor P .arms)) := by
  let e := localFactorTwoCoreEquivRadical P hp .arms
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv e, map_commutator_eq,
    e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  exact RadicalCoordinates.center_radical_arms_eq_commutator P hp

/-- The Frattini subgroup also equals the center. -/
theorem localFactor_arms_twoCore_center_eq_frattini
    (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (pCore 2 (localFactor P .arms)) =
      frattini (pCore 2 (localFactor P .arms)) := by
  let e := localFactorTwoCoreEquivRadical P hp .arms
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv e, Subgroup.frattini_map_equiv e]
  exact RadicalCoordinates.center_radical_arms_eq_frattini P hp

/-- The first core center is the additive group of the actual fixed field. -/
@[expose] def localFactorArmsTwoCoreCenterEquiv (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (pCore 2 (localFactor P .arms)) ≃* Multiplicative (fixedField P) :=
  (Subgroup.centerCongr (localFactorTwoCoreEquivRadical P hp .arms)).trans
    (((Subgroup.center (radical P .arms)).equivMapOfInjective
      (radical P .arms).subtype (radical P .arms).subtype_injective).trans
        ((MulEquiv.subgroupCongr (RadicalCoordinates.embedded_center_radical_arms P hp)).trans
          (RadicalCoordinates.Centers.highestRootEquiv P hp).symm))

theorem localFactor_arms_twoCore_center_elementary (P : Parameters) (hp : P.prime = 2) :
    IsElementaryAbelian 2 (Subgroup.center (pCore 2 (localFactor P .arms))) := by
  let : CharP (fixedField P) 2 := hp ▸ inferInstanceAs (CharP (fixedField P) P.prime)
  let : IsElementaryAbelian 2 (Multiplicative (fixedField P)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro z
      apply Multiplicative.toAdd.injective
      simp [pow_two, CharTwo.add_self_eq_zero] }
  exact IsElementaryAbelian.of_surjective
    (localFactorArmsTwoCoreCenterEquiv P hp).symm.toMonoidHom
    (localFactorArmsTwoCoreCenterEquiv P hp).symm.surjective

/-- The source orientation [L₁, Z(S)] = 1, with Z(S) embedded in the carrier. -/
theorem localFactor_arms_commutator_center_unipotent
    (P : Parameters) (hp : P.prime = 2) :
    ⁅localFactor P .arms,
      (Subgroup.center (unipotent P)).map (unipotent P).subtype⁆ = ⊥ :=
  RadicalCoordinates.localFactor_arms_commutator_center_unipotent P hp

/-- Both factors are perfect for q > 2; no perfectness assertion at q = 2. -/
theorem localFactor_isPerfect (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) : Group.IsPerfect (localFactor P a) := by
  let := levi_isPerfect P a hp hq
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  have hR : radical P a ≤ ⁅localFactor P a, localFactor P a⁆ := by
    calc
      radical P a = ⁅radical P a, levi P a⁆ :=
        (RadicalCoordinates.commutator_radical_levi_eq P hp hq a).symm
      _ ≤ ⁅localFactor P a, localFactor P a⁆ :=
        Subgroup.commutator_mono (radical_le_localFactor P hp a)
          (RadicalCoordinates.levi_le_localFactor P hp a)
  have hC : levi P a ≤ ⁅localFactor P a, localFactor P a⁆ := by
    calc
      levi P a = ⁅levi P a, levi P a⁆ := (Subgroup.commutator_eq_self (H := levi P a)).symm
      _ ≤ ⁅localFactor P a, localFactor P a⁆ :=
        Subgroup.commutator_mono (RadicalCoordinates.levi_le_localFactor P hp a)
          (RadicalCoordinates.levi_le_localFactor P hp a)
  calc
    localFactor P a = radical P a ⊔ levi P a :=
      RadicalCoordinates.localFactor_eq_radical_sup_levi P hp a
    _ ≤ ⁅localFactor P a, localFactor P a⁆ := sup_le hR hC

theorem localFactor_solvableResidual_eq_top (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) :
    Subgroup.solvableResidual (localFactor P a) = ⊤ := by
  let := localFactor_isPerfect P hp hq a
  exact Subgroup.solvableResidual_eq_top

/-- The source equality Lᵢ = Lᵢ^∞, expressed in their common ambient carrier. -/
theorem localFactor_solvableResidual_map (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) :
    (Subgroup.solvableResidual (localFactor P a)).map (localFactor P a).subtype =
      localFactor P a := by
  rw [localFactor_solvableResidual_eq_top P hp hq a, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Triality.Standard.Parabolics
