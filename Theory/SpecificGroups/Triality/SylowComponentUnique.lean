module
public import Theory.SpecificGroups.SL2.SylowOvergroupComponentUnique
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient

/-!
# Unique C-components in genuine binary triality Sylow overgroups

Use the graph-field D₄ carrier and its root parabolics. The normal local
factor has cyclic quotient in the full parabolic. Modulo its two-core,
the arm factor is PSL₂(q³) and the central factor is PSL₂(q), including
q = 2. Solvable-extension lifting and full-Sylow placement give uniqueness.
Source: Aschbacher--Smith A.3.12, pp.47--48; GLS3 §§2.3--2.6.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard
open Parabolics
theorem localFactor_sylow_component_unique (P : Parameters) (hp : P.prime = 2) (a : Node) :
    SylowOvergroupComponentUnique (localFactor P a) := by
  let : Group.IsNilpotent (pCore 2 (localFactor P a)) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (localFactor P a))
  cases a with
  | arms =>
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
    exact SylowOvergroupComponentUnique.of_equiv (localFactorArmsQuotientEquivPSL2 P hp)
      (Theory.PSL2.sylow_overgroup_component_unique (ExtensionField P))
  | central =>
    let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
    exact SylowOvergroupComponentUnique.of_equiv (localFactorCentralQuotientEquivPSL2 P hp)
      (Theory.PSL2.sylow_overgroup_component_unique (GaloisField P.prime P.exponent))

theorem parabolic_sylow_component_unique (P : Parameters) (hp : P.prime = 2) (a : Node) :
    SylowOvergroupComponentUnique (parabolic P a) := by
  let N := (localFactor P a).subgroupOf (parabolic P a)
  let : IsCyclic (parabolic P a ⧸ N) := parabolic_quotient_isCyclic P hp a
  apply SylowOvergroupComponentUnique.of_solvable_quotient N
  exact SylowOvergroupComponentUnique.of_equiv
    (subgroupOfEquivOfLe (localFactor_le_parabolic P a))
    (localFactor_sylow_component_unique P hp a)

theorem binary_sylow_overgroup_component_unique (n : ℕ) (hn : 0<n)
    [Group.IsPerfect (BinaryCarrier n hn)] : SylowOvergroupComponentUnique (BinaryCarrier n hn) := by
  apply SylowOvergroupComponentUnique.of_proper_conjugate_cover
  intro S P hSP hP
  let D := binaryParameters n hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier D) S (unipotentSylow D rfl)
  let a := MulAut.conj g
  have hS : (S : Subgroup (Carrier D)).map a.toMonoidHom = unipotent D :=
    congrArg Sylow.toSubgroup hg
  have hp : P.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hP
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨b,hb⟩ := OddSupplement.le_parabolic n hn (P.map a.toMonoidHom) (hS ▸ map_mono hSP) hp
  exact ⟨g,parabolic D b,hb,parabolic_sylow_component_unique D rfl b⟩
end Triality.Standard
