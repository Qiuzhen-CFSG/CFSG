module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Reduction
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Critical geometry on the minimum nonbinary characteristic replacement

For the original nonbinary symplectic MS input, every minimum characteristic
replacement has the same component, with its original symplectic quotient
marking. Its two-core is self-centralizing by subnormal inheritance. MS3
then makes its own central omega orbit faithful and supplies positive even
critical geometry on its actual holomorph graph.

The replacement's two-group supplement and MS3 are proved directly. No
odd-index radical witness is transferred or assumed. The resulting distance
has not yet been bounded above by two.

Source: Meierfrankenfeld--Stellmacher (1993), Section 7, pp.932--933, and
the preliminary geometry (2.0)--(2.2); Aschbacher--Smith C.1.31--32.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

omit [Finite H] in
/-- The original literal product generates the ambient group. -/
theorem Input.sup_eq_top : K ⊔ R = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k,hk,r,hr,rfl⟩ := h.product x
  exact mul_mem (mem_sup_left hk) (mem_sup_right hr)

omit [Finite H] in
/-- The chosen characteristic subgroup is still a two-group on its actual carrier. -/
theorem Input.replacement_two_group : IsPGroup 2 d.radical :=
  (h.radical.isPGroup.to_subgroup d.subgroup).of_equiv d.radicalEquiv

/-- The replacement is normal in the original group. -/
theorem Input.replacement_normal : d.overgroup.Normal := by
  let := h.component_normal
  exact d.overgroup_normal_of_sup h.sup_eq_top

omit [Finite H] in
/-- The original C-component remains a C-component in the replacement. -/
theorem Input.replacement_component : (K.subgroupOf d.overgroup).IsCComponent :=
  h.component.subgroupOf le_sup_left

/-- The replacement group is the literal product of the same component and
its new two-group supplement. -/
theorem Input.replacement_product : ∀ x : d.overgroup,
    ∃ k ∈ K.subgroupOf d.overgroup, ∃ r ∈ d.radical, k * r = x := by
  let := h.component_normal
  intro x
  obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_left.mp x.property
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

/-- Its residual is the original component restricted to the replacement. -/
theorem Input.replacement_residual :
    pResidual 2 d.overgroup = K.subgroupOf d.overgroup :=
  component_eq_residual _ _ (h.replacement_component d)
    (h.replacement_two_group d) (h.replacement_product d)

omit [Finite H] in
/-- MS3 transfers through the characteristic replacement. -/
theorem Input.replacement_characteristic : MSCharacteristicCondition d.radical :=
  d.msCharacteristic_of_sup h.sup_eq_top h.characteristic

/-- The replacement contains its own two-core in its supplement. -/
theorem Input.replacement_core_le : pCore 2 d.overgroup ≤ d.radical := by
  let := h.component_normal
  exact d.core_le_radical_of_sup h.sup_eq_top

/-- The original characteristic-two hypothesis descends to this normal subgroup. -/
theorem Input.replacement_core_selfCentralizing :
    centralizer (pCore 2 d.overgroup : Set d.overgroup) ≤ pCore 2 d.overgroup :=
  subnormal_core_selfCentralizing h.core_selfCentralizing d.overgroup
    (h.replacement_normal d).isSubnormal

/-- Nontriviality of the original component rules out a trivial replacement edge. -/
theorem Input.replacement_radical_ne_bot : d.radical ≠ ⊥ := by
  intro hr
  have hq : pCore 2 d.overgroup = ⊥ :=
    le_bot_iff.mp (hr ▸ h.replacement_core_le d)
  have ht : (⊤ : Subgroup d.overgroup) ≤ ⊥ := by
    intro x _
    have hx : x ∈ centralizer (pCore 2 d.overgroup : Set d.overgroup) := by
      rw [hq]
      intro y hy
      have hy' : y = 1 := hy
      simp only [hy',one_mul,mul_one]
    exact hq ▸ h.replacement_core_selfCentralizing d hx
  exact (h.replacement_component d).ne_bot (le_bot_iff.mp (le_top.trans ht))

omit [Finite H] in
/-- The exact component quotient marking survives the change of ambient group. -/
@[expose] noncomputable def Input.replacement_quotientEquiv :
    ((K.subgroupOf d.overgroup) ⧸ pCore 2 (K.subgroupOf d.overgroup)) ≃*
      Matrix.symplecticGroup (Fin 2) F :=
  (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv

omit [Finite H] in
/-- The new marking agrees with the original one on every representative. -/
theorem Input.replacement_quotientEquiv_mk (k : K.subgroupOf d.overgroup) :
    h.replacement_quotientEquiv d (QuotientGroup.mk' _ k) =
      h.quotientEquiv (QuotientGroup.mk' (pCore 2 K)
        (subgroupOfEquivOfLe (show K ≤ d.overgroup from le_sup_left) k)) := rfl

/-- Minimum order gives the source characteristic-minimality property in the
replacement's own ambient group. -/
theorem Input.replacement_minimal :
    CharacteristicMinimal (K.subgroupOf d.overgroup) d.radical :=
  NaturalSixControl.SymplecticSetup.Reduction.reduced_minimal d
    h.component_normal h.sup_eq_top

/-- The commutator core is preserved through the literal subgroup embedding. -/
theorem Input.replacement_commutatorCore :
    (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
      (blockU K).map K.subtype := by
  let := h.component_normal
  apply d.commutatorCore_eq_intrinsic_of_sup h.sup_eq_top
  rw [← h.residual_eq]
  exact isPPerfect_pResidual 2

variable [Finite F] [CharP F 2]

omit [Finite H] in
/-- Simplicity concerns the replacement's literal component core quotient. -/
theorem Input.replacement_quotient_simple :
    IsSimpleGroup ((K.subgroupOf d.overgroup) ⧸ pCore 2 (K.subgroupOf d.overgroup)) := by
  let := h.quotient_simple
  exact (subgroupOfCoreQuotientEquiv (show K ≤ d.overgroup from le_sup_left)).isSimpleGroup

/-- The replacement's own omega orbit is faithful modulo its own two-core. -/
theorem Input.replacement_omegaOrbit_centralizer :
    centralizer (omegaOrbit d.radical : Set d.overgroup) = pCore 2 d.overgroup := by
  let : (K.subgroupOf d.overgroup).Normal := by
    rw [← h.replacement_residual d]
    infer_instance
  let := h.replacement_quotient_simple d
  exact MSCentralOrbit.omegaOrbit_centralizer (K.subgroupOf d.overgroup) d.radical
    (h.replacement_two_group d) (h.replacement_radical_ne_bot d)
    (h.replacement_core_le d) (h.replacement_core_selfCentralizing d)
    (h.replacement_product d) (h.replacement_characteristic d)

/-- The full central omega layer has the same exact conjugation kernel. -/
theorem Input.replacement_centralOmega_centralizer :
    centralizer (omegaCenterIn (pCore 2 d.overgroup) : Set d.overgroup) =
      pCore 2 d.overgroup :=
  MSCentralOrbit.centralOmega_centralizer d.radical (h.replacement_core_le d)
    (h.replacement_core_selfCentralizing d) (h.replacement_omegaOrbit_centralizer d)

/-- The minimum replacement admits actual positive even critical geometry. -/
theorem Input.replacement_positive_even_geometry :
    ∃ g : Geometry d.radical, 0 < g.b d.radical ∧ Even (g.b d.radical) :=
  exists_positive_even_geometry d.radical (h.replacement_two_group d)
    (h.replacement_radical_ne_bot d) (h.replacement_characteristic d)
    (h.replacement_core_le d) (h.replacement_core_selfCentralizing d)
    (h.replacement_omegaOrbit_centralizer d)

/-- Existence, minimality and positive geometry for the actual Section 7 pair.
The remaining large-distance exclusion must concern this pair. -/
theorem Input.exists_positive_even_replacement :
    ∃ d : CharacteristicReduction K R, ∃ g : Geometry d.radical,
      0 < g.b d.radical ∧ Even (g.b d.radical) ∧
      CharacteristicMinimal (K.subgroupOf d.overgroup) d.radical ∧
      (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
        (blockU K).map K.subtype := by
  obtain ⟨d⟩ := exists_characteristicReduction_of_core_le (L := K) h.radical.twoCore_le
  obtain ⟨g,hpos,heven⟩ := h.replacement_positive_even_geometry d
  exact ⟨d,g,hpos,heven,h.replacement_minimal d,h.replacement_commutatorCore d⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
