module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.LocalKernel
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.StructureTransport
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.Components
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage

/-!
# Assembly of the HS inner centralizer calculations

Simplicity and perfectness, inherited from the source's simple-group setup,
make the inner action faithful. Thus an inner involutory automorphism comes
from an element of order two. Exhaustive element-class coverage then transports
the representative centralizers to its entire fixed subgroup.

The central class has a proved self-centralizing normal two-kernel and no
components. In the product class every component is A₆ and the ambient
fixed-subgroup index is 15400. The exact embedded central product and normal
S₅ quotient transport without imposing a splitting.

Source: Aschbacher–Smith, 16.1.5(10), 16.1.7(h), and 16.1.8, pp.1172–1173;
GLS3, Table 5.3m. `CoreStructure` and `ClassCoverage` discharge the representative
extension and exhaustive coverage inputs. The final inner alternatives retain
only the inherited simplicity and perfectness hypotheses, the order-two
condition, and innerness. The conditional assembly APIs remain available.
The outer alternatives and the full source-theorem assembly are separate.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

variable [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]

/-- The source simplicity and perfectness hypotheses make the inner action faithful. -/
theorem conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
  have hZ : center Carrier = ⊥ := by
    rcases (inferInstance : (center Carrier).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Carrier (center_eq_top_iff.mp h)).elim
  apply (MulAut.conj : Carrier →* MulAut Carrier).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have he : MulAut.conj x = 1 := hx
  have hc : x ∈ center Carrier := by
    rw [mem_center_iff]
    intro y
    have hy := congrArg (fun a : MulAut Carrier => a y) he
    change x * y * x⁻¹ = y at hy
    exact ((mul_inv_eq_iff_eq_mul).mp hy).symm
  simpa only [hZ] using hc

section Conditional

variable (hcover : ∀ x : Carrier, orderOf x = 2 →
  IsConj e0 x ∨ Nonempty (centralizer ({x} : Set Carrier) ≃* C2 × MulAut A6))

include hcover

/-- Element-class coverage suffices for exhaustive coverage of inner fixed subgroups. -/
theorem inner_fixed_representatives (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* centralizer ({e0} : Set Carrier)) ∨
      Nonempty (r.fixedSubgroup ≃* C2 × MulAut A6) := by
  obtain ⟨x, rfl⟩ := hi
  have hx : orderOf x = 2 := (orderOf_injective MulAut.conj conj_injective x).symm.trans hr
  rcases hcover x hx with hc | he
  · exact Or.inl (fixed_equiv_centralizer_of_isConj hc)
  · obtain ⟨e⟩ := he
    exact Or.inr ⟨(MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj x)).trans e⟩

/-- The two remaining concrete calculations imply the exact source inner alternatives. -/
theorem inner_alternative_of_classification
    (hcore : IsHSCoreExtension (centralizer ({e0} : Set Carrier)))
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) : HSInvolutionAlternative r := by
  refine Or.inl ⟨hi, ?_⟩
  rcases inner_fixed_representatives hcover r hr hi with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl (coreExtension_transport e.symm hcore)
  · exact Or.inr he

/-- Coverage alone suffices for the component and index consequences:
the central class is excluded using its actual kernel action. -/
theorem component_and_index_of_classification
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    Nonempty (K ≃* A6) ∧ 4 ∣ r.fixedSubgroup.index := by
  rcases inner_fixed_representatives hcover r hr hi with he | he
  · obtain ⟨e⟩ := he
    exact ((selfCentralizing_transport e.symm centralizer_selfCentralizing).not_isComponent K hK).elim
  · obtain ⟨e⟩ := he
    exact ⟨component_equiv_of_fixed_equiv r e K hK, four_dvd_fixed_index_of_equiv r e⟩

end Conditional

/-- Exhaustive inner alternatives, including the proved kernel action in the
core-extension class. Every representative calculation is discharged. -/
theorem inner_structure (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    (IsHSCoreExtension r.fixedSubgroup ∧
      HasSelfCentralizingNormalTwoSubgroup r.fixedSubgroup) ∨
    Nonempty (r.fixedSubgroup ≃* C2 × MulAut A6) := by
  rcases inner_fixed_representatives ClassCoverage.involution_alternative r hr hi with he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨coreExtension_transport e.symm centralizer_coreExtension,
      selfCentralizing_transport e.symm centralizer_selfCentralizing⟩
  · exact Or.inr he

/-- The exact inner centralizer alternatives of source 16.1.5(10). -/
theorem inner_centralizer_alternative (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    IsHSCoreExtension r.fixedSubgroup ∨ Nonempty (r.fixedSubgroup ≃* C2 × MulAut A6) :=
  (inner_structure r hr hi).imp And.left id

/-- The inner branch of the complete source table, with no additional model premise. -/
theorem inner_alternative (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) : HSInvolutionAlternative r :=
  inner_alternative_of_classification ClassCoverage.involution_alternative
    centralizer_coreExtension r hr hi

/-- Within the actual inner centralizers, the core-extension shape selects the
class with a self-centralizing normal two-kernel. The product class is excluded
by its different order; the kernel action itself comes from the checked model. -/
theorem inner_core_selfCentralizing (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (hcore : IsHSCoreExtension r.fixedSubgroup) :
    HasSelfCentralizingNormalTwoSubgroup r.fixedSubgroup := by
  rcases inner_structure r hr hi with ⟨_, hself⟩ | he
  · exact hself
  · obtain ⟨e⟩ := he
    have hc := coreExtension_card hcore
    rw [Nat.card_congr e.toEquiv, ClassCoverage.product_card] at hc
    norm_num at hc

/-- Every component of an inner involution centralizer is actually A₆,
as needed in the inner HS case of source 16.1.7(h). -/
theorem inner_component_equiv (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    Nonempty (K ≃* A6) :=
  (component_and_index_of_classification ClassCoverage.involution_alternative r hr hi K hK).1

/-- If a component exists, the entire inner fixed subgroup has index 15400. -/
theorem inner_component_index (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    r.fixedSubgroup.index = 15400 := by
  rcases inner_structure r hr hi with ⟨_, hself⟩ | he
  · exact (hself.not_isComponent K hK).elim
  · obtain ⟨e⟩ := he
    exact fixed_index_of_equiv r e

/-- The index bound used in the inner HS case of source 16.1.8. -/
theorem four_dvd_index_of_inner_component (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    4 ∣ r.fixedSubgroup.index := by
  rw [inner_component_index r hr hi K hK]
  decide

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
