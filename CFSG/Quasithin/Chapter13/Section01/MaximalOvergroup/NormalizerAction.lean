module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.ReducedModule
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The actual reduced-module quotient at a component normalizer

The quotient M/C_M(R₂(M)), with M=N_G(L), has its faithful conjugation
action and the literal image of L. A nonzero reduced commutator makes
the kernel on L proper, hence solvable by component minimality. When
the radical centralizes R₂(M), the kernel is exactly O∞(L), and the
first isomorphism theorem gives the specified quotient equivalence.
Every radical supplement produces the same reduced commutator.

Source: Aschbacher--Smith 13.1.4(5),13.1.8, pp.867--869.
The source centralization input is discharged in the companion module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.NormalizerReducedAction
open Chapter1
variable {G : Type*} [Group G] [Finite G]
abbrev Ambient (L : Subgroup G) := normalizer (L : Set G)
abbrev Core (L : Subgroup G) := reducedTwoSubgroup (Ambient L)
abbrev Central (L : Subgroup G) := centralizer (Core L : Set (Ambient L))
abbrev Star (L : Subgroup G) := Ambient L ⧸ Central L
@[expose] def quotient (L : Subgroup G) : Ambient L →* Star L := QuotientGroup.mk' _
def componentMap (L : Subgroup G) : L →* Star L :=
  (quotient L).comp (inclusion L.le_normalizer)
def componentImage (L : Subgroup G) : Subgroup (Star L) :=
  (L.subgroupOf (Ambient L)).map (quotient L)

omit [Finite G] in
/-- The component map is the restriction of the original centralizer quotient. -/
theorem componentMap_eq (L : Subgroup G) :
    componentMap L = (quotient L).comp (inclusion L.le_normalizer) := by rfl

omit [Finite G] in
/-- The component image retains the original subgroup and quotient map. -/
theorem componentImage_eq (L : Subgroup G) :
    componentImage L = (L.subgroupOf (Ambient L)).map (quotient L) := by rfl

omit [Finite G] in
theorem componentMap_ker (L : Subgroup G) :
    (componentMap L).ker = (Central L).comap (inclusion L.le_normalizer) := by
  ext x
  change QuotientGroup.mk' (Central L) (inclusion L.le_normalizer x) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

omit [Finite G] in
theorem componentMap_ker_ambient (L : Subgroup G) :
    (componentMap L).ker = (centralizer (normalizerReduced L : Set G)).comap L.subtype := by
  rw [componentMap_ker,normalizerReduced_eq]
  ext x
  constructor
  · intro hx
    change (inclusion L.le_normalizer x) ∈ Central L at hx
    apply mem_centralizer_iff.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx v hv)
  · intro hx
    change (inclusion L.le_normalizer x) ∈ Central L
    apply mem_centralizer_iff.mpr
    intro v hv
    exact Subtype.ext (mem_centralizer_iff.mp hx (v : G) (mem_map_of_mem _ hv))

omit [Finite G] in
theorem componentMap_ker_ne_top {L : Subgroup G} (hne : normalizerMoved L ≠ ⊥) :
    (componentMap L).ker ≠ ⊤ := by
  intro hk
  apply hne
  rw [normalizerMoved_eq, ← normalizerReduced_eq, commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  have hh : (⟨x,hx⟩ : L) ∈ (componentMap L).ker := hk ▸ mem_top _
  rw [componentMap_ker_ambient] at hh
  exact hh

omit [Finite G] in
theorem componentMap_range (L : Subgroup G) :
    (componentMap L).range = componentImage L := by
  ext x
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨inclusion L.le_normalizer l,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

theorem kernel_eq_solvableRadical {S L : Subgroup G} (hL : L ∈ Chapter1.L G S)
    (hne : normalizerMoved L ≠ ⊥)
    (hc : (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G)) :
    (componentMap L).ker = solvableRadical L := by
  have ht : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.1.subgroupOf_of_le le_rfl le_sup_left
  apply le_antisymm (kernel_le_solvableRadical_of_top_isCComponent ht _ (componentMap_ker_ne_top hne))
  rw [componentMap_ker_ambient]
  exact map_le_iff_le_comap.mp hc

noncomputable def radicalQuotientEquiv {S L : Subgroup G} (hL : L ∈ Chapter1.L G S)
    (hne : normalizerMoved L ≠ ⊥)
    (hc : (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G)) :
    (L ⧸ solvableRadical L) ≃* componentImage L :=
  (QuotientGroup.quotientMulEquivOfEq (kernel_eq_solvableRadical hL hne hc).symm).trans
    ((QuotientGroup.quotientKerEquivRange (componentMap L)).trans
      (MulEquiv.subgroupCongr (componentMap_range L)))

theorem radicalQuotientEquiv_mk {S L : Subgroup G} (hL : L ∈ Chapter1.L G S)
    (hne : normalizerMoved L ≠ ⊥)
    (hc : (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G))
    (l : L) :
    (radicalQuotientEquiv hL hne hc (QuotientGroup.mk' (solvableRadical L) l) : Star L) =
      componentMap L l := by
  simp only [radicalQuotientEquiv, MulEquiv.trans_apply]
  rfl

omit [Finite G] in
theorem supplement_commutator {L L₁ : Subgroup G}
    (hc : (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G))
    (hgen : (solvableRadical L).map L.subtype ⊔ L₁ = L) :
    ⁅normalizerReduced L,L₁⁆ = normalizerMoved L := by
  rw [normalizerMoved_eq, ← normalizerReduced_eq]
  apply commutator_eq_of_centralizing_sup hgen hc
  have hle : L₁ ≤ L := hgen ▸ le_sup_right
  apply hle.trans (L.le_normalizer.trans ?_)
  rw [normalizerReduced_eq]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  obtain ⟨w,hw,rfl⟩ := hv
  exact ⟨(⟨g,hg⟩ : normalizer (L : Set G))*w*(⟨g,hg⟩ : normalizer (L : Set G))⁻¹,
    (inferInstance : (reducedTwoSubgroup (normalizer (L : Set G))).Normal).conj_mem w hw ⟨g,hg⟩,rfl⟩


@[expose] noncomputable def action (L : Subgroup G) : Star L →* MulAut (Core L) :=
  QuotientGroup.lift (Central L)
    ((MulAut.conjNormal : Ambient L →* MulAut (Core L)))
    (by rw [MulAut.conjNormal_ker_eq_centralizer])

omit [Finite G] in
theorem action_quotient (L : Subgroup G) (x : normalizer (L : Set G)) :
    action L (quotient L x) = MulAut.conjNormal x := rfl

omit [Finite G] in
theorem action_injective (L : Subgroup G) : Function.Injective (action L) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [MulAut.conjNormal_ker_eq_centralizer]

end CFSG.Quasithin.Chapter13.Section01.NormalizerReducedAction
