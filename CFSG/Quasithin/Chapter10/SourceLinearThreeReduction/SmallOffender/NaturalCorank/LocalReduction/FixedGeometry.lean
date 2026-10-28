module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DisplacementZero
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import CFSG.Quasithin.Chapter10.SourceA5OffenderNormalization

/-!
# Normalization and common fixed spaces for a natural small offender

A stabilizing involution fixes a vector outside the component-fixed part:
otherwise its displacement is in the central kernel and the faithful natural
head forces it to centralize the fully moved factor. The displacement theorem
then gives normalization of the whole offender and the uniform fixed-space
identity. The outside-local intersection is the only earlier input.

Source: Aschbacher--Smith 10.2.12 through (*), printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Every stabilizing involution fixes a vector outside C_W(L), including
when the natural central section has a nonzero kernel. -/
theorem natural_involution_fixed_not_le
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (b : G) (hbM : b ∈ D.maximalLocal)
    (hbN : b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hb2 : b ^ 2 = 1) :
    ¬ ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G) := by
  intro hfixed
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  let := source_full_moved_elementary D
  have hinv : ∀ w ∈ W, w⁻¹ = w := by
    intro w hw
    exact inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw))
  have hs : b*b = 1 := by simpa only [pow_two] using hb2
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hbL := source_original_moved_stabilizer_le_component_normalizer D ht htn
    (m.crossed t ht htn) ⟨hbM,hbN⟩
  have hHZ : H ≤ normalizer (Z : Set G) := source_original_moved_fixed_normalizer D
  have hdisp : ∀ w ∈ W, ⁅b,w⁆ ∈ Z := by
    intro w hw
    have hbw : b*w*b⁻¹ ∈ W := (mem_normalizer_iff.mp hbN w).mp hw
    have hd : ⁅b,w⁆ ∈ W := W.mul_mem hbw (W.inv_mem hw)
    have he : b*⁅b,w⁆*b⁻¹ = ⁅b,w⁆ := by
      change b*(b*w*b⁻¹*w⁻¹)*b⁻¹ = b*w*b⁻¹*w⁻¹
      calc
        _ = (b*b)*w*(b*b)⁻¹ * (b*w*b⁻¹)⁻¹ := by group
        _ = w*(b*w*b⁻¹) := by simp only [hs,one_mul,inv_one,mul_one,hinv _ hbw]
        _ = (b*w*b⁻¹)*w := setLike_mul_comm hw hbw
        _ = _ := by rw [hinv w hw]
    exact ⟨hd,hfixed ⟨hd,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩⟩
  have hbK : b ∈ commutatorPreimage H W Z :=
    (mem_commutatorPreimage_iff H W Z hHZ b).mpr ⟨⟨hbL,hbN⟩,hdisp⟩
  have hker : commutatorPreimage L W Z ≤ centralizer (W : Set G) := by
    rw [moved_quotient_kernel m]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  have hbC := commutatorPreimage_le_centralizer_of_fully_moved H L W Z
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _))
    inf_le_left inf_le_right hHZ inf_le_right (source_full_moved_eq_commutator D) hker hbK
  have hWC : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hbC w hw)
  have hzero := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_inf le_rfl hWC).trans hfixed)
  rw [source_full_moved_eq_commutator D] at hzero
  exact source_full_moved_ne_bot D hzero

/-- At corank at most one the literal offender normalizes W, and every
non-component-fixed offender element has the common fixed space C_W(A).
The only additional premise is the preceding outside-M intersection. -/
theorem natural_offender_geometry
    {g : G} (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    A ≤ normalizer (W : Set G) ∧
      ∀ a ∈ A, a ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) →
        W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  obtain ⟨b,hb,hbM,hbN,hbn⟩ :=
    corank_one_exists_noncentral_normalizing_element D c.nonnormal hsmall
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b (show b ∈ W.map (MulAut.conj g).toMonoidHom from hb)
  have hzero := displacement_eq_bot D c m ht htn hinter ⟨⟨hb,hbM⟩,hbN⟩ hbn
  have hfix : W ⊓ centralizer ({b} : Set G) ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hAN : A ≤ normalizer (W : Set G) :=
    source_nonnormal_normalizes_moved_of_fixed_subgroup D c.nonnormal ht htn
      (m.crossed t ht htn) (W ⊓ centralizer ({b} : Set G)) A inf_le_left
      (natural_involution_fixed_not_le m c.nonnormal b hbM hbN hb2) inf_le_right hfix
  refine ⟨hAN,?_⟩
  intro a ha han
  have hf := normalizer_fixed_space c m hinter ha.1 han
  change W ⊓ centralizer ({a} : Set G) ≤
    centralizer ((A ⊓ normalizer (W : Set G) : Subgroup G) : Set G) at hf
  simpa only [inf_of_le_left hAN] using hf

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
