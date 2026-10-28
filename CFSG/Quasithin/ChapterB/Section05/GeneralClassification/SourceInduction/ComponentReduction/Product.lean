module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.GroupTheory.DisjointCommutingProduct
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement

/-!
# The product construction in B.5.10

If every best offender on an invariant action image lies in the image of
H, B.1.5 and offender generation show that H surjects onto that action image.
Faithfulness on H makes H disjoint from the kernel. Normality makes these
two subgroups commute, yielding an actual multiplication equivalence.
Centerlessness then identifies the kernel with C_G(H), and with C_G(W).

The model-dependent offender localization, normality and module supplement
remain explicit. This proves the group construction used by B.5.10(2), not
those missing model facts. The consumer below feeds precisely this product
and these original subspaces to the proved complementary-factor descent.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem kernel_disjoint (W : Subrepresentation ρ) (H : Subgroup G)
    (hf : Function.Injective (W.toRepresentation.comp H.subtype)) :
    Disjoint H W.toRepresentation.asGroupHom.ker := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hk
  have he : (⟨x,hx⟩ : H) = 1 := by
    apply hf
    have ht := congrArg Units.val hk
    exact ht.trans (W.toRepresentation.map_one.symm)
  exact congrArg Subtype.val he

private theorem kernel_centralizes (W : Subrepresentation ρ) (H : Subgroup G) [H.Normal]
    (hf : Function.Injective (W.toRepresentation.comp H.subtype)) :
    W.toRepresentation.asGroupHom.ker ≤ centralizer (H : Set G) := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (commutator_le_inf _ _).trans
    (disjoint_iff.mp (kernel_disjoint ρ W H hf).symm).le

private theorem kernel_eq (W : Subrepresentation ρ) :
    W.toRepresentation.asGroupHom.ker = subspaceKernel ρ W.toSubmodule ⊤ := by
  ext x
  constructor
  · intro hx
    refine ⟨mem_top _, ?_⟩
    intro w hw
    exact congrArg Subtype.val (LinearMap.congr_fun (congrArg Units.val hx) (⟨w,hw⟩ : W))
  · rintro ⟨_,hx⟩
    apply Units.ext
    apply LinearMap.ext
    intro w
    exact Subtype.ext (hx w w.property)

/-- The action-image localization step of B.5.10(2). -/
theorem product_of_offender_image [Finite G] [Module.Finite (ZMod 2) V]
    (hgen : offenderSubgroup ρ = ⊤) (W : Subrepresentation ρ)
    (H : Subgroup G) [H.Normal]
    (hf : Function.Injective (W.toRepresentation.comp H.subtype))
    (hz : center H = ⊥)
    (hloc : ∀ A, IsBestOffender (subspaceImageRepresentation ρ W.toSubmodule) A →
      A ≤ restrictedSubgroup ρ W.toSubmodule H) :
    Nonempty (InternalProduct H (centralizer (H : Set G))) ∧
      centralizer (H : Set G) = subspaceKernel ρ W.toSubmodule ⊤ := by
  let hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun g _ v hv => W.apply_mem_toSubmodule g hv)
  let f := invariantActionHom ρ W.toSubmodule hs
  have hr : H.map f = ⊤ := by
    rw [invariantActionHom_map]
    apply top_unique
    rw [← invariant_image_generated ρ W.toSubmodule hs hgen]
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,_⟩
    exact hloc A hA
  have hker : f.ker = W.toRepresentation.asGroupHom.ker :=
    (invariantActionHom_ker ρ _ hs).trans (kernel_eq ρ W).symm
  have hsup : H ⊔ f.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hr, Subgroup.comap_top]
  have hd : Disjoint H f.ker := hker ▸ kernel_disjoint ρ W H hf
  have hc : f.ker ≤ centralizer (H : Set G) := hker ▸ kernel_centralizes ρ W H hf
  obtain ⟨e,he⟩ := Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting H f.ker hd
    (Subgroup.le_centralizer_iff.mp hc)
  let p : InternalProduct H f.ker :=
    ⟨e.trans ((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv), he⟩
  have hceq : centralizer (H : Set G) = f.ker := by
    apply le_antisymm _ hc
    intro x hx
    obtain ⟨a,b,rfl⟩ := p.exists_mul x
    have hac : (a : G) ∈ centralizer (H : Set G) :=
      (centralizer (H : Set G)).mul_mem_cancel_right (hc b.property) |>.mp hx
    have haz : a ∈ center H := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (hac c c.property)
    have ha : a = 1 := by simpa only [hz, mem_bot] using haz
    simpa only [ha, OneMemClass.coe_one, one_mul] using b.property
  constructor
  · rw [hceq]
    exact ⟨p⟩
  · exact hceq.trans (invariantActionHom_ker ρ _ hs)

/-- Construct the actual G-invariant fixed space of a normal first factor. -/
noncomputable def fixedSubrepresentation (H : Subgroup G) [H.Normal] :
    Subrepresentation ρ where
  toSubmodule := fixedSpace ρ H
  apply_mem_toSubmodule g v hv :=
    (fixedSpace_stable_of_normal ρ H (mem_top g) v).2 hv

/-- Assemble the source configuration after the model arguments supply
normality, faithfulness, centerlessness, offender localization and the precise
supplement alternative. The product and centralizer equality are proved here. -/
theorem configuration_of_offender_image [Finite G] [Module.Finite (ZMod 2) V]
    (hgen : offenderSubgroup ρ = ⊤) (W : Subrepresentation ρ)
    (H : Subgroup G) [H.Normal]
    (hf : Function.Injective (W.toRepresentation.comp H.subtype))
    (hz : center H = ⊥)
    (hloc : ∀ A, IsBestOffender (subspaceImageRepresentation ρ W.toSubmodule) A →
      A ≤ restrictedSubgroup ρ W.toSubmodule H)
    (hs : W.toSubmodule ⊔ fixedSpace ρ H = ⊤ ∨ IsExceptional ρ H W) :
    Nonempty (ProductConfiguration ρ H W) := by
  obtain ⟨⟨p⟩,hc⟩ := product_of_offender_image ρ hgen W H hf hz hloc
  exact ⟨⟨inferInstance, inferInstance, fixedSubrepresentation ρ H, rfl, p, hc, hs⟩⟩

/-- The actual B.5.11 consumer obtains all B.5.3 hypotheses and strict descent
from the configuration; it needs no extra faithfulness or generation premise. -/
theorem ProductConfiguration.descent [Finite G] {K : CFSG.Quasithin.GroupClass}
    {H : Subgroup G} {W : Subrepresentation ρ}
    (c : ProductConfiguration ρ H W) (hyp : FFHypothesis K ρ) (hne : H ≠ ⊥) :
    Nat.card (centralizer (H : Set G)) < Nat.card G ∧
      FFHypothesis K (c.fixed.toRepresentation.comp (centralizer (H : Set G)).subtype) := by
  apply hyp.descent_to_second ρ c.product hne W c.fixed
  · rw [c.centralizer_eq]
    exact le_fixedSpace_subspaceKernel ρ W.toSubmodule ⊤
  · exact c.fixed_eq.le
  · rcases c.configuration with hs | he
    · exact Or.inl hs
    · right
      rw [c.fixed_eq]
      exact he.2
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
