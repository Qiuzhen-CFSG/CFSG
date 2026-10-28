module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Nonbinary
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleIntermediate

/-!
# The actual diagram-preserving subgroup of a symplectic extension

Take the kernel of the action on the two parabolic conjugacy classes. It is a
normal subgroup containing the marked symplectic socle. A swapping actor makes
it proper. It is supplemented by the ambient Sylow, and its intrinsic
generalized Fitting subgroup is the restricted original socle. The model
isomorphism and induced automorphisms are compatible with the actual inclusions.
This permits applying the separately owned diagram-preserving generation bound.

The final centralizer reduction uses the proved trivial ambient two-core:
tau is the Sylow centralizer. A rank bound for elementary subgroups of the
kernel centralized by a swapping actor therefore puts tau inside the kernel.
That bound is an explicit outstanding model input, not an asserted normal form.
Semilinear classification discharges the premise in the existing outer-cyclicity
theorem; no graph-cocycle descent is assumed here.

Source: Aschbacher--Smith E.1.1--2, E.1.14(1), pp.209--210,214;
F.1.12, pp.263--264; GLS3, Theorems 2.5.1 and 2.5.12(e).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
open DiagramAutomorphisms
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Kernel of the permutation action on the actual two parabolic classes. -/
noncomputable def diagramKernel (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F) : Subgroup G :=
  ((parabolicClassAction hF).comp (extensionAction L e)).ker

/-- The class action is a homomorphism, so its kernel is normal. -/
instance diagramKernel_normal (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F) : (diagramKernel L e hF).Normal := inferInstanceAs
      (((parabolicClassAction hF).comp (extensionAction L e)).ker.Normal)

omit [Finite G] in
/-- Kernel membership is literal preservation of both parabolic conjugacy classes. -/
theorem mem_diagramKernel_iff (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F) (g : G) :
    g ∈ diagramKernel L e hF ↔ PreservesDiagram (extensionAction L e g) :=
  mem_parabolicClassAction_ker_iff hF _

omit [Finite G] [Finite F] [CharP F 2] in
/-- A marked socle element acts as its actual inner automorphism. -/
theorem extensionAction_model_element (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) (x : Sp F) :
    extensionAction L e (e x).val = MulAut.conj x := by
  apply MulEquiv.ext
  intro y
  apply e.injective
  apply Subtype.ext
  rw [extensionAction_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv, coe_mul, coe_inv]

omit [Finite G] in
/-- Inner conjugation preserves both parabolic types. -/
theorem le_diagramKernel (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F) : L ≤ diagramKernel L e hF := by
  intro g hg
  obtain ⟨x, hx⟩ := e.surjective ⟨g, hg⟩
  have he : (e x).val = g := congrArg Subtype.val hx
  rw [mem_diagramKernel_iff, ← he, extensionAction_model_element]
  exact inner_preservesDiagram x

omit [Finite G] in
/-- The original Sylow supplement also supplements the diagram kernel. -/
theorem diagramKernel_sup_sylow (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F) (T : Sylow 2 G) (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    diagramKernel L e hF ⊔ (T : Subgroup G) = ⊤ := by
  apply top_unique
  rw [← hLT]
  exact sup_le_sup_right (le_diagramKernel L e hF) _

omit [Finite G] in
/-- A swapping extension has a proper diagram kernel. -/
theorem diagramKernel_ne_top (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (hF : 2 < Nat.card F)
    (hswap : ∃ g : G, ¬ PreservesDiagram (extensionAction L e g)) :
    diagramKernel L e hF ≠ ⊤ := by
  rintro h
  obtain ⟨g, hg⟩ := hswap
  exact hg ((mem_diagramKernel_iff L e hF g).mp (h.symm ▸ mem_top g))

omit [Finite G] in
/-- Nonbinary symplectic perfectness supplies the needed nonabelianness. -/
theorem symplectic_socle_nonabelian [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hF : 2 < Nat.card F) :
    ¬ IsMulCommutative (generalizedFitting G) := by
  let := perfect_of_card_gt_two hF
  let : Group.IsPerfect (generalizedFitting G) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isMulCommutative _

/-- Fixed-actor rank control gives ambient tau containment for large kernel actors. -/
theorem tau_le_diagramKernel_of_fixed_rank {f : ℕ}
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hF : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hfixed : ∀ (A : Subgroup G), IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≤ diagramKernel (generalizedFitting G) e hF →
      ∀ x ∈ (T : Subgroup G), ¬ PreservesDiagram (extensionAction (generalizedFitting G) e x) →
        x ∈ centralizer (A : Set G) → Group.rank A ≤ f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup G))
    (hAH : A ≤ diagramKernel (generalizedFitting G) e hF) (hr : f < Group.rank A) :
    tau (T : Subgroup G) A ≤ diagramKernel (generalizedFitting G) e hF := by
  have ha := symplectic_socle_nonabelian e hF
  have hcore := (SimpleSocle.structure_of_sylow_supplement ha T hLT).2.2.1
  intro x hx
  apply (mem_diagramKernel_iff _ e hF x).mpr
  by_contra hswap
  have hc : x ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hh := (mem_centralizerModulo_iff.mp hx).2 a ha
    rwa [hcore, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hh
  exact (Nat.not_le_of_gt hr) (hfixed A hA hAT hAH x (tau_le _ _ hx) hswap hc)

/-- Outer cyclicity with the semilinear classification premise discharged. -/
theorem outer_isCyclic {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    IsCyclic (MulAut.Outer (Sp F)) :=
  ExceptionalGraph.outer_isCyclic_of_card hF hf
    SemilinearClassification.inner_field_of_preservesDiagram

omit [Finite G] [Finite F] [CharP F 2] in
/-- Restriction to an intermediate group preserves the marked action exactly. -/
theorem extensionAction_intermediate (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) (H : Subgroup G) (hLH : L ≤ H) (x : H) :
    extensionAction (L.subgroupOf H) (e.trans (subgroupOfEquivOfLe hLH).symm) x =
      extensionAction L e (x : G) := by
  apply MulEquiv.ext
  intro y
  apply e.injective
  apply Subtype.ext
  have he := congrArg (fun z : H => (z : G))
    (extensionAction_apply (L.subgroupOf H)
      (e.trans (subgroupOfEquivOfLe hLH).symm) x y)
  exact he.trans (extensionAction_apply L e (x : G) y).symm

omit [Finite G] [Finite F] [CharP F 2] in
/-- Transport across subgroup equality preserves the induced automorphism. -/
theorem extensionAction_congr (L M : Subgroup G) [L.Normal] [M.Normal]
    (hLM : L = M) (e : Sp F ≃* L) (x : G) :
    extensionAction M (e.trans (MulEquiv.subgroupCongr hLM)) x =
      extensionAction L e x := by
  subst M
  rfl

/-- The full matrix model on the intrinsic generalized Fitting subgroup of the kernel. -/
noncomputable def diagramKernelModel [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hF : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    Sp F ≃* generalizedFitting (diagramKernel (generalizedFitting G) e hF) :=
  (e.trans (subgroupOfEquivOfLe (le_diagramKernel _ e hF)).symm).trans
    (MulEquiv.subgroupCongr
      (SimpleSocle.intermediate_fitting (symplectic_socle_nonabelian e hF) T hLT _
        (le_diagramKernel _ e hF)).symm)

/-- Every intrinsic kernel actor preserves the diagram in this exact model. -/
theorem diagramKernelModel_preserves [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hF : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (x : diagramKernel (generalizedFitting G) e hF) :
    PreservesDiagram (extensionAction _ (diagramKernelModel e hF T hLT) x) := by
  unfold diagramKernelModel
  rw [extensionAction_congr, extensionAction_intermediate]
  exact (mem_diagramKernel_iff _ e hF x).mp x.property

/-- Simplicity and an intrinsic Sylow supplement for the diagram-preserving consumer. -/
theorem diagramKernel_source_structure [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hF : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    let H := diagramKernel (generalizedFitting G) e hF
    IsSimpleGroup (generalizedFitting H) ∧
      ∃ S : Sylow 2 H, generalizedFitting H ⊔ (S : Subgroup H) = ⊤ := by
  let H := diagramKernel (generalizedFitting G) e hF
  have he := SimpleSocle.intermediate_fitting (symplectic_socle_nonabelian e hF) T hLT H
    (le_diagramKernel _ e hF)
  have hs : IsSimpleGroup ((generalizedFitting G).subgroupOf H) :=
    (MulEquiv.isSimpleGroup_congr (subgroupOfEquivOfLe (le_diagramKernel _ e hF))).mpr
      inferInstance
  constructor
  · rw [he]
    exact hs
  · obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal H
    refine ⟨S, ?_⟩
    rw [hS, he]
    exact SimpleSocle.intermediate_sylow_supplement _ T hLT H (le_diagramKernel _ e hF)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
