module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.TwoLayers
public import Theory.Representation.SLThreeCentralExtension.DisjointDisplacement
public import Theory.Representation.BinaryConjugationSection.CentralKernel
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.FixedSpaceTransport

/-!
# Removal of the source point from a natural component cover

For the conjugator selected in the original F.9 geometry, the source point
is disjoint from the opposite span. The component commutator lies in
O₂(LT), and therefore normalizes that span. If its natural-module cover has
a central kernel in the source point, displacement by an opposite-span
involution meets that kernel trivially. The binary three-dimensional
central-extension calculation then makes the cover bijective.

The final specialization uses the literal [U₀,K] and supplies its containment
in O₂(LT) from the original source hypotheses. The quotient marking and its
opposite involution are retained explicitly; this is the kernel-removal
step of original13.5.2(3), not a producer of that earlier marking.
Source: Aschbacher–Smith13.5.2(3), pp.913–914, and13.7.16(2), p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {F : ChapterF.Section09.Setup G}

theorem source_point_disjoint_opposite
    (h : F.Hypothesis) (g : F.LT)
    (hs : (QuotientGroup.mk' (pCore 2 F.LT) g)^2 = 1)
    (hout : ¬ conjugate F.V₁ (g : G) ≤ F.UH) :
    Disjoint F.V₁ (conjugate F.UH (g : G)) := by
  have hu := h.conjugate_twice_eq_of_square (A := F.UH)
    (le_normalizer_conjugateSpanBy F.Vplus F.H)
    (h.square_mem_local_of_core_quotient_square g hs)
  have hcard : Nat.card (conjugate F.V₁ (g : G)) = 2 :=
    (card_map_of_injective (MulAut.conj (g : G)⁻¹).injective).trans h.point_card
  have hi : conjugate F.V₁ (g : G) ⊓ F.UH = ⊥ := by
    let A := conjugate F.V₁ (g : G)
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    apply _root_.eq_bot_iff.mpr
    intro x hx
    by_contra hx1
    have hxne : x ≠ 1 := by simpa only [mem_bot] using hx1
    have hax : (⟨x,hx.1⟩ : A) = a := ha _ (fun he => hxne (congrArg Subtype.val he))
    apply hout
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ F.UH.one_mem
    · have hay := ha (⟨y,hy⟩ : A) (fun he => hy1 (congrArg Subtype.val he))
      have hxy : y = x := congrArg Subtype.val (hay.trans hax.symm)
      rw [hxy]
      exact hx.2
  apply disjoint_iff.mpr
  apply Subgroup.map_injective (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) (MulAut.conj (g : G)⁻¹).injective
  rw [Subgroup.map_bot]
  rw [map_inf _ _ _ (MulAut.conj (g : G)⁻¹).injective]
  change conjugate F.V₁ (g : G) ⊓
    conjugate (conjugate F.UH (g : G)) (g : G) = ⊥
  rw [hu,hi]

theorem natural_cover_bijective_of_opposite
    (h : F.Hypothesis) (g : F.LT)
    (hs : (QuotientGroup.mk' (pCore 2 F.LT) g)^2 = 1)
    (hout : ¬ conjugate F.V₁ (g : G) ≤ F.UH)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWU : W ≤ PlusAction.fixedLayer F)
    (hUQ : F.UH ≤ F.LT.pCoreIn 2)
    (σ : Representation (ZMod 2) BinaryLinearThree.Group (Additive W))
    (p : σ.IntertwiningMap BinaryLinearThree.W)
    (hp : Representation.OneCohomology.IsCover p)
    (hker : ∀ v, p v = 0 → (v.toMul : G) ∈ F.V₁)
    (a : BinaryLinearThree.Group) (ha : orderOf a = 2)
    (u : G) (hu : u ∈ conjugate F.UH (g : G))
    (hact : ∀ v : Additive W, ((σ a v).toMul : G) = u * v.toMul * u⁻¹) :
    Function.Bijective p := by
  have hcore : F.LT ≤ normalizer (F.LT.pCoreIn 2 : Set G) :=
    F.LT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.LT (pCore 2 F.LT))
  have he : conjugate (F.LT.pCoreIn 2) (g : G) = F.LT.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (F.LT.pCoreIn 2 : Set G)).inv_mem (hcore g.property))
  have hQU : F.LT.pCoreIn 2 ≤ normalizer (conjugate F.UH (g : G) : Set G) := by
    have hn : F.LT.pCoreIn 2 ≤ normalizer (F.UH : Set G) :=
      ((h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H).trans
        (le_normalizer_conjugateSpanBy F.Vplus F.H)
    have hm := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom) hn
    rw [map_normalizer_eq_of_bijective F.UH (MulAut.conj (g : G)⁻¹).bijective] at hm
    change conjugate (F.LT.pCoreIn 2) (g : G) ≤ normalizer (conjugate F.UH (g : G) : Set G) at hm
    rw [he] at hm
    exact hm
  have hWN : W ≤ normalizer (conjugate F.UH (g : G) : Set G) :=
    (hWU.trans inf_le_left).trans (hUQ.trans hQU)
  have hdis := source_point_disjoint_opposite h g hs hout
  apply Representation.OneCohomology.SLThreeCentralExtension.cover_bijective_of_disjoint_involution_displacement
    σ p hp a ha
  apply Submodule.disjoint_def.mpr
  intro v hv hr
  obtain ⟨w,hw⟩ := hr
  have hew : (v.toMul : G) = ⁅u,(w.toMul : G)⁆ := by
    rw [←hw]
    change (((σ a w - w).toMul : W) : G) = _
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv]
    rw [hact]
    rfl
  have hc : ⁅u,(w.toMul : G)⁆ ∈ conjugate F.UH (g : G) :=
    le_normalizer_iff_commutator_le_left.mp hWN (commutator_mem_commutator hu w.toMul.property)
  have hv1 : (v.toMul : G) = 1 := hdis.le_bot ⟨hker v hv,hew.symm ▸ hc⟩
  exact Additive.toMul.injective (Subtype.ext hv1)

open Section08.SourceCompletion
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original component commutator has no central point attachment once
its quotient marking and opposite involution are supplied. -/
theorem source_component_natural_cover_bijective
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (K : Subgroup G) (hKH : K ≤ H)
    [IsElementaryAbelian 2 (⁅PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ : Subgroup G)]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group (Additive
      (⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ : Subgroup G)))
    (p : σ.IntertwiningMap BinaryLinearThree.W)
    (hp : Representation.OneCohomology.IsCover p)
    (hker : ∀ v, p v = 0 → (v.toMul : G) ∈ V₁)
    (a : BinaryLinearThree.Group) (ha : orderOf a = 2)
    (u : G) (hu : u ∈ conjugate (Section08.Source.UH H V₃) (g : G))
    (hact : ∀ v, ((σ a v).toMul : G) = u * v.toMul * u⁻¹) :
    Function.Bijective p := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hWU : ⁅PlusAction.fixedLayer F,K⁆ ≤ PlusAction.fixedLayer F :=
    le_normalizer_iff_commutator_le_left.mp
      (hKH.trans (PlusAction.fixedLayer_normalized (D := F)))
  exact natural_cover_bijective_of_opposite h g hs hout _ hWU
    ((le_conjugateSpanBy F.UH L).trans (span_UH_L_le_core d h hU))
    σ p hp hker a ha u hu hact

/-- The natural cover's exact linear coordinates induce multiplicative
coordinates on the original subgroup, with no quotient by the source point. -/
noncomputable def naturalCoverCoordinates
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (p : Additive W →ₗ[ZMod 2] BinaryLinearThree.Vector)
    (hp : Function.Bijective p) :
    W ≃* Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.Model := by
  let f : W →* Multiplicative BinaryLinearThree.Vector := {
    toFun w := Multiplicative.ofAdd (p (Additive.ofMul w))
    map_one' := by change p 0 = 0; exact map_zero p
    map_mul' w x := by
      change p (Additive.ofMul (w*x)) = p (Additive.ofMul w) + p (Additive.ofMul x)
      change p (Additive.ofMul w + Additive.ofMul x) = _
      exact map_add p _ _ }
  exact MulEquiv.ofBijective f
    ⟨fun w x h => Additive.ofMul.injective (hp.1 (Multiplicative.ofAdd.injective h)),
      fun v => by obtain ⟨w,hw⟩ := hp.2 v.toAdd; exact ⟨w.toMul,congrArg Multiplicative.ofAdd hw⟩⟩

omit [Finite G] in
/-- Evaluation of the original subgroup coordinates retains the given linear map. -/
@[simp] theorem naturalCoverCoordinates_apply
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (p : Additive W →ₗ[ZMod 2] BinaryLinearThree.Vector)
    (hp : Function.Bijective p) (w : W) :
    (naturalCoverCoordinates W p hp w).toAdd = p (Additive.ofMul w) := by rfl

end CFSG.Quasithin.Chapter13.Section07
