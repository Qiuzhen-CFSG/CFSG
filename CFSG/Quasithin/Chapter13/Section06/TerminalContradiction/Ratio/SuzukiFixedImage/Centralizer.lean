module
public import Theory.Representation.FixedIsotypicCentralizer
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceStarComponent
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceConstituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourceSteinbergCoordinates
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.SmallRatioTransport
public import Theory.Representation.BinaryOffender.ScalarExtensionBudget

/-!
# The original quadratic actor in the Suzuki centralizer

The source trivial/Steinberg type span and the actor theorem may choose
different markings of the same component quotient. Full Steinberg invariance
under every Suzuki automorphism aligns those markings. Each original
intertwiner image then lies in the canonical isotypic part fixed by the actor.

Consequently the same actor in H/O₂(H) commutes with the original Suzuki
image. Restricting the whole binary module to that centralizer retains full
faithfulness, SQTK, the actor's exact rank and fixed codimension, and its
quadratic ratio bound. No direct summand is assumed faithful, no constituent
is selected, and no actor is replaced by a possibly smaller action image.

The centralizer generalized-Fitting calculation and final exceptional strict
bound have independent producers consumed by the terminal assembly owner.
Source: Aschbacher--Smith, §13.6, printed pp.934--935.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SuzukiFixedImage
open Section08 Components.SuzukiIsolation BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {H D V₃ V₁ : Subgroup G}
    (hDH : D ≤ H) (hHD : H ≤ normalizer (D : Set G))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K]
attribute [local instance] sourceSpanCommGroup

omit [Algebra (ZMod 2) K] in
include hm in
/-- Changing the actual component quotient marking preserves the full Steinberg type. -/
theorem markedSteinberg_equiv
    (f g : SuzukiMatrixGroup m ≃* (D ⧸ pCore 2 D)) :
    Nonempty ((markedComponentSteinberg hDH K f).Equiv
      (markedComponentSteinberg hDH K g)) := by
  obtain ⟨e⟩ := SuzukiSmallDegree.full_tensor_comp_equiv hm K (g.trans f.symm)
  refine ⟨.mk e.toLinearEquiv (fun d => ?_)⟩
  have he := e.isIntertwining' (markedComponentProjection hDH g d)
  simpa only [markedComponentSteinberg, markedComponentProjection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, g.apply_symm_apply] using he

include hm in
set_option backward.isDefEq.respectTransparency false in
/-- The full original Steinberg type span lies in the canonical isotypic part
for any marking returned by the actor calculation. -/
theorem source_typeSpan_le_isotypic
    (f g : SuzukiMatrixGroup m ≃* (D ⧸ pCore 2 D)) :
    (typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
      (markedComponentSteinberg hDH K f)).toSubmodule ≤
    (Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
      (Representation.asModule (markedExtendedComponentRepresentation hn hk hDH hHD K g))
      (SuzukiSmallDegree.tensorRep m K Finset.univ).asModule)).toSubmodule := by
  obtain ⟨e⟩ := markedSteinberg_equiv hDH hm K f g
  rw [typeSpan_eq_of_equiv _ e]
  have he := markedExtendedComponentRepresentation_comp hn hk hDH hHD K g
  change (markedExtendedComponentRepresentation hn hk hDH hHD K g).comp
    (markedComponentProjection hDH g) = _ at he
  rw [← he]
  change (typeSpan ((markedExtendedComponentRepresentation hn hk hDH hHD K g).comp _)
    ((SuzukiSmallDegree.tensorRep m K Finset.univ).comp (markedComponentProjection hDH g))).toSubmodule ≤ _
  rw [typeSpan_comp_surjective _ (markedComponentProjection_surjective hDH g)]
  let := SuzukiSmallDegree.tensorRep_irreducible hm (K := K) Finset.univ
  exact typeSpan_le_isotypicComponent _ _

include hm in
set_option backward.isDefEq.respectTransparency false in
/-- Fixation of the full canonical Steinberg part puts the same original
star actor inside the centralizer of the literal Suzuki image. -/
theorem source_actor_le_centralizer
    (f g : SuzukiMatrixGroup m ≃* (D ⧸ pCore 2 D))
    (hspan : typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (trivial K (D.subgroupOf H) K) ⊔
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (markedComponentSteinberg hDH K f) = ⊤)
    (B : Subgroup (Source.Hstar H))
    (hfix : ∀ (b : B) (v : (Subrepresentation.ofSubmodule'
      (isotypicComponent K[SuzukiMatrixGroup m]
        (Representation.asModule (markedExtendedComponentRepresentation hn hk hDH hHD K g))
        (SuzukiSmallDegree.tensorRep m K Finset.univ).asModule)).toSubmodule),
      (extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v = v) :
    B ≤ centralizer (Source.starImage H D : Set (Source.Hstar H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let σ := starRepresentation H V₃ V₁ hn hk
  have he : σ.comp q = representation H V₃ V₁ hn := by
    ext a v
    exact DFunLike.congr_fun (starRepresentation_mk H V₃ V₁ hn hk a) v
  let : (D.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHD
  apply le_centralizer_image_of_fixed_typeSpan q (QuotientGroup.mk'_surjective _)
    σ (starRepresentation_injective H V₃ V₁ hn hk) (D.subgroupOf H)
    (markedComponentSteinberg hDH K f) (by rw [he]; exact hspan) B
  intro a ha v hv
  have hv' : v ∈ typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp
      (D.subgroupOf H).subtype) (markedComponentSteinberg hDH K f) := by
    rw [he] at hv
    exact hv
  have hh := hfix ⟨q a,ha⟩ ⟨v,source_typeSpan_le_isotypic hDH hHD hn hk hm K f g hv'⟩
  simpa only [extendScalars_apply, MonoidHom.comp_apply, starRepresentation_mk, q, σ] using hh

include hm hHD in
set_option backward.isDefEq.respectTransparency false in
/-- The proved Steinberg actor theorem directly supplies centralizer containment;
only its genuine source kernel and displacement bounds remain as inputs. -/
theorem source_small_actor_le_centralizer [Finite G]
    (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hspan : ∃ f : SuzukiMatrixGroup m ≃* (D ⧸ pCore 2 D),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (trivial K (D.subgroupOf H) K) ⊔
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (markedComponentSteinberg hDH K f) = ⊤)
    (B : Subgroup (Source.Hstar H)) (hB : ∀ b : B, b ^ 2 = 1)
    (hquad : ∀ (a b : B) v,
      (extendScalars K (starRepresentation H V₃ V₁ hn hk)) a
        ((extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v - v) =
      (extendScalars K (starRepresentation H V₃ V₁ hn hk)) b v - v)
    (hker : Nat.card ((centralizer (Source.starImage H D : Set (Source.Hstar H))).subgroupOf B) ≤ 2048)
    (hsmall : ∀ b : B, Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
      ((extendScalars K (starRepresentation H V₃ V₁ hn hk)) b) ≤ 2 * Nat.log 2 (Nat.card B)) :
    B ≤ centralizer (Source.starImage H D : Set (Source.Hstar H)) := by
  obtain ⟨f,hf⟩ := hspan
  obtain ⟨g,hg⟩ := source_star_steinberg_fixed hn hk hDH hHD hm e K B hB hquad hker hsmall
  exact source_actor_le_centralizer hDH hHD hn hk hm K f g hf B hg

include hm hHD in
set_option backward.isDefEq.respectTransparency false in
/-- The binary source budget discharges the scalar-extension premises of the
Steinberg fixation theorem and yields the same literal centralizer inclusion. -/
theorem source_small_actor_le_centralizer_of_binary_budget [Finite G]
    (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hspan : ∃ f : SuzukiMatrixGroup m ≃* (D ⧸ pCore 2 D),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (trivial K (D.subgroupOf H) K) ⊔
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (D.subgroupOf H).subtype)
        (markedComponentSteinberg hDH K f) = ⊤)
    (B : Subgroup (Source.Hstar H))
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hquad : Representation.BinaryOffender.IsQuadratic
      (starRepresentation H V₃ V₁ hn hk) B)
    (hker : Nat.card ((centralizer (Source.starImage H D : Set (Source.Hstar H))).subgroupOf B) ≤ 2048)
    (hsmall : Representation.BinaryOffender.fixedCodim
      (starRepresentation H V₃ V₁ hn hk) B ≤
        2 * Representation.BinaryOffender.rank B) :
    B ≤ centralizer (Source.starImage H D : Set (Source.Hstar H)) := by
  let : IsElementaryAbelian 2 B := hB.2
  apply source_small_actor_le_centralizer hDH hHD hn hk hm K e hspan B
  · intro b
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) b
  · exact hquad.extendScalars
  · exact hker
  · exact Representation.BinaryOffender.extendScalars_operatorFixedCodim_le_of_fixedCodim
      (starRepresentation H V₃ V₁ hn hk) B hsmall

section Restriction
open Representation.BinaryOffender
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- A small quadratic actor keeps exactly its rank and displacement when the
whole module is restricted to any subgroup containing that actor. -/
theorem quadraticRatio_comp_subtype_le_two
    (ρ : Representation (ZMod 2) X W) (C B : Subgroup X) (hBC : B ≤ C)
    (hB : IsElementaryTwo B) (hq : IsQuadratic ρ B)
    (hsmall : fixedCodim ρ B ≤ 2 * rank B) :
    quadraticRatio (ρ.comp C.subtype) ≤ 2 := by
  let : IsElementaryAbelian 2 B := hB.2
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨B.subgroupOf C,⟨?_,IsElementaryAbelian.subgroupOf hBC⟩,?_,?_⟩
  · intro hz
    apply hB.1
    rw [← map_subgroupOf_eq_of_le hBC,hz,Subgroup.map_bot]
  · intro a ha b hb v
    exact hq a.val ha b.val hb v
  · rw [fixedCodim_subgroupOf ρ hBC,rank_subgroupOf hBC]
    exact hsmall

/-- Restriction to the centralizer preserves the original actor's full rank,
its fixed codimension, and its quadratic action on the entire module. -/
theorem same_actor_on_centralizer
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    {κ : GroupClass.{u}} (hsq : IsSQTK κ X)
    (D B : Subgroup X) (hBD : B ≤ centralizer (D : Set X))
    (hB : IsElementaryTwo B) (hq : IsQuadratic ρ B)
    (hsmall : fixedCodim ρ B ≤ 2 * rank B) :
    let C := centralizer (D : Set X)
    Function.Injective (ρ.comp C.subtype) ∧ IsSQTK κ C ∧
    IsElementaryTwo (B.subgroupOf C) ∧
    IsQuadratic (ρ.comp C.subtype) (B.subgroupOf C) ∧
    rank (B.subgroupOf C) = rank B ∧
    fixedCodim (ρ.comp C.subtype) (B.subgroupOf C) = fixedCodim ρ B ∧
    quadraticRatio (ρ.comp C.subtype) ≤ 2 := by
  let C := centralizer (D : Set X)
  let : IsElementaryAbelian 2 B := hB.2
  have he : IsElementaryTwo (B.subgroupOf C) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hBD⟩
    intro hz
    apply hB.1
    rw [← map_subgroupOf_eq_of_le hBD, hz, Subgroup.map_bot]
  have hq' : IsQuadratic (ρ.comp C.subtype) (B.subgroupOf C) := by
    intro a ha b hb v
    exact hq a.val ha b.val hb v
  refine ⟨hf.comp C.subtype_injective, hsq.subgroup C, he, hq',
    rank_subgroupOf hBD, fixedCodim_subgroupOf ρ hBD, ?_⟩
  exact quadraticRatio_comp_subtype_le_two ρ C B hBD hB hq hsmall
end Restriction

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SuzukiFixedImage
