module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.AlternatingEightExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Recognition
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Displacement

/-!
# Excluding normal irreducible Mathieu components on the original flag

The ten-dimensional M₂₂ code and cocode are not self-dual: the native point
stabilizer fixes a nonzero cocode vector but no code vector. Their explicit
duality therefore contradicts the original invariant nondegenerate form.

For the triple cover, James's equivalence identifies the actual normal
component action in degree twelve. Its matrix normalizer identifies the
whole group once the original actor-rank inequality forces a proper outer
extension. Transport through the literal terminal quotient then supplies
the coordinates of the existing source Mathieu contradiction. No equality
between the component and the generalized Fitting subgroup is assumed.

Source: Aschbacher--Smith G.7.3(2), H.12.1(3), H.13.1, H.15.1(2),
and 14.4.2(6),14.4.12--14; printed pp.348,394--398,1006,1011--1012;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MathieuComponent
open MathieuCode Sporadic.Mathieu

private def transportSelfDual {D V W : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) D W}
    (e : ρ.Equiv σ) (d : σ.Equiv σ.dual) : ρ.Equiv ρ.dual :=
  (e.trans d).trans (.mk e.toLinearEquiv.dualMap (by
    intro g
    ext f v
    exact congrArg f (LinearMap.congr_fun (e.isIntertwining' g⁻¹) v).symm))

private theorem cocode_not_selfDual
    (s : m22CocodeRepresentation.Equiv m22CocodeRepresentation.dual) : False := by
  let z := m22WeightTwoVector 0
  let w := m22CodeCocodeDuality.symm (s z)
  have hw : w ∈ fixedSpace m22CodeRepresentation (MulAction.stabilizer M22 (0 : Fin 22)) := by
    intro g
    apply m22CodeCocodeDuality.injective
    change m22CodeCocodeDuality (m22CodeRepresentation g.val w) = m22CodeCocodeDuality w
    rw [m22CodeCocodeDuality_equivariant_native]
    dsimp only [w]
    rw [m22CodeCocodeDuality.apply_symm_apply]
    have he := LinearMap.congr_fun (s.isIntertwining' g.val) z
    change s (m22CocodeRepresentation g.val z) = m22CocodeRepresentation.dual g.val (s z) at he
    rw [← he,(m22WeightTwoVector_fixed_iff g.val 0).mpr g.property]
  rw [m22PointStabilizer_code_fixed_eq_bot,Submodule.mem_bot] at hw
  have hs : s z = 0 := by
    rw [← m22CodeCocodeDuality.apply_symm_apply (s z)]
    change m22CodeCocodeDuality w = 0
    rw [hw,map_zero]
  exact m22WeightTwoVector_ne_zero 0 (s.toLinearEquiv.map_eq_zero_iff.mp hs)

private theorem code_not_selfDual
    (s : m22CodeRepresentation.Equiv m22CodeRepresentation.dual) : False := by
  let z := m22WeightTwoVector 0
  let f : Module.Dual (ZMod 2) M22Code := m22CodeCocodeDuality.toLinearMap.flip z
  have hf : ∀ g : MulAction.stabilizer M22 (0 : Fin 22),
      m22CodeRepresentation.dual g.val f = f := by
    intro g
    ext u
    change m22CodeCocodeDuality (m22CodeRepresentation g.val⁻¹ u) z =
      m22CodeCocodeDuality u z
    rw [m22CodeCocodeDuality_equivariant_native]
    change m22CodeCocodeDuality u (m22CocodeRepresentation (g.val⁻¹)⁻¹ z) = _
    rw [inv_inv,(m22WeightTwoVector_fixed_iff g.val 0).mpr g.property]
  have hw : s.symm f ∈ fixedSpace m22CodeRepresentation
      (MulAction.stabilizer M22 (0 : Fin 22)) := by
    intro g
    change m22CodeRepresentation g.val (s.symm f) = s.symm f
    have he := LinearMap.congr_fun (s.symm.isIntertwining' g.val) f
    change s.symm (m22CodeRepresentation.dual g.val f) = m22CodeRepresentation g.val (s.symm f) at he
    rw [← he,hf g]
  rw [m22PointStabilizer_code_fixed_eq_bot,Submodule.mem_bot] at hw
  have hz : f = 0 := by rw [← s.apply_symm_apply f, hw, map_zero]
  apply m22WeightTwoVector_ne_zero 0
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) z).mp
  intro φ
  obtain ⟨u,rfl⟩ := m22CodeCocodeDuality.surjective φ
  exact LinearMap.congr_fun hz u

private theorem not_model
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {B : LinearMap.BilinForm (ZMod 2) W}
    {v : W} {E : Submodule (ZMod 2) W} {X C : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X C C
      (finrank (ZMod 2) (Additive X)))
    (e : C ≃* M22) : False := by
  have hd := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  have hb := m22_automorphism_twoRank_le_five
  let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  obtain ⟨a,hc | hc⟩ := Representation.MathieuSmall.M22Recognition.of_small_degree σ
    (h.faithful.comp (C.subtype_injective.comp e.symm.injective)) (by omega)
  all_goals
    obtain ⟨f⟩ := hc
    let σ' : Representation (ZMod 2) M22 W := σ.comp a.symm.toMonoidHom
    have hs : σ'.Equiv σ'.dual := .mk (B.toDual h.nondegenerate) (by
      intro g
      ext u w
      change B (ρ (e.symm (a.symm g)) u) w =
        B u (ρ (e.symm (a.symm g⁻¹)) w)
      have hh := h.preserves (e.symm (a.symm g)) u (ρ (e.symm (a.symm g⁻¹)) w)
      simpa only [← Module.End.mul_apply, ← map_mul, map_inv, Subgroup.coe_inv,
        mul_inv_cancel, map_one, Module.End.one_apply] using hh)
  · have ef : σ'.Equiv m22CocodeRepresentation := .mk f.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro u
      change f (σ (a.symm g) u) = m22CocodeRepresentation g (f u)
      have hh := LinearMap.congr_fun (f.isIntertwining' (a.symm g)) u
      change f (σ (a.symm g) u) = m22CocodeRepresentation (a (a.symm g)) (f u) at hh
      rw [a.apply_symm_apply] at hh
      exact hh)
    exact cocode_not_selfDual (transportSelfDual ef.symm hs)
  · have ef : σ'.Equiv m22CodeRepresentation := .mk f.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro u
      change f (σ (a.symm g) u) = m22CodeRepresentation g (f u)
      have hh := LinearMap.congr_fun (f.isIntertwining' (a.symm g)) u
      change f (σ (a.symm g) u) = m22CodeRepresentation (a (a.symm g)) (f u) at hh
      rw [a.apply_symm_apply] at hh
      exact hh)
    exact code_not_selfDual (transportSelfDual ef.symm hs)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MathieuComponent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original invariant alternating form excludes a normal irreducible
M₂₂ component, including the separate fixed-line clause. -/
theorem source_no_mathieu_twenty_two_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* Sporadic.Mathieu.M22) : False := by
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  exact MathieuComponent.not_model hyp h9 e₀

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

public noncomputable section

open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative Matrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Mathieu
open LargerDimension.LocalAction.Components
open ChapterH.Section10To12
open Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private theorem mathieu_coordinates_of_normal_irreducible_component
    {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) W = 12)
    (K : Subgroup Q) [K.Normal] (hK : IsTripleM22 K)
    [IsIrreducible (ρ.comp K.subtype)]
    (hproper : K ≠ ⊤) :
    ∃ e : Q ≃* ActorCatalogue.Native.Model,
    ∃ c : W ≃ₗ[ZMod 2] ActorCatalogue.Native.Space,
      ∀ a w, c (ρ a w) = ActorCatalogue.Native.action (e a) (c w) := by
  obtain ⟨c⟩ := hK.equiv_binaryRepresentation_of_finrank_twelve (ρ.comp K.subtype)
    (hf.comp K.subtype_injective) hd
  let e := hK.groupEquiv
  let f : Q →* Matrix12ˣ :=
    (Units.mapEquiv Matrix.toLinAlgEquiv'.symm.toMulEquiv).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c.toLinearEquiv).toMonoidHom.comp
        ρ.asGroupHom)
  have hact (a : Q) (w : W) :
      (f a : Matrix12) *ᵥ (c w) = c (ρ a w) := by
    change (Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm
      (c.toLinearEquiv.conjRingEquiv (ρ a)))) (c w) = _
    rw [Matrix.toLinAlgEquiv'.apply_symm_apply]
    change c (ρ a (c.toLinearEquiv.symm (c w))) = c (ρ a w)
    exact congrArg (fun x => c (ρ a x)) (c.toLinearEquiv.symm_apply_apply w)
  have hfi : Function.Injective f := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro w
    apply c.injective
    change c (ρ a w) = c (ρ b w)
    rw [← hact,← hact,hab]
  have hcomp (k : K) : f k = (e k).val := by
    apply Units.ext
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := c.toLinearEquiv.surjective w
    change (f k : Matrix12) *ᵥ (c v) = M22TripleCover.binaryRepresentation (e k) (c v)
    rw [hact]
    exact Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap k v
  have hm : K.map f = derivedGroup := by
    ext a
    constructor
    · rintro ⟨k,hk,rfl⟩
      rw [hcomp ⟨k,hk⟩]
      exact (e ⟨k,hk⟩).property
    · intro ha
      obtain ⟨k,hk⟩ := e.surjective ⟨a,ha⟩
      exact ⟨k,k.property,(hcomp k).trans (congrArg Subtype.val hk)⟩
  refine ⟨ActorCatalogue.Native.equivOfMatrixComponent K f hfi hm hproper,
    c.toLinearEquiv,?_⟩
  intro a w
  rw [ActorCatalogue.Native.equivOfMatrixComponent_action]
  exact (hact a w).symm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual normal irreducible triple component supplies the native whole
Mathieu coordinates and therefore the original large-case contradiction. -/
theorem source_no_triple_mathieu_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (C : Subgroup F.TerminalHdot) [C.Normal]
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : Chapter1.Section02.LocalModels.IsM22Cover C)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 12) : False := by
  let hC : IsTripleM22 C := {
    quasisimple := model.1
    center_card := (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
    centralQuotient := model.2.2 }
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,hx,B,v,hyp⟩ := source_terminal_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  have hproper : C ≠ ⊤ := by
    intro ht
    let e : F.TerminalHdot ≃* M22TripleCover :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht).symm.trans hC.groupEquiv)
    have hr : Group.rank (F.terminalDot (F.X g)) ≤ 4 := by
      have h := Subgroup.rank_le_primeRank 2 (F.terminalDot (F.X g))
        (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
      exact h.trans ((primeRank_congr 2 e).trans_le M22TripleCover.NoFF.twoRank_le_four)
    have hqrank := Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)
    have hb := hyp.dimension_bound.1
    rw [hd] at hb
    omega
  let := hirr
  obtain ⟨e,c,hc⟩ := mathieu_coordinates_of_normal_irreducible_component
    F.terminalRepresentation F.terminalRepresentation_injective hd C hC hproper
  let q := QuotientGroup.quotientMulEquivOfEq
    (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ).symm
  exact source_mathieu_contradiction d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH (q.trans e) c (fun a w => (hc _ w).symm)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
