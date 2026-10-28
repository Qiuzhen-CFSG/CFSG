module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSix

/-!
# The tensor rows of the original G.11 catalogue

All four concrete G.11.2(9) actions are transported to the literal H/O₂(H)
action, with the source order of tensor factors and the original A₅ marking.
For the natural S₅ extension, the five-line isomorphism is checked on its
actual determinant-one subgroup. The resulting marked coordinates feed the
proved large-case tensor exclusion.

The equal-sign extension in G.11.2(10) contains the actual A₆ × C₃ subgroup.
Its three-rank contradicts the bound inherited by the terminal quotient from
the original SQTK group. No action identification is inferred from orders.

Source: Aschbacher--Smith G.11.2(9--10), 14.4.2(5) and its exclusion of
G.11.2(10), printed pp.364,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueTensor
open LargerDimension LargerDimension.Tensor
open Representation.RankTwo.TensorModels
universe w
variable {H W : Type*} [Group H] {U : Subgroup H} [U.Normal]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem tensor_of_model {A : Type*} [Group A]
    {Z : Type w} [AddCommGroup Z] [Module (ZMod 2) Z]
    (d : RankCore.SourceAction H U W) (τ : Representation (ZMod 2) A Z)
    (D : Subgroup Five) (hAD : AltFive ≤ D) (hD : D = ⊤ ∨ D = AltFive)
    (θ : A ≃* D) (hτ : IsSourceConstituent hAD (τ.comp θ.symm.toMonoidHom))
    (e : (H ⧸ pCore 2 H) ≃* A × Three)
    (f : W ≃ₗ[ZMod 2] (Z ⊗[ZMod 2] BinaryPermutation.core (Fin 3)))
    (hf : ∀ a v, f (d.representation a v) = BinaryPermutation.ThreeTensor.action τ (e a) (f v)) :
    RankCore.ActionAlternative.{w} d := by
  let σ := τ.comp θ.symm.toMonoidHom
  let s := TensorProduct.comm (ZMod 2) Z (BinaryPermutation.core (Fin 3))
  let e' := e.trans ((MulEquiv.prodCongr θ (MulEquiv.refl Three)).trans MulEquiv.prodComm)
  refine .tensor D hAD σ hD hτ e' (f.trans s) ?_
  intro a v
  change s (f (d.representation a v)) = sourceTensorAction σ (e' a) (s (f v))
  rw [hf]
  generalize f v = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul z n =>
    change s (τ (e a).1 z ⊗ₜ[ZMod 2]
      BinaryPermutation.coreRepresentation (Fin 3) (e a).2 n) =
      BinaryPermutation.coreRepresentation (Fin 3) (e a).2 n ⊗ₜ[ZMod 2]
        τ (θ.symm (θ (e a).1)) z
    simp [s]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem natural_marking (a : AltFive) :
    Natural.groupEquiv.symm a.val = Natural.inclusion (Natural.alternatingEquiv.symm a) := by
  apply Natural.groupEquiv.injective
  rw [Natural.groupEquiv.apply_symm_apply]
  rw [show Natural.groupEquiv (Natural.inclusion (Natural.alternatingEquiv.symm a)) =
    Representation.SL2FourNatural.SemilinearNormalizer.specialFiveLines
      (Natural.alternatingEquiv.symm a) from
    Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv_special_apply _]
  exact congrArg Subtype.val (Natural.alternatingEquiv.apply_symm_apply a).symm

/-- Every concrete G.11 tensor action gives the source tensor row, with the
same whole-group and vector identifications and the source order of factors. -/
theorem of_case_nine [FiniteDimensional (ZMod 2) W]
    {K : Type*} [Group K] [Finite K]
    (d : RankCore.SourceAction H U W) (ρ : Representation (ZMod 2) K W)
    (q : (H ⧸ pCore 2 H) ≃* K)
    (hq : ∀ a v, d.representation a v = ρ (q a) v)
    (hm : ChapterG.Section11.CaseNine ρ) :
    RankCore.ActionAlternative.{0} d := by
  rcases hm.2 with h | h | h | h
  · obtain ⟨e,f,hf⟩ := h
    exact tensor_of_model d Orthogonal.representation ⊤ le_top (Or.inl rfl)
      (Subgroup.topEquiv.symm) (Or.inr ⟨LinearEquiv.refl _ _,fun _ _ => rfl⟩) (q.trans e) f
      (fun a v => (congrArg f (hq a v)).trans (hf (q a) v))
  · obtain ⟨e,f,hf⟩ := h
    exact tensor_of_model d RankTwo.Imprimitive.OrthogonalA5.representation AltFive le_rfl
      (Or.inr rfl) (MulEquiv.refl _) (Or.inr ⟨LinearEquiv.refl _ _,fun _ _ => rfl⟩) (q.trans e) f
      (fun a v => (congrArg f (hq a v)).trans (hf (q a) v))
  · obtain ⟨e,f,hf⟩ := h
    let θ := Natural.groupEquiv.trans Subgroup.topEquiv.symm
    have hn : IsNaturalFour (show AltFive ≤ ⊤ from le_top)
        (Natural.representation.comp θ.symm.toMonoidHom) := by
      refine ⟨Natural.alternatingEquiv.symm,LinearEquiv.refl _ _,?_⟩
      intro a v
      change Natural.representation (Natural.groupEquiv.symm a.val) v = _
      rw [natural_marking,Natural.restriction]
      rfl
    exact tensor_of_model d Natural.representation ⊤ le_top (Or.inl rfl) θ (Or.inl hn) (q.trans e) f
      (fun a v => (congrArg f (hq a v)).trans (hf (q a) v))
  · obtain ⟨e,f,hf⟩ := h
    have hn : IsNaturalFour (show AltFive ≤ AltFive from le_rfl)
        ((Natural.representation.comp Natural.inclusion).comp Natural.alternatingEquiv.symm.toMonoidHom) := by
      exact ⟨Natural.alternatingEquiv.symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
    exact tensor_of_model d (Natural.representation.comp Natural.inclusion) AltFive le_rfl
      (Or.inr rfl) Natural.alternatingEquiv (Or.inl hn) (q.trans e) f
      (fun a v => (congrArg f (hq a v)).trans (hf (q a) v))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueTensor

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Transport all four concrete G.11.2(9) tensor models to the literal source
quotient H/O₂(H), preserving the constituent and tensor markings. -/
theorem source_case_nine_catalogue (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseNine F.terminalRepresentation) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact CatalogueTensor.of_case_nine (sourceAction F hk) F.terminalRepresentation q
    (fun _ _ => rfl) hm

/-- The genuine equal-sign A₆-by-cubic tensor extension contains the literal
A₆ × C₃ subgroup and contradicts the source three-rank bound. -/
theorem source_case_ten_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (X : Subgroup F.TerminalHdot)
    (hm : ChapterG.Section11.CaseTen F.terminalRepresentation X) : False := by
  let := chosen.elementary
  obtain ⟨e,_⟩ := hm.2
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3
    RankTwo.Imprimitive.AlternatingSixTensor.base
    RankTwo.Imprimitive.AlternatingSixTensor.base_injective
  rw [primeRank_prod_eq_add,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide),
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 3 3 Nat.prime_three (by decide)] at hl
  have he := Theory.GroupTheory.primeRank_equiv 3 e
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hk ▸ pCore_isPGroup
  have hu : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
