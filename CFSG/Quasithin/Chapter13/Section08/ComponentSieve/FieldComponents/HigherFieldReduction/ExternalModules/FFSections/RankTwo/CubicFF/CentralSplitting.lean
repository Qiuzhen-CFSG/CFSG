module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Natural
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FieldGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion.Cohomology
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.Representation.BinaryOffender.CentralSectionSplitting

/-!
# Splitting recognized odd-degree natural constituents

The literal projection from an Irr⁺ subspace I to I/C_I(K) is a perfect central
cover: its kernel is fixed, it is onto, and the defining commutator-generation
clause of Irr⁺ makes its source perfect as a module. The universal-cover theorem
therefore makes this projection injective when the quotient's dual H¹ vanishes.

For an odd-degree field of order 2ⁿ with n > 1, transport the checked natural
SL₃ first-cohomology calculation through scalar restriction and the actual
SL₃-to-PSL₃ equivalence. The graph automorphism, dot product and trace give the
binary dual calculation. Evaluation handles the double dual. Consequently both
recognized quotient orientations split, retaining the supplied marking of K and
the same orientation on I. No splitting map or cohomology hypothesis is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Remark I.1.5
and Lemma I.1.6(4), printed p.408, applied in 13.8.20(a), printed pp.954–955.
-/

@[expose] public noncomputable section

open Representation Representation.OneCohomology Representation.HigherFieldBorelFixedSpaces
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.CentralSplitting
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)

include hn in
/-- The natural binary cohomology vanishes under the actual projective marking. -/
lemma projectiveNatural_h1 : Module.finrank (ZMod 2) (H1 (projectiveBinaryNatural ho hF)) = 0 := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  have hb : Module.finrank (ZMod 2) (H1 (binaryNatural (F := F) 3)) = 0 := by
    rw [finrank_restrictScalars, SLHigherNatural.finrank_H1_sl3_large_field hlarge, mul_zero]
  let e := H1Congr (binaryNatural (F := F) 3) (projectiveBinaryNatural ho hF)
    (sl3ProjectiveEquiv ho hF) (LinearEquiv.refl (ZMod 2) (Fin 3 → F)) (by
      intro g v
      exact (projectiveBinaryNatural_projection ho hF g v).symm)
  exact e.finrank_eq.symm.trans hb

include hn in
/-- The graph-and-trace comparison gives vanishing for the binary dual natural module. -/
lemma projectiveDualNatural_h1 :
    Module.finrank (ZMod 2) (H1 (projectiveBinaryNatural ho hF).dual) = 0 := by
  let d := projectiveGraphNaturalBinaryDual ho hF
  let a := Matrix.PSL3.OuterSolvable.graph F
  let e := H1Congr (projectiveBinaryNatural ho hF) (projectiveBinaryNatural ho hF).dual
    a.symm d.toLinearEquiv (by
      intro g v
      have h := LinearMap.congr_fun (d.isIntertwining' (a.symm g)) v
      change d.toLinearEquiv (projectiveBinaryNatural ho hF (a (a.symm g)) v) = _ at h
      rwa [a.apply_symm_apply] at h)
  exact e.finrank_eq.symm.trans (projectiveNatural_h1 hn ho hF)

include hn in
private lemma doubleDualNatural_h1 :
    Module.finrank (ZMod 2) (H1 (projectiveBinaryNatural ho hF).dual.dual) = 0 := by
  let e := H1Congr (projectiveBinaryNatural ho hF).dual.dual (projectiveBinaryNatural ho hF)
    (MulEquiv.refl _) (Module.evalEquiv (ZMod 2) (Fin 3 → F)).symm
    (evaluationIntertwining (projectiveBinaryNatural ho hF)).isIntertwining
  exact e.finrank_eq.trans (projectiveNatural_h1 hn ho hF)

include hn in
/-- Both recognized orientations have vanishing first cohomology with dual coefficients. -/
lemma recognized_dual_h1 {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) PSL(3,F) N)
    (hσ : IsProjectiveNaturalOrDual ho hF σ) :
    Module.finrank (ZMod 2) (H1 σ.dual) = 0 := by
  rcases hσ with ⟨f, hf⟩ | ⟨f, hf⟩
  · let e := H1Congr σ.dual (projectiveBinaryNatural ho hF).dual
      (MulEquiv.refl _) f.symm.dualMap (dual_equivariant f hf)
    exact e.finrank_eq.trans (projectiveDualNatural_h1 hn ho hF)
  · let e := H1Congr σ.dual (projectiveBinaryNatural ho hF).dual.dual
      (MulEquiv.refl _) f.symm.dualMap (dual_equivariant f hf)
    exact e.finrank_eq.trans (doubleDualNatural_h1 hn ho hF)

include hn in
/-- Transport the dual-coefficient calculation back to the original acting group. -/
lemma marked_dual_h1 {G N : Type*} [Group G] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) G N) (e : G ≃* PSL(3,F))
    (hσ : IsProjectiveNaturalOrDual ho hF (σ.comp e.symm.toMonoidHom)) :
    Module.finrank (ZMod 2) (H1 σ.dual) = 0 := by
  let a := H1Congr σ.dual (Representation.dual (σ.comp e.symm.toMonoidHom)) e
    (LinearEquiv.refl (ZMod 2) _) (by
      intro g f
      ext v
      change f (σ g⁻¹ v) = f (σ (e.symm ((e g)⁻¹)) v)
      rw [← e.map_inv, e.symm_apply_apply])
  exact a.finrank_eq.trans (recognized_dual_h1 hn ho hF _ hσ)

open Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D)

private lemma constituent_commutator (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I) :
    Coinvariants.ker (invariantSubspace ρ K I hI.choose).toRepresentation = ⊤ := by
  let σ : Representation (ZMod 2) K I := (invariantSubspace ρ K I hI.choose).toRepresentation
  have hi : I ≤ (Coinvariants.ker σ).map I.subtype := by
    conv_lhs => rw [← hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact ⟨σ ⟨k, hk⟩ ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨w, hw, hew⟩ := hi v.property
  have he : w = v := Subtype.ext hew
  rwa [← he]

/-- The actual quotient map from I to I/C_I(K), with its original K-action. -/
def constituentProjection (I : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ I) :
    (invariantSubspace ρ K I hs).toRepresentation.IntertwiningMap
      (centralQuotientRepresentation ρ K I hs) :=
  ((fixedSpace ρ K).comap I.subtype).mkQ.intertwiningMap_of_isIntertwiningMap _ _
    (fun _ _ => rfl)

/-- The defining commutator-generation clause makes the central quotient map a cover. -/
lemma constituentProjection_isCover (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I) :
    IsCover (constituentProjection ρ K I hI.choose) := by
  refine ⟨Submodule.mkQ_surjective _, ?_, constituent_commutator ρ K I hI⟩
  intro v hv k
  apply Subtype.ext
  exact ((Submodule.Quotient.mk_eq_zero _).mp hv) k

variable [Finite D] [Finite V]

include hn in
/-- A recognized natural or dual-natural central quotient has zero central kernel. -/
lemma disjoint_fixedSpace (e : K ≃* PSL(3,F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hσ : IsProjectiveNaturalOrDual ho hF
      ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom)) :
    Disjoint I (fixedSpace ρ K) := by
  have hp := cover_injective (constituentProjection ρ K I hI.choose)
    (constituentProjection_isCover ρ K I hI)
    (marked_dual_h1 hn ho hF _ e hσ)
  rw [Submodule.disjoint_def]
  intro v hv hc
  have hz : constituentProjection ρ K I hI.choose ⟨v, hv⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  have hh := hp (hz.trans (map_zero _).symm)
  exact congrArg Subtype.val hh

include hn in
/-- The natural-or-dual recognition lifts to the actual I-action with the same marking. -/
lemma naturalOrDual (e : K ≃* PSL(3,F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hσ : IsProjectiveNaturalOrDual ho hF
      ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom)) :
    IsProjectiveNaturalOrDual ho hF
      ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom) := by
  let a := centralSectionEquiv ρ K I (disjoint_fixedSpace hn ho hF ρ K e I hI hσ)
  rcases hσ with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨a.trans f, fun g v => hf g (a v)⟩
  · exact Or.inr ⟨a.trans f, fun g v => hf g (a v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.CentralSplitting
