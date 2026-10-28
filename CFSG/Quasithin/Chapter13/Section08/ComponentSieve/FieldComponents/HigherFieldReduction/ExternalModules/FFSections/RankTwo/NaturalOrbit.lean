module
public import Theory.Representation.BinaryOffender.Homogeneous.FixedSpaceOrbit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native

/-!
# Borel fixed vectors on the full natural constituent orbit

Every ambient conjugate of an odd-degree PSL₃ natural constituent is natural
or dual under the original projective marking. The proved automorphism
classification supplies actual binary intertwiners. Each conjugate has zero
fixed space for the marked Borel residual, and irreducible-sum induction
proves the same for its full ambient orbit W.

If W is properly contained in the component moved space, native cubic FF
recognition supplies a natural tensor quotient above W. Otherwise W already
is the moved space. In either case the moved space has no Borel-fixed vectors.
Odd-index averaging then gives equality of Borel and component fixed spaces,
retaining the component-central complement. Pair invariance is unnecessary.
OriginalSource.LinearThreeComplete applies this to the literal source action.

Source: Aschbacher–Smith, 13.8.20(a), printed pp.954–955, with B.4.2 and
F.9.18(6); projective automorphism coverage uses GLS3, Theorem 2.5.12(a).
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2^n)

omit [CharP F 2] in
include hn in
/-- Both natural orientations remain natural or dual after any projective
automorphism, using actual binary linear maps. -/
theorem twist_naturalOrDual
    {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) PSL(3,F) N)
    (hnat : IsProjectiveNaturalOrDual ho hF σ) (α : MulAut PSL(3,F)) :
    IsProjectiveNaturalOrDual ho hF (σ.comp α.toMonoidHom) := by
  let ν := projectiveBinaryNatural ho hF
  obtain ⟨β,f,hf⟩ : ∃ (β : MulAut PSL(3,F)) (f : N ≃ₗ[ZMod 2] (Fin 3 → F)),
      ∀ g v, f (σ g v) = ν (β g) (f v) := by
    rcases hnat with ⟨f,hf⟩ | ⟨f,hf⟩
    · exact ⟨1,f,hf⟩
    · let d := projectiveGraphNaturalBinaryDual ho hF
      refine ⟨Matrix.PSL3.OuterSolvable.graph F, f.trans d.symm.toLinearEquiv, ?_⟩
      intro g v
      change d.symm (f (σ g v)) = _
      rw [hf]
      exact LinearMap.congr_fun (d.symm.isIntertwining' g) (f v)
  rcases MarkingRigidity.automorphism_naturalOrDual ho hF hn (α.trans β) with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact Or.inl ⟨f.trans a, fun g v => by
      change a (f (σ (α g) v)) = _
      rw [hf]
      exact ha g (f v)⟩
  · exact Or.inr ⟨f.trans a, fun g v => by
      change a (f (σ (α g) v)) = _
      rw [hf]
      exact ha g (f v)⟩

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
  (e : K ≃* PSL(3,F))
  (B : Subgroup K)
  (hB : B.map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
  (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
  (hnat : IsProjectiveNaturalOrDual ho hF
    ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom))

omit [Finite D] in
include hn hB hI hnat in
/-- Every ambient conjugate of the natural constituent has no fixed vector
for the original marked Borel residual. -/
theorem conjugate_inf_fixedSpace_eq_bot (g : D) :
    I.map (ρ g) ⊓ fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  let σ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let a : MulAut K := MulAut.conjNormal g⁻¹
  let α : MulAut PSL(3,F) := (e.symm.trans a).trans e
  have hnat' := twist_naturalOrDual hn ho hF (σ.comp e.symm.toMonoidHom) hnat α
  have hzero : fixedSpace (σ.comp a.toMonoidHom) B = ⊥ := by
    have hz := projectiveNaturalOrDual_fixedSpace hn ho hF _ hnat'
    rw [← hB, ← fixedSpace_comp_map] at hz
    have he : (((σ.comp e.symm.toMonoidHom).comp α.toMonoidHom).comp e.toMonoidHom) =
        σ.comp a.toMonoidHom := by
      ext k v
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply,α]
    rwa [he] at hz
  apply (Submodule.eq_bot_iff _).mpr
  rintro v ⟨⟨w,hw,rfl⟩,hv⟩
  have hwfix : (⟨w,hw⟩ : I) ∈ fixedSpace (σ.comp a.toMonoidHom) B := by
    intro b
    apply Subtype.ext
    change ρ (g⁻¹ * (b.val : D) * (g⁻¹)⁻¹) w = w
    rw [inv_inv]
    have h := congrArg (ρ g⁻¹) (hv b)
    change ρ g⁻¹ (ρ (b.val : D) (ρ g w)) = ρ g⁻¹ (ρ g w) at h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, mul_assoc] using h
  have hh : (⟨w,hw⟩ : I) = 0 := by
    simpa only [hzero,Submodule.mem_bot] using hwfix
  have hwzero : w = 0 := congrArg Subtype.val hh
  rw [hwzero,map_zero]

include hn hB hI hnat in
/-- The entire ambient orbit of a natural constituent has zero fixed space
for the original Borel residual. Pair invariance is unnecessary. -/
theorem orbit_inf_fixedSpace_eq_bot :
    Representation.BinaryOffender.Homogeneous.orbitSpan ρ ⊤ I ⊓
      fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  rw [fixedSpace_comp_map]
  apply Representation.BinaryOffender.Homogeneous.orbitSpan_inf_fixedSpace_eq_bot
    ρ K (B.map K.subtype) (map_subtype_le _) I hI
  intro g
  rw [← fixedSpace_comp_map]
  exact conjugate_inf_fixedSpace_eq_bot hn ho hF ρ K e B hB I hI hnat g
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit
open Representation.BinaryOffender.Homogeneous
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (B : Subgroup K)
    (hB : B.map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hnat : IsProjectiveNaturalOrDual ho hF
      ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom))

include hS hx hc hs hmark hg hn hB hI hnat in
/-- A natural constituent and the source ratio-two bound imply equality of
Borel and component fixed spaces, through the full ambient orbit and the
literal moved quotient. No two-conjugate orbit premise is needed. -/
theorem fixedSpace_eq_invariants
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    fixedSpace (ρ.comp K.subtype) B = Representation.invariants (ρ.comp K.subtype) := by
  let W : Subrepresentation ρ :=
    ⟨orbitSpan ρ ⊤ I, fun g v hv => (orbitSpan_invariant ρ ⊤ I (mem_top g) v).2 hv⟩
  have hW : W.toSubmodule = orbitSpan ρ ⊤ I := rfl
  have hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule := by
    rw [hW]
    exact orbitSpan_full_commutator ρ (by rw [normalizer_eq_top]) hI
  have hz : W.toSubmodule ⊓ fixedSpace (ρ.comp K.subtype) B = ⊥ :=
    orbit_inf_fixedSpace_eq_bot hn ho hF ρ K e B hB I hI hnat
  have hmoved : subspaceCommutator ρ ⊤ K ⊓ fixedSpace (ρ.comp K.subtype) B = ⊥ := by
    by_cases he : W.toSubmodule = subspaceCommutator ρ ⊤ K
    · rwa [← he]
    obtain ⟨M,hWM,hM,hnat₂⟩ := Native.second_layer ρ K X hS hx hc s hs hmark hg
      hn ho hF e W (by rw [hW]; exact orbitSpan_ne_bot ρ hI) hfull he A hA hbound
    have hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤ := by
      rw [hmark]; exact hg
    have hle := (projectiveTensorLayer ρ K.subtype s hs e W M hWM hgen).fixed_le
      B _ hB (projectiveNaturalOrDual_fixedSpace hn ho hF _ hnat₂)
    rw [← hM]
    apply le_bot_iff.mp
    rw [← hz]
    exact le_inf hle inf_le_right
  apply odd_index_fixedSpace_extension (ρ.comp K.subtype) B (subspaceCommutator ρ ⊤ K)
    (NaturalLayers.odd_index_of_model e B _ hB (psl3_twoResidual_odd_index hn hF))
  · intro k v
    exact Submodule.subset_span ⟨k,k.property,v,Submodule.mem_top,rfl⟩
  · rw [hmoved]
    exact bot_le
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit
