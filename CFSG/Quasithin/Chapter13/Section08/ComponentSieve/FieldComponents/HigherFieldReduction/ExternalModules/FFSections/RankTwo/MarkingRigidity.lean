module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FieldGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Natural
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Natural modules under an arbitrary projective marking

A natural SL₃ action over an equal-cardinality binary field is natural or
binary dual-natural under any prescribed PSL₃ marking. Entrywise field
coordinates and the odd-degree SL₃-to-PSL₃ isomorphism first compare the two
group markings. Linear conjugation, field automorphisms and inverse transpose
preserve the pair of natural representation classes. Intertwiners transport
through composition and inverse, giving a subgroup of the automorphism group;
root orientation and standard coverage prove that this subgroup is the whole
automorphism group.

All module comparisons are actual binary linear equivalences. The final
theorem uses the supplied marking exactly, so two layers can have independent
natural/dual orientations while retaining the same Borel marking. Its natural
action and field-cardinality inputs are explicit; no FF classification or
extension theorem is asserted here.

Source: Aschbacher–Smith, B.4.2(2), printed p.86, and the two natural layers in
the proof of 13.8.20, printed pp.954–955. Automorphism coverage uses the concrete
matrix actions and root geometry developed for GLS3, Theorem 2.5.12(a).
-/

@[expose] public noncomputable section

open Representation Representation.HigherFieldBorelFixedSpaces
open Matrix Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.MarkingRigidity

section Transport
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}

private def precomp (e : Representation.Equiv ρ σ) (f : D →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := e.isIntertwining' (f g)

private def untwist (α : MulAut G) (e : Representation.Equiv (ρ.comp α.toMonoidHom) σ) :
    Representation.Equiv (σ.comp α.symm.toMonoidHom) ρ where
  toLinearEquiv := e.symm.toLinearEquiv
  isIntertwining' g := by
    have h := e.symm.isIntertwining' (α.symm g)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using h

private def dualTwist (α : G →* G) (e : Representation.Equiv (ρ.comp α) σ) :
    Representation.Equiv (ρ.dual.comp α) σ.dual where
  toLinearEquiv := e.toLinearEquiv.symm.dualMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change f (ρ (α g)⁻¹ (e.symm w)) = f (e.symm (σ g⁻¹ w))
    have h : e.symm (σ g⁻¹ w) = ρ (α g⁻¹) (e.symm w) :=
      LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w
    rw [α.map_inv] at h
    exact congrArg f h.symm

private def pairStabilizer (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) : Subgroup (MulAut G) where
  carrier := {α |
    (Nonempty (Representation.Equiv (ρ.comp α.toMonoidHom) ρ) ∧
      Nonempty (Representation.Equiv (σ.comp α.toMonoidHom) σ)) ∨
    (Nonempty (Representation.Equiv (ρ.comp α.toMonoidHom) σ) ∧
      Nonempty (Representation.Equiv (σ.comp α.toMonoidHom) ρ))}
  one_mem' := Or.inl ⟨⟨.refl ρ⟩, ⟨.refl σ⟩⟩
  mul_mem' := by
    rintro α β (⟨⟨a⟩, ⟨b⟩⟩ | ⟨⟨a⟩, ⟨b⟩⟩) (⟨⟨c⟩, ⟨d⟩⟩ | ⟨⟨c⟩, ⟨d⟩⟩)
    · exact Or.inl ⟨⟨(precomp a β.toMonoidHom).trans c⟩,
        ⟨(precomp b β.toMonoidHom).trans d⟩⟩
    · exact Or.inr ⟨⟨(precomp a β.toMonoidHom).trans c⟩,
        ⟨(precomp b β.toMonoidHom).trans d⟩⟩
    · exact Or.inr ⟨⟨(precomp a β.toMonoidHom).trans d⟩,
        ⟨(precomp b β.toMonoidHom).trans c⟩⟩
    · exact Or.inl ⟨⟨(precomp a β.toMonoidHom).trans d⟩,
        ⟨(precomp b β.toMonoidHom).trans c⟩⟩
  inv_mem' := by
    rintro α (⟨⟨a⟩, ⟨b⟩⟩ | ⟨⟨a⟩, ⟨b⟩⟩)
    · exact Or.inl ⟨⟨untwist α a⟩, ⟨untwist α b⟩⟩
    · exact Or.inr ⟨⟨untwist α b⟩, ⟨untwist α a⟩⟩
end Transport

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n)

/-- Conjugation by a general linear matrix is implemented by that matrix. -/
def linearConjEquiv (a : GL (Fin 3) F) : Representation.Equiv
    (projectiveBinaryNatural hn hF)
    ((projectiveBinaryNatural hn hF).comp (linearConj F a).toMonoidHom) where
  toLinearEquiv := (GeneralLinearGroup.toLin a).toLinearEquiv.restrictScalars (ZMod 2)
  isIntertwining' g := by
    obtain ⟨g, rfl⟩ := Matrix.PSL3.projection_surjective F g
    apply LinearMap.ext
    intro v
    change (GeneralLinearGroup.toLin a).toLinearEquiv
      (projectiveBinaryNatural hn hF (Matrix.PSL3.projection F g) v) =
      projectiveBinaryNatural hn hF
        (Matrix.PSL3.projection F (linearConjSL F a g)) _
    rw [projectiveBinaryNatural_projection, projectiveBinaryNatural_projection]
    change a.val *ᵥ (g.val *ᵥ v) = (linearConjSL F a g).val *ᵥ (a.val *ᵥ v)
    have ha := congrArg Units.val (linearConjSL_toGL F a g)
    change (linearConjSL F a g).val = a.val * g.val * a⁻¹.val at ha
    rw [ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      mul_assoc, a.inv_mul, mul_one]

/-- Entrywise field automorphisms give binary linear natural comparisons. -/
def fieldEquiv (a : F ≃+* F) : Representation.Equiv
    (projectiveBinaryNatural hn hF)
    ((projectiveBinaryNatural hn hF).comp (fieldAction F a).toMonoidHom) where
  toLinearEquiv := fieldCoordinates 3 a
  isIntertwining' g := by
    obtain ⟨g, rfl⟩ := Matrix.PSL3.projection_surjective F g
    apply LinearMap.ext
    intro v
    change fieldCoordinates 3 a
      (projectiveBinaryNatural hn hF (Matrix.PSL3.projection F g) v) =
      projectiveBinaryNatural hn hF
        (fieldAction F a (Matrix.PSL3.projection F g)) _
    have ha : fieldAction F a (Matrix.PSL3.projection F g) =
        Matrix.PSL3.projection F (Atlas.fieldEquivSL 3 a g) :=
      Atlas.fieldEquivPSL_mk 3 a g
    rw [ha, projectiveBinaryNatural_projection, projectiveBinaryNatural_projection]
    exact fieldCoordinates_intertwines 3 a g v

/-- Every projective automorphism preserves the natural/dual pair of binary
representations. Coverage is proved from opposite-root orientation. -/
theorem automorphism_naturalOrDual (hlarge : 1 < n) (α : MulAut PSL(3,F)) :
    IsProjectiveNaturalOrDual hn hF
      ((projectiveBinaryNatural hn hF).comp α.toMonoidHom) := by
  let ρ := projectiveBinaryNatural hn hF
  have hs : standard F ≤ pairStabilizer ρ ρ.dual := by
    apply sup_le
    · apply sup_le
      · rintro _ ⟨a, rfl⟩
        exact Or.inl ⟨⟨(linearConjEquiv hn hF a).symm⟩,
          ⟨dualTwist _ (linearConjEquiv hn hF a).symm⟩⟩
      · rintro _ ⟨a, rfl⟩
        exact Or.inl ⟨⟨(fieldEquiv hn hF a).symm⟩,
          ⟨dualTwist _ (fieldEquiv hn hF a).symm⟩⟩
    · apply Subgroup.zpowers_le.mpr
      have hg := projectiveGraphNaturalBinaryDual hn hF
      have hgi : (graph F).symm = graph F :=
        inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using graph_sq F)
      have hg' := untwist (graph F) hg
      rw [hgi] at hg'
      exact Or.inr ⟨⟨hg⟩, ⟨hg'⟩⟩
  have hcoverage := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F
    (show 0 < n by omega) hF
    (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots F hlarge hF)
  have hα := hs (show α ∈ standard F by rw [hcoverage]; trivial)
  rcases hα with ⟨⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩
  · exact Or.inl ⟨e.toLinearEquiv, fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩
  · exact Or.inr ⟨e.toLinearEquiv, fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Natural coordinates over an equal-cardinality binary field can be aligned
with any supplied projective marking. The result keeps that exact marking,
with a genuine binary linear intertwiner in either natural orientation. -/
theorem actionEquiv_naturalOrDual (hlarge : 1 < n)
    {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) L V) (B : BinaryField)
    (hB : Nat.card B.Carrier = Nat.card F)
    (a : ActionEquiv σ (linearNatural B 3)) (e : L ≃* PSL(3,F)) :
    IsProjectiveNaturalOrDual hn hF (σ.comp e.symm.toMonoidHom) := by
  let := Fintype.ofFinite B.Carrier
  let := Fintype.ofFinite F
  let c : B.Carrier ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hB)
  let m : L ≃* PSL(3,F) :=
    (a.groupEquiv.trans (Atlas.fieldEquivSL 3 c)).trans (sl3ProjectiveEquiv hn hF)
  let α : MulAut PSL(3,F) := e.symm.trans m
  let f : V ≃ₗ[ZMod 2] (Fin 3 → F) := a.linearEquiv.trans (fieldCoordinates 3 c)
  have hf (g : PSL(3,F)) (v : V) :
      f ((σ.comp e.symm.toMonoidHom) g v) = projectiveBinaryNatural hn hF (α g) (f v) := by
    change fieldCoordinates 3 c (a.linearEquiv (σ (e.symm g) v)) = _
    rw [a.intertwines]
    change fieldCoordinates 3 c (binaryNatural 3 (a.groupEquiv (e.symm g)) (a.linearEquiv v)) =
      projectiveBinaryNatural hn hF
        (Matrix.PSL3.projection F (Atlas.fieldEquivSL 3 c (a.groupEquiv (e.symm g)))) (f v)
    rw [projectiveBinaryNatural_projection]
    exact fieldCoordinates_intertwines 3 c _ _
  rcases automorphism_naturalOrDual hn hF hlarge α with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨f.trans b, fun g v => by
      change b (f ((σ.comp e.symm.toMonoidHom) g v)) = _
      rw [hf]
      exact hb g (f v)⟩
  · exact Or.inr ⟨f.trans b, fun g v => by
      change b (f ((σ.comp e.symm.toMonoidHom) g v)) = _
      rw [hf]
      exact hb g (f v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.MarkingRigidity
