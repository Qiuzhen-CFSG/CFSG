module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.Residuals
public import Theory.GroupTheory.PCoreSurjective

/-!
# The source lift and its two torus factors

The source Borel maps onto the binary product Borel through the literal
H/O₂(H) quotient and the constructed component coordinates. The composed
factor quotient maps have kernel exactly O₂(B₀). Identifying the two cyclic
tori uses an actual multiplicative equivalence of their equal-order carriers.
The residual equality at q = 4 is then applied to this concrete map.

Ambient normalizer elements induce actual automorphisms of this torus
quotient, with the conjugation formula proved on every representative.
These definitions are shared with the remaining marked-conjugation argument.
Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceTorus
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
variable (H K₀ : Subgroup G) (hK : K₀ ≤ H)
  (e : Source.starImage H K₀ ≃* Q × Q)
  (S : Sylow 2 (Source.starImage H K₀))

abbrev chosenStarBorel : Subgroup (Source.Hstar H) :=
  SylowBorel.relativeBorel (Source.starImage H K₀) S

abbrev chosenLift : Subgroup G := borelLift H K₀ hK (chosenStarBorel H K₀ S)

noncomputable abbrev chosenSylow : Sylow 2 (Q × Q) := SylowBorel.productSylow (Source.starImage H K₀) e S

/-- The actual quotient restriction, followed by the marked product coordinates. -/
noncomputable def toBinary : chosenLift H K₀ hK S →* BinaryBorel.borel (chosenSylow H K₀ e S) :=
  (SylowBorel.coordinates (Source.starImage H K₀) e S).toMonoidHom.comp
    (liftToBorel H K₀ hK (chosenStarBorel H K₀ S))

omit [Finite Q] in
theorem toBinary_surjective : Function.Surjective (toBinary H K₀ hK e S) :=
  (SylowBorel.coordinates (Source.starImage H K₀) e S).surjective.comp
    (liftToBorel_surjective H K₀ hK _ (SylowBorel.relativeBorel_le _ S))

omit [Finite Q] in
theorem toBinary_ker_two : IsPGroup 2 (toBinary H K₀ hK e S).ker := by
  rw [toBinary, MonoidHom.ker_comp_of_injective _ _ (SylowBorel.coordinates _ e S).injective]
  exact liftToBorel_ker_two H K₀ hK _

/-- The two literal factor torus quotients of the source lift. -/
noncomputable def toTori : chosenLift H K₀ hK S →*
    BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
      BinaryBorel.Torus (BinaryBorel.secondSylow (chosenSylow H K₀ e S)) :=
  (BinaryBorel.productMap (chosenSylow H K₀ e S)).comp (toBinary H K₀ hK e S)

theorem toTori_surjective : Function.Surjective (toTori H K₀ hK e S) :=
  (BinaryBorel.productMap_surjective _).comp (toBinary_surjective H K₀ hK e S)

/-- The kernel is the intrinsic two-core of the lift, not the ambient two-core. -/
theorem toTori_ker : (toTori H K₀ hK e S).ker = pCore 2 (chosenLift H K₀ hK S) := by
  rw [toTori, ← MonoidHom.comap_ker, BinaryBorel.productMap_ker]
  exact (toBinary H K₀ hK e S).comap_pCore_of_ker_isPGroup
    (toBinary_surjective H K₀ hK e S) (toBinary_ker_two H K₀ hK e S)

/-- Identification of the two cyclic factors keeps both coordinates and chooses
an actual isomorphism for the second factor. -/
noncomputable def commonTorusCoordinates {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
        BinaryBorel.Torus (BinaryBorel.secondSylow (chosenSylow H K₀ e S)) ≃*
      BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
        BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) :=
  MulEquiv.prodCongr (MulEquiv.refl _)
    (BinaryBorel.torusEquiv hn hmodel _ _)

noncomputable def toCommonTori {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) : chosenLift H K₀ hK S →*
      BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
        BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) :=
  (commonTorusCoordinates H K₀ e S hn hmodel).toMonoidHom.comp (toTori H K₀ hK e S)

theorem toCommonTori_surjective {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    Function.Surjective (toCommonTori H K₀ hK e S hn hmodel) :=
  (commonTorusCoordinates H K₀ e S hn hmodel).surjective.comp (toTori_surjective H K₀ hK e S)

theorem toCommonTori_ker {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    (toCommonTori H K₀ hK e S hn hmodel).ker = pCore 2 (chosenLift H K₀ hK S) := by
  rw [toCommonTori, MonoidHom.ker_comp_of_injective _ _
    (commonTorusCoordinates H K₀ e S hn hmodel).injective, toTori_ker]

include e in
/-- At n = 2 the constructed quotient map supplies the terminal residual
identification, using only containment and the earlier theta identity. -/
theorem marked_eq_residual_at_four (M L₁ : Subgroup G)
    (hLB : L₁ ≤ chosenLift H K₀ hK S) (hBM : chosenLift H K₀ hK S ≤ M)
    (hL : IsPPerfect 2 L₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hmodel : ClassicalGroup.IsPSL Q 2 4) :
    L₁ = (pResidual 2 (chosenLift H K₀ hK S)).map (chosenLift H K₀ hK S).subtype :=
  BorelResiduals.marked_eq_residual H M _ L₁
    ((borelLift_le H K₀ hK _).trans hK) hBM hLB hL htheta hmodel
    (chosenSylow H K₀ e S) (toBinary H K₀ hK e S) (toBinary_ker_two H K₀ hK e S)


variable {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))

/-- Quotient coordinates for the actual lifted Borel. -/
noncomputable def quotientCoordinates :
    (chosenLift H K₀ hK S ⧸ pCore 2 (chosenLift H K₀ hK S)) ≃*
      BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
        BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) :=
  (QuotientGroup.quotientMulEquivOfEq (toCommonTori_ker H K₀ hK e S hn hmodel).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toCommonTori_surjective H K₀ hK e S hn hmodel))

theorem quotientCoordinates_mk (x : chosenLift H K₀ hK S) :
    quotientCoordinates H K₀ hK e S hn hmodel (QuotientGroup.mk' _ x) =
      toCommonTori H K₀ hK e S hn hmodel x := rfl

/-- Any actual automorphism of the lift descends through its characteristic
core to both torus coordinates. -/
noncomputable def action (a : MulAut (chosenLift H K₀ hK S)) :
    MulAut (BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
      BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S))) :=
  (quotientCoordinates H K₀ hK e S hn hmodel).symm.trans
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
      (quotientCoordinates H K₀ hK e S hn hmodel))

theorem action_toCommonTori (a : MulAut (chosenLift H K₀ hK S))
    (x : chosenLift H K₀ hK S) :
    action H K₀ hK e S hn hmodel a (toCommonTori H K₀ hK e S hn hmodel x) =
      toCommonTori H K₀ hK e S hn hmodel (a x) := by
  change quotientCoordinates H K₀ hK e S hn hmodel
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
      ((quotientCoordinates H K₀ hK e S hn hmodel).symm
        (toCommonTori H K₀ hK e S hn hmodel x))) = _
  rw [← quotientCoordinates_mk H K₀ hK e S hn hmodel x, MulEquiv.symm_apply_apply]
  rfl

/-- Conjugation by an actual ambient normalizer element, in torus coordinates. -/
noncomputable def normalizerAction
    (g : normalizer (chosenLift H K₀ hK S : Set G)) :
    MulAut (BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S)) ×
      BinaryBorel.Torus (BinaryBorel.firstSylow (chosenSylow H K₀ e S))) :=
  action H K₀ hK e S hn hmodel ((chosenLift H K₀ hK S).normalizerMonoidHom g)

/-- The quotient action is literally induced by ambient conjugation. -/
theorem normalizerAction_toCommonTori
    (g : normalizer (chosenLift H K₀ hK S : Set G)) (x : chosenLift H K₀ hK S) :
    normalizerAction H K₀ hK e S hn hmodel g (toCommonTori H K₀ hK e S hn hmodel x) =
      toCommonTori H K₀ hK e S hn hmodel
        ⟨g.val * x.val * g.val⁻¹, (mem_normalizer_iff.mp g.property x.val).mp x.property⟩ :=
  action_toCommonTori H K₀ hK e S hn hmodel _ x


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceTorus

end
