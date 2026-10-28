module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.TernaryCover.Eigenvectors
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.TernaryCover.ThreeFamily
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.TernaryCover.Complete

/-!
# Ternary local-family obstruction and complete corrected cover

The elementary eight currently defined in `Atlas.G2.TernaryLocals` is
constructed from the split torus and the longest Weyl element. Its normalizer
has order at most 512, and consequently cannot be the elementary-eight local
of order 1344 in the source recognition configuration.

An element of the normalizer permutes common eigenvectors of the eight and
preserves their octonion norms. Each of three algebra generators therefore
has at most eight possible images. Those images determine the automorphism:
the eight coordinate basis vectors are explicit words in the generators.
Encoding the three images injects the normalizer into a set of size 8³.

Source comparison: Aschbacher–Smith, *The Classification of Quasithin Groups*,
§I.4(G2), printed p.417, requires an elementary-eight generalized Fitting
subgroup with quotient L₃(2), hence a local of order 1344. The main converse
appears on printed pp.3–4 and 481–482. The concrete model obstruction below
explains why the complete cover uses an enlarged family. The shared
representatives and parent assembly are preserved.

The imported `ThreeFamily` module uses the enlarged family containing both
old representatives and the all-norm-one Cayley-eight normalizer. It reduces
complete coverage to involution conjugacy, a normalizer-invariant eight
extension for each four-group, and the two-orbit classification of eights.
Its character-space dimension input is proved from the actual octonion action.
The imported `Complete` module discharges all three geometric branches and
exports `maximalTwoLocal_threeFamily_cover`, covering arbitrary maximal
two-locals without additional geometric hypotheses.

The coordinate conventions come from the licensed ATLAS split-octonion port;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover

open Atlas.G2 Atlas.G2.TernaryLocals Atlas.SplitOctonion
private abbrev G := Model (ZMod 3)

private def IsCommonEigenvector (v : Space) : Prop :=
  ∀ x : G, x ∈ elementary → IsSignEigenvector x.val v

private theorem firstSign_apply (v : Space) :
    (torus (-1) (1 : (ZMod 3)ˣ)).val v = firstSign v := by
  have hw : ∀ i : Fin 8, (torusWeights (-1) (1 : (ZMod 3)ˣ) i : ZMod 3) =
      ![-1,1,-1,1,1,-1,1,-1] i := by decide +kernel
  funext i
  change (torusWeights (-1) (1 : (ZMod 3)ˣ) i : ZMod 3) * v i = firstSign v i
  rw [hw]
  fin_cases i <;> simp [firstSign]

private theorem secondSign_apply (v : Space) :
    (torus 1 (-1 : (ZMod 3)ˣ)).val v = secondSign v := by
  have hw : ∀ i : Fin 8, (torusWeights 1 (-1 : (ZMod 3)ˣ) i : ZMod 3) =
      ![1,-1,-1,1,1,-1,-1,1] i := by decide +kernel
  funext i
  change (torusWeights 1 (-1 : (ZMod 3)ˣ) i : ZMod 3) * v i = secondSign v i
  rw [hw]
  fin_cases i <;> simp [secondSign]

private theorem longest_apply (v : Space) : longest.val v = reverseCoordinates v := by
  change weylRApply (weylSApply (weylRApply (weylSApply (weylRApply (weylSApply v))))) = _
  simp [weylRApply, weylSApply, reverseCoordinates]

private theorem first_mem : (torus (-1) (1 : (ZMod 3)ˣ)) ∈ elementary := by
  refine ⟨Multiplicative.ofAdd ![1,0,0], ?_⟩
  change torus (-1) 1 * longest ^ 0 = _
  simp only [pow_zero, mul_one]

private theorem second_mem : (torus 1 (-1 : (ZMod 3)ˣ)) ∈ elementary := by
  refine ⟨Multiplicative.ofAdd ![0,1,0], ?_⟩
  change torus 1 (-1) * longest ^ 0 = _
  simp only [pow_zero, mul_one]

private theorem longest_mem : longest ∈ elementary := by
  refine ⟨Multiplicative.ofAdd ![0,0,1], ?_⟩
  change torus 1 1 * longest ^ 1 = longest
  rw [pow_one, show torus (1 : (ZMod 3)ˣ) 1 = 1 from torusHom.map_one, one_mul]

private theorem common_mem_choices {v : Space} (hv : IsCommonEigenvector v)
    (hn : norm v ≠ 0) : v ∈ eigenvectorChoices (norm v) := by
  apply mem_eigenvectorChoices _ ?_ ?_ ?_ hn
  · simpa only [IsSignEigenvector, firstSign_apply] using hv _ first_mem
  · simpa only [IsSignEigenvector, secondSign_apply] using hv _ second_mem
  · simpa only [IsSignEigenvector, longest_apply] using hv _ longest_mem

private theorem normalizer_common (g : localSubgroup true) {v : Space}
    (hv : IsCommonEigenvector v) : IsCommonEigenvector (g.val.val v) := by
  intro x hx
  have hc : g.val⁻¹ * x * g.val ∈ elementary :=
    (Subgroup.mem_normalizer_iff''.mp g.property x).mp hx
  have he := hv _ hc
  have hact : x.val (g.val.val v) = g.val.val ((g.val⁻¹ * x * g.val).val v) := by
    change x.val (g.val.val v) = g.val.val (g.val.val.symm (x.val (g.val.val v)))
    simp
  rcases he with he | he
  · left
    rw [hact, he]
  · right
    rw [hact, he, map_neg]

private def generator : Fin 3 → Space :=
  ![basisVector 0 + basisVector 7,
    basisVector 1 + basisVector 6,
    basisVector 3 - basisVector 4]

set_option maxRecDepth 100000 in
private theorem generator_common (i : Fin 3) : IsCommonEigenvector (generator i) := by
  rintro _ ⟨a, rfl⟩
  exact (by decide +kernel : ∀ (i : Fin 3) (a : Parameters),
    IsSignEigenvector (embedding a).val (generator i)) i a

private theorem generator_norm_ne_zero (i : Fin 3) : norm (generator i) ≠ 0 := by
  exact (by decide +kernel : ∀ i : Fin 3, norm (generator i) ≠ 0) i

private def word (a b c : Space) : Fin 8 → Space :=
  ![-(a - mul a c), -(b + mul b c), mul a b + mul (mul a b) c,
    -(unit + c), -(unit - c), mul a b - mul (mul a b) c,
    -(b - mul b c), -(a + mul a c)]

private theorem basis_word (i : Fin 8) :
    basisVector i = word (generator 0) (generator 1) (generator 2) i := by
  exact (by decide +kernel : ∀ i : Fin 8,
    basisVector i = word (generator 0) (generator 1) (generator 2) i) i

private theorem map_word (g : G) (a b c : Space) (i : Fin 8) :
    g.val (word a b c i) = word (g.val a) (g.val b) (g.val c) i := by
  fin_cases i <;> simp [word]

private theorem ext_generators {g h : G}
    (he : ∀ i : Fin 3, g.val (generator i) = h.val (generator i)) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext
  intro i
  simp only [LinearEquiv.coe_coe, basis_word, map_word, he]

private def imageChoices (g : localSubgroup true) (i : Fin 3) :
    ↥(eigenvectorChoices (norm (generator i))) :=
  ⟨g.val.val (generator i), by
    have h := common_mem_choices (normalizer_common g (generator_common i))
      (by simpa only [automorphism_norm] using generator_norm_ne_zero i)
    simpa only [automorphism_norm] using h⟩

private noncomputable def imageCode (g : localSubgroup true) (i : Fin 3) :
    Fin 4 × Bool :=
  (Finset.mem_image.mp (imageChoices g i).property).choose

private theorem imageCode_spec (g : localSubgroup true) (i : Fin 3) :
    (if (imageCode g i).2 then (-1 : ZMod 3) else 1) •
      (basisVector (imageCode g i).1.castSucc.castSucc.castSucc.castSucc +
        norm (generator i) • basisVector
          (7 - (imageCode g i).1.castSucc.castSucc.castSucc.castSucc)) =
      g.val.val (generator i) :=
  (Finset.mem_image.mp (imageChoices g i).property).choose_spec.2

private theorem imageCode_injective : Function.Injective imageCode := by
  intro g h he
  apply Subtype.ext
  apply ext_generators
  intro i
  rw [← imageCode_spec g i, ← imageCode_spec h i, congrFun he i]

/-- The specified torus/Weyl eight has a normalizer of order at most 512. -/
public theorem localSubgroup_true_card_le_512 : Nat.card (localSubgroup true) ≤ 512 := by
  have hc := Nat.card_le_card_of_injective imageCode imageCode_injective
  simpa using hc

/-- In particular, this is not the elementary-eight local of order 1344
required by the source recognition configuration. -/
public theorem localSubgroup_true_card_ne_1344 :
    Nat.card (localSubgroup true) ≠ 1344 := by
  have h := localSubgroup_true_card_le_512
  omega

end CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover
