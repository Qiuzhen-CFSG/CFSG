module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicSections
public import Theory.SpecificGroups.LinearHigher.A02ParabolicSections
public import Theory.SpecificGroups.Symplectic.A02ParabolicSections
public import Theory.SpecificGroups.Symplectic.A02ParabolicSections.RankThree

/-!
# Split parabolic applications in A.2.18

The binary higher-linear parabolic contains the actual PSL₆(2) first block.
The smaller-section induction hypothesis makes that semisimple section
strongly quasithin, contradicting the established binary degree-six Levi
obstruction.  All transport uses the supplied isomorphism from G/Z(G).
The finite field in a binary model predicate is transported by its actual
field isomorphism with ZMod 2.

The other two applications below retain their geometric construction inputs.
Their endpoint rank obstructions and semisimplicity inputs are discharged
over the supplied finite fields.

Source: Aschbacher--Smith A.2.18, printed p.40, using A.2.15(2).
-/

public section

open Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
open Theory.SpecificGroups.LinearHigher
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem quasisimple_semisimple (T : Type*) [Group T] [IsQuasisimple T] :
    IsSemisimple T := by
  apply top_unique
  exact le_sSup (show IsComponent T ⊤ from
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)

/-- The concrete six-dimensional Levi discharges the higher binary linear
branch through the literal center quotient, without an endpoint rank premise. -/
theorem false_of_binary_linear_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {d : ℕ} (hd : 7 ≤ d)
    (e : (G ⧸ Subgroup.center G) ≃* PSL(d, ZMod 2)) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ d by omega)
  have hm : 0 < m := by omega
  let T := ULift.{u} PSL(6, ZMod 2)
  let : IsQuasisimple PSL(6, ZMod 2) := psl_isQuasisimple (by decide)
  let : IsQuasisimple T := IsQuasisimple.of_mulEquiv MulEquiv.ulift.symm
  have hs : IsSectionOf T (blockParabolic 6 m (by decide) hm) := by
    apply IsSectionOf.of_mulEquiv (e := MulEquiv.ulift)
    exact IsSectionOf.refl.ambient_injective (blockFirstToParabolic 6 m (by decide) hm)
      (blockFirstToParabolic_injective 6 m (by decide) hm)
  have ht := stronglyQuasithin_semisimple_section_of_center_quotient ih hG hK e
    (blockParabolic_ne_top 6 m (by decide) hm)
    (blockParabolic_isTwoLocal 6 m (by decide) hm) hs (quasisimple_semisimple T)
  exact BinaryLinear.EvenLieLevi.not_quasithin_projective (by decide : 6 ≤ 6)
    (isQuasithin_of_equiv (MulEquiv.ulift : T ≃* PSL(6, ZMod 2)) ht.quasithin)

/-- The binary model adapter retains and transports the supplied field witness. -/
theorem binary_linear_center_quotient_degree_le_six
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {d : ℕ} (hmodel : ClassicalGroup.IsPSL (G ⧸ Subgroup.center G) d 2) : d ≤ 6 := by
  by_contra hd
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hmodel
  let eF := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo F hc
  exact false_of_binary_linear_center_quotient ih hG hK (by omega)
    (e.trans (Atlas.fieldEquivPSL d eF))

/-- Consumer of a split four-space Levi over the supplied finite field.
Only the parabolic geometry remains as input; simplicity and the endpoint
quasithin obstruction are proved for the literal PSL₄ carrier. -/
theorem false_of_linear_four_split_parabolic
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type} [Field F] [Finite F] {a d : ℕ}
    (ha : 0 < a) (hc : Nat.card F = 2 ^ a) (hq : 2 < Nat.card F)
    (e : (G ⧸ Subgroup.center G) ≃* PSL(d, F))
    {P : Subgroup PSL(d, F)} (hP : P ≠ ⊤) (hl : IsTwoLocal P)
    (f : PSL(4, F) →* P) (hf : Function.Injective f) : False := by
  let T := ULift.{u} PSL(4, F)
  let : IsQuasisimple PSL(4, F) := psl_isQuasisimple (by decide)
  let : IsQuasisimple T := IsQuasisimple.of_mulEquiv MulEquiv.ulift.symm
  have hs : IsSectionOf T P :=
    (IsSectionOf.refl.ambient_injective f hf).of_mulEquiv MulEquiv.ulift
  have ht := stronglyQuasithin_semisimple_section_of_center_quotient ih hG hK e
    hP hl hs (quasisimple_semisimple T)
  have ha1 := linear_exponent_eq_one ht.quasithin (by decide : 4 ≤ 4) ha
    (show ClassicalGroup.IsPSL T 4 (2 ^ a) from
      ⟨F, inferInstance, inferInstance, hc, ⟨MulEquiv.ulift⟩⟩)
  rw [ha1, pow_one] at hc
  omega

/-- Consumer of the actual iterated symplectic tail numerator.  Its section
map is the central quotient of that numerator, and the rank obstruction is
discharged for every positive even-field exponent.  Only the root-normalizer
placement and properness remain inputs. -/
theorem false_of_symplectic_six_split_parabolic
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ}
    (ha : 0 < a) (hc : Nat.card F = 2 ^ a)
    (n : ℕ) (i : Fin (4 + n))
    (e : (G ⧸ Subgroup.center G) ≃* Matrix.PSp4Three.PSp (4 + n) F)
    (hP : Theory.SpecificGroups.Symplectic.symplecticParabolic (F := F) n i ≠ ⊤)
    (hplace : Theory.SpecificGroups.Symplectic.symplecticSixRange (F := F) n ≤
      Theory.SpecificGroups.Symplectic.symplecticParabolic (F := F) n i) : False := by
  let T := ULift.{u} (Matrix.PSp4Three.PSp 3 F)
  let : IsQuasisimple (Matrix.PSp4Three.PSp 3 F) :=
    Theory.SpecificGroups.Symplectic.six_projective_quasisimple ha hc
  let : IsQuasisimple T := IsQuasisimple.of_mulEquiv MulEquiv.ulift.symm
  have hs : IsSectionOf T
      (Theory.SpecificGroups.Symplectic.symplecticParabolic (F := F) n i) := by
    apply IsSectionOf.of_mulEquiv (e := MulEquiv.ulift)
    exact (IsSectionOf.of_surjective
      (Theory.SpecificGroups.Symplectic.symplecticSixRangeProjection (F := F) n)
      (Theory.SpecificGroups.Symplectic.symplecticSixRangeProjection_surjective n)).ambient_injective
        (Subgroup.inclusion hplace) (Subgroup.inclusion_injective hplace)
  exact false_of_symplectic_six_parabolic_section ih hG hK e hP
    (Theory.SpecificGroups.Symplectic.symplecticParabolic_isTwoLocal n i)
    hs (quasisimple_semisimple T) ha
    ⟨F, inferInstance, inferInstance, hc, ⟨MulEquiv.ulift⟩⟩

end CFSG.Quasithin.ChapterA.Section02.EvenLie
