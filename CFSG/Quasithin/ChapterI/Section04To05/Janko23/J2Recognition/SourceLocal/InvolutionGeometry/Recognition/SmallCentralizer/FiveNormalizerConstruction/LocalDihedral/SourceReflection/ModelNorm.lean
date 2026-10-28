module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction.LocalDihedral.SourceReflection.NormCalculation
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Transport of the central-norm certificate to the extraspecial group

The existing generator-word interpretation turns every automorphism into a
candidate in the finite certificate. An even nonidentity involution on the five
singular points has support four, so the certificate excludes its nonidentity
central norm. The `import all` edges deliberately reuse the internal coordinate
interpretation; no private coordinate occurs in the exported statements.

Source: Aschbacher, *Sporadic Groups* (1994), 46.8 and 46.11, pp.253–255.
-/

namespace MinusExtraspecial.FixedFourCalculation.Reflection
open Outside

/-- A nontrivial central norm cannot occur for the double-transposition action. -/
public theorem norm_ne_central (a : MulAut Model) (ha : a ^ 2 = 1)
    (heven : Equiv.Perm.sign (fivePointAction a) = 1)
    (hne : fivePointAction a ≠ 1) (d : Model) :
    d * a d ≠ quaternion z := by
  let ap : alternatingGroup (Fin 5) := ⟨fivePointAction a, heven⟩
  have hap : orderOf ap = 2 := orderOf_eq_prime
    (Subtype.ext (by change fivePointAction a ^ 2 = 1; rw [← map_pow, ha, map_one]))
    (fun hh => hne (congrArg Subtype.val hh))
  have hs : (fivePointAction a).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) ap hap]
    rfl
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have hi : Outside.invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ g)) = decode g
    rw [decode_word, decode_word]
    have hh := congrArg (fun b : MulAut Model => b (decode g)) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hm := (moved_eq a).trans hs
  intro hd
  apply calculation_all (encode (a (generators 0))) h1 _ h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 hi hm (encode d)
  apply equiv.injective
  change decode (mul _ _) = decode 2
  rw [decode_mul, decode_word, decode_encode]
  exact hd

/-- Any central norm for this action is the identity. -/
public theorem central_norm_eq_one (a : MulAut Model) (ha : a ^ 2 = 1)
    (heven : Equiv.Perm.sign (fivePointAction a) = 1)
    (hne : fivePointAction a ≠ 1) (d : Model)
    (hd : d * a d ∈ Subgroup.center Model) : d * a d = 1 :=
  ((MinusExtraspecial.mem_center_iff _).mp hd).resolve_right
    (norm_ne_central a ha heven hne d)
end MinusExtraspecial.FixedFourCalculation.Reflection
