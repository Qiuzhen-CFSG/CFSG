module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.OrbitBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.LargeDegree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.ImageReduction
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbit
public import Theory.Representation.BinaryOffender.ConjugateDisplacement.Codimension
/-!
# Odd linear-three obstruction through the actual central quotient

Three-conjugate generation bounds the codimension of the component-fixed
space by eighteen at cubic ratio at most two. Independently, any Irr⁺ seed
has a nontrivial irreducible central image. Its quasisimple actor has central
action kernel, so the original PSL₃(p) projective marking passes to its
faithful image. The native transitive-plane degree estimate makes this
central image larger than eighteen, hence so is the ambient fixed codimension.

This handles both zero and nonzero seed fixed spaces. It requires neither
irreducibility of the whole orbit nor a ratio bound on the seed.
Source: Aschbacher--Smith, 3.2.5, p.580, and the odd linear-three obstruction
in 13.1.4, p.867, with the Chapter K odd-linear estimates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) G W)


theorem two_free_fixedCodim_le_eighteen_pslThree (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (hr : cubicRatio ρ ≤ 2) : fixedCodim ρ (generalizedFitting G) ≤ 18 := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_involution_of_cubicRatio_le_nat ρ (a := 2) hr
  obtain ⟨g, hg⟩ := two_free_three_conjugates_pslThree hcore hq hp ho hm t ht ht2
  have hd' := fixedCodim_le_mul_of_conjugate_generation ρ _ t g hg
  have hrank := two_free_two_rank_pslThree hcore hq hp ho hm
  omega

theorem irrPlus_fixedCodim_gt_eighteen_pslThree
    (X : Subgroup G) [IsQuasisimple X] {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlus ρ X I) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : ClassicalGroup.IsPSL (X ⧸ center X) 3 p) :
    18 < fixedCodim ρ X := by
  let U := quotientImage ρ X I hI.choose
  let σ := U.toRepresentation
  have hirr : IsIrreducible σ := quotientImage_irreducible ρ hI
  have hk : σ.ker ≤ center X := by
    rcases IsQuasisimple.normal_le_center_or_eq_top σ.ker with hk | hk
    · exact hk
    exfalso
    apply hI.not_le_fixedSpace ρ
    rw [← hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, hv, rfl⟩
    have he : σ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (hk ▸ mem_top _)
    have he' := congrArg Subtype.val (LinearMap.congr_fun he
      (⟨(fixedSpace ρ X).mkQ v, ⟨v, hv, rfl⟩⟩ : U.toSubmodule))
    change (fixedSpace ρ X).mkQ (ρ x v) = (fixedSpace ρ X).mkQ v at he'
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ X).mkQ (ρ x v - v) = 0
    rw [map_sub, he', sub_self]
  let := OddSymplecticOrthogonal.actionImage_quasisimple σ hk
  let := imageRepresentation_isIrreducible σ hirr
  have hm' := hm.of_mulEquiv
    (OddSymplecticOrthogonal.actionImage_quotientCenterEquiv σ hk).symm
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm'
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (actionImage σ)))
  have hsurj : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcentral : f.ker ≤ center (actionImage σ) := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let : Fact p.Prime := ⟨hp⟩
  have hd := BinaryCoprimeDegree.central_quotient_transitive_plane_degree
    (imageRepresentation σ) (imageRepresentation_injective σ) f hsurj hcentral
    (by omega : p ≠ 2) (Matrix.PSL3.prime_hasTransitiveElementaryPlane F hcard)
  have hpdeg := BinaryCoprimeDegree.twenty_le_prime_times_binary_order hp hp5
  have hle : Module.finrank (ZMod 2) U.toSubmodule ≤ fixedCodim ρ X :=
    Submodule.finrank_le _
  omega
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
