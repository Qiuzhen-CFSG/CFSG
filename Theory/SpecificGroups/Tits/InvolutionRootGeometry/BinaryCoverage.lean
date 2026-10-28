module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryCoverage.Certificate
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction

/-!
# Complete involution coverage in the actual binary Ree group

Sylow conjugacy puts any involution in the actual positive subgroup. Its
square-one elements lie in the derived subgroup and have one of the 2048
marked Atlas Sylow normal forms. The checked two-root certificate therefore
supplies an ambient root conjugacy. The existing outer centralizers correct
the conjugator to the derived group, retaining the literal underlying element.

Source: Aschbacher--Smith 16.1.4, printed p.1171; GLS3 Table 2.4 and
Parrott (1972), section 5, p.683. This supplies the original Chapter K
Tits displacement consumer's full binary involution-coverage premise.
-/

public section
namespace Tits.InvolutionRootGeometry
open Subgroup ReeF4
open ExceptionalParabolics.FullRee

/-- Full binary Ree involutions belong to the derived subgroup and to one
of its two intrinsically marked root conjugacy classes. -/
theorem binaryInvolutionCoverage : BinaryInvolutionCoverage := by
  intro g hsq hne
  have ho : orderOf g = 2 := orderOf_eq_prime hsq hne
  have hpg : IsPGroup 2 (zpowers g) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, ho]; rfl)
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Model 0) P sylow
  let x := MulAut.conj c g
  have hxP : x ∈ ((c • P : Sylow 2 (Model 0)) : Subgroup (Model 0)) :=
    ((P.equivSMul c) ⟨g, hP (mem_zpowers g)⟩).property
  have hxU : x ∈ ReeF4.Parabolics.unipotent 0 := by
    change x ∈ ExceptionalParabolics.FullRee.S
    rw [← sylow_coe, ← hc]
    exact hxP
  have hx2 : x ^ 2 = 1 := by
    change (MulAut.conj c g) ^ 2 = 1
    rw [← map_pow, hsq, map_one]
  have hxne : x ≠ 1 := by
    intro hh
    exact hne ((MulAut.conj c).injective (hh.trans (map_one (MulAut.conj c)).symm))
  obtain ⟨n, hn⟩ := BinaryDerivedFusion.square_one_atlas_normalForm x hxU hx2
  have hn2 : atlas1600SylowTwoNormalForm n ^ 2 = 1 := atlasEmbedding_injective (by
    rw [map_pow, hn, hx2, map_one])
  have hnne : atlas1600SylowTwoNormalForm n ≠ 1 := by
    intro hh
    apply hxne
    rw [← hn, hh, map_one]
  have hlong : atlasEmbedding (atlas1600ParrottAssignment .s1) = (longRoot : Model 0) := by
    simp only [atlasEmbedding_generator, longRoot, derivedEquiv_coe, embedding_generator]
  have hshort : atlasEmbedding (atlas1600ParrottAssignment .s4) = (shortRoot : Model 0) := by
    simp only [atlasEmbedding_generator, shortRoot, derivedEquiv_coe, embedding_generator]
  have hxclass : IsConj (longRoot : Model 0) x ∨ IsConj (shortRoot : Model 0) x := by
    rcases BinaryCoverage.normalForm_root_classes n hn2 hnne with h | h
    · exact Or.inl (by simpa only [hlong, hn] using atlasEmbedding.map_isConj h)
    · exact Or.inr (by simpa only [hshort, hn] using atlasEmbedding.map_isConj h)
  have hgx : IsConj g x := isConj_iff.mpr ⟨c, rfl⟩
  exact BinaryDerivedFusion.root_lift g (hxclass.imp
    (fun h => h.trans hgx.symm) (fun h => h.trans hgx.symm))

end Tits.InvolutionRootGeometry
