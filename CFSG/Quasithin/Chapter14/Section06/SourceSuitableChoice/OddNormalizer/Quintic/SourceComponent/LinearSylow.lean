module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.OddLinearExclusion
public import Theory.SpecificGroups.SL3.QuinticParabolic

/-!
# The surviving linear-three radical is Sylow

The actual radical intersection has its normalizer inside the marked star
intersection. A nonsylow radical normalizer in SL₃ is a full parabolic in
natural coordinates. The original first factor preserves this normalizer,
is solvable, and is normalized by it, contradicting the intrinsic quintic
parabolic calculation. Thus the surviving radical is itself Sylow.

This is an intermediate result of original 14.6.15, printed p.1035.
The Borel comparison and final assembly remain with qt-e-14615-quintic-exclusion.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The original radical intersection is a full Sylow subgroup in every
surviving SL₃ row: each nonsylow radical normalizer would be a forbidden parabolic. -/
theorem source_component_linear_radical_sylow (F : BinaryField)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(3,F.Carrier)) :
    ∃ S : Sylow 2 (starImage j.J (Mc.pCoreIn 2) j.J),
      (S : Subgroup _) = (starImage j.J (Mc.pCoreIn 2) (Mc.pCoreIn 2)).subgroupOf
        (starImage j.J (Mc.pCoreIn 2) j.J) := by
  have hd := source_component_linear_degree_mod_four s d j F e
  have hl : 1 < F.degree := by omega
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let Q := (starImage j.J R R).subgroupOf C
  let N := normalizer (Q : Set C)
  let f := (starComponentAction j.J R).comp
    (inclusion (source_first_le_common_normalizer s d j))
  let : Group.IsSolvable d.K1 := source_first_factor_solvable s d
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hi := source_component_input s d j
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    have h4 : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hl
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left h4 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^3*(4^3-1)*(4^2-1)) hh
  obtain ⟨hr,hN⟩ := star_intersection_placement_from_source_of_large_order hi hlarge
  have hNf : N.map MulAut.conj ≤ normalizer (f.range : Set _) := by
    have he : f.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (R : Set G))).map
          (starComponentAction j.J R) := by rw [MonoidHom.range_comp,inclusion_range]
    rw [he]
    exact (map_mono hN).trans (source_borel_normalizes_first_actor s d j hi.normalizes)
  have hfix : ∀ b ∈ f.range, N.map b.toMonoidHom = N := by
    rintro _ ⟨k,rfl⟩
    change (normalizer (Q : Set C)).map (f k).toMonoidHom = normalizer (Q : Set C)
    rw [map_equiv_normalizer_eq]
    exact congrArg (fun U : Subgroup C => normalizer (U : Set C))
      (source_component_radical_intersection_fixed s d j
        (inclusion (source_first_le_common_normalizer s d j) k))
  rcases Matrix.PSL3.LinearThree.RadicalNormalizer.radical_normalizer_parabolic_or_sylow
    (Q.map e.toMonoidHom) (hr.map_equiv e) hl F.card_eq with ⟨b,hb⟩ | ⟨S,hS⟩
  · let t := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj b)
    have hmark : N.map t.toMonoidHom = Matrix.PSL3.LinearThree.pointParabolicSL F.Carrier ∨
        N.map t.toMonoidHom = Matrix.PSL3.LinearThree.lineParabolicSL F.Carrier := by
      change N.map ((Matrix.HigherLinear.SubspaceTransport.slConj b).toMonoidHom.comp
        e.toMonoidHom) = _ ∨ N.map ((Matrix.HigherLinear.SubspaceTransport.slConj b).toMonoidHom.comp
        e.toMonoidHom) = _
      simpa only [N,←map_map,map_equiv_normalizer_eq] using hb
    obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
    exact (Matrix.PSL3.LinearThree.QuinticParabolic.no_solvable_parabolic_quintic_of_equiv
      F.Carrier hl F.card_eq (source_component_linear_degree s d j F e) t N hmark
      f.range hfix hNf _ ⟨⟨k,hk⟩,rfl⟩ ha).elim
  · refine ⟨S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
    change (S : Subgroup SL(3,F.Carrier)).map e.symm.toMonoidHom = Q
    rw [hS,map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C := by
      ext x : 1
      exact e.symm_apply_apply x
    rw [he,map_id]

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
