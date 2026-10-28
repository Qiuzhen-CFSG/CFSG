module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.Quotients
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.InnerMarking
public import Theory.SpecificGroups.SL2.SylowBorelSeparation

/-!
# A compatible natural module and Borel marking

Given a genuine natural L₂ block and the literal Sylow-normalizer image
of B in its two-core quotient, Sylow conjugacy places that image in the
standard upper Borel. Applying the same actor to the module preserves
the intertwining identity. The field degree remains the original one.

These are explicit reconstruction premises; this module does not select
the source row. Its consumer is the terminal contradiction in 14.6.15.
Source: Aschbacher--Smith 14.6.15, printed p.1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
variable {G : Type*} [Group G] [Finite G]

/-- A natural block and its literal Sylow-normalizer image can be marked
simultaneously on the quotient and the actual conjugation module. -/
theorem exists_naturalBorelModel_of_block {J B : Subgroup G} {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock J n)
    (hQB : pCore 2 J ≤ B.subgroupOf J)
    (hB : ∃ S : Sylow 2 (J ⧸ pCore 2 J),
      coreImage J B = normalizer (S : Set (J ⧸ pCore 2 J))) :
    ∃ b : NaturalBorelModel J B, b.field.degree = n := by
  obtain ⟨hn,_,F,_,_,hF,_,ρ,⟨model⟩,hnatural⟩ := hb
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let field : ChapterB.QuasisimpleSource.BinaryField :=
    { Carrier := F
      binaryAlgebra := ZMod.algebra F 2
      degree := n
      degree_pos := by omega
      card_eq := hF }
  obtain ⟨S,hS⟩ := hB
  let P := S.mapSurjective (f := model.quotientIso.toMonoidHom) model.quotientIso.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) P
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  have hP : (P : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom =
      Matrix.SpecialLinearGroup.upperUnipotent F := by
    change ((g • P : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [hg]
    rfl
  have hN : (coreImage J B).map model.quotientIso.toMonoidHom =
      normalizer (P : Set SL(2,F)) := by
    rw [hS]
    exact map_normalizer_eq_of_bijective _ model.quotientIso.bijective
  have hmark : ((coreImage J B).map model.quotientIso.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F := by
    rw [hN]
    calc
      _ = normalizer ((P : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom :
          Set SL(2,F)) := map_equiv_normalizer_eq (P : Subgroup SL(2,F)) (MulAut.conj g)
      _ = _ := by rw [hP]
  refine ⟨{ field := field
            large := ?_
            action := ρ
            model := model.innerMarking g
            natural := hnatural
            core_le := hQB
            borel := ?_ },rfl⟩
  · change 2 < Nat.card F
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  · change (B.subgroupOf J).map
      ((MulAut.conj g).toMonoidHom.comp
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J)))) = _
    rw [←Subgroup.map_map,←Subgroup.map_map]
    exact hmark

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
