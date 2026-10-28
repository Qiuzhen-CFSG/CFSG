module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeRecognition
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticSource
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.PerfectNormalizer

/-!
# The original perfect L-image in the symplectic block quotient

The full symplectic quotient has order greater than 8!, so the actual star
radical's normalizer lies in the source local intersection. This intersection
normalizes L. Perfectness and nontriviality of the original L-image therefore
identify it with a point or plane residual, in the same symplectic coordinates.
No action of a graph automorphism or abstract local isomorphism is substituted.

Source: Aschbacher–Smith C.4.5 and C.4.1(2), printed pp.151–153.
The next module uses the full module to exclude the point marking.
-/
public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem SourceConfiguration.block_sp4_radical_placement_of_equiv
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (e₀ : (c.K ⧸ pCore 2 c.K) ≃* Sp F) :
    IsPRadical 2
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ∧
      normalizer
        (((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
          (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) :
          Set (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≤
        (starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
          (c.H ⊓ normalizer (L : Set G))).subgroupOf
            (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  have he : (c.K.map c.H.subtype).subgroupOf c.H = c.K :=
    c.K.comap_map_eq_self_of_injective c.H.subtype_injective
  let : ((c.K.map c.H.subtype).subgroupOf c.H).Normal := he.symm ▸ c.component_normal
  exact C27Source.star_symplectic_radical_placement (c.block_source_input hf)
    ((c.block_star_quotientEquiv hb).symm.trans e₀) hF

/-- The original L-image is a parabolic residual under an inner marking of
 the original quotient isomorphism. -/
theorem SourceConfiguration.block_symplectic_local_conjugate
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hcard : Nat.card F = 2^n)
    (e₀ : (c.K ⧸ pCore 2 c.K) ≃* Sp F) :
    ∃ g : Sp F,
      c.componentQuotientL.map (e₀.trans (MulAut.conj g)).toMonoidHom = pointLocal ∨
      c.componentQuotientL.map (e₀.trans (MulAut.conj g)).toMonoidHom = planeLocal := by
  have hF : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let C := starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)
  let R := (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf C
  let B := (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf C
  let E := (c.block_star_quotientEquiv hb).symm.trans e₀
  have hB : c.componentQuotientL.map (c.block_star_quotientEquiv hb).toMonoidHom = B :=
    c.componentQuotientL_star hb
  let : Group.IsPerfect c.componentQuotientL := c.componentQuotientL_perfect
  let : Group.IsPerfect B := hB ▸ Group.IsPerfect.map (c.block_star_quotientEquiv hb).toMonoidHom
  have hBne : B ≠ ⊥ := fun he => c.componentQuotientL_ne_bot
    ((map_eq_bot_iff_of_injective _ (c.block_star_quotientEquiv hb).injective).mp (hB.trans he))
  have hp := c.block_sp4_radical_placement_of_equiv hf hb hF e₀
  have hBN := c.block_star_L_le_radical_normalizer
  have hNB := hp.2.trans c.block_star_local_normalizes_L
  let B' := B.map E.toMonoidHom
  let R' := R.map E.toMonoidHom
  let : Group.IsPerfect B' := Group.IsPerfect.map E.toMonoidHom
  have hB' : B' ≠ ⊥ := fun he => hBne ((B.map_eq_bot_iff_of_injective E.injective).mp he)
  have hBR : B' ≤ normalizer (R' : Set (Sp F)) := by
    rw [←map_equiv_normalizer_eq R E]
    exact map_mono hBN
  have hRB : normalizer (R' : Set (Sp F)) ≤ normalizer (B' : Set (Sp F)) := by
    rw [←map_equiv_normalizer_eq R E,←map_equiv_normalizer_eq B E]
    exact map_mono hNB
  obtain ⟨g,he⟩ := Theory.SpecificGroups.SymplecticFour.RadicalNormalizer.radical_perfect_normal_conjugate
    R' B' (hp.1.map_equiv E) hB' hBR hRB hcard hn
  have hBE : B' = c.componentQuotientL.map e₀.toMonoidHom := by
    change B.map E.toMonoidHom = c.componentQuotientL.map e₀.toMonoidHom
    rw [←hB]
    have hhom : E.toMonoidHom.comp (c.block_star_quotientEquiv hb).toMonoidHom =
        e₀.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact congrArg e₀ ((c.block_star_quotientEquiv hb).symm_apply_apply x)
    rw [Subgroup.map_map, hhom]
  refine ⟨g,?_⟩
  have hh : c.componentQuotientL.map
      (e₀.trans (MulAut.conj g)).toMonoidHom =
      B'.map (MulAut.conj g).toMonoidHom := by
    rw [hBE]
    have hhom : (e₀.trans (MulAut.conj g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom := rfl
    rw [hhom]
    exact (Subgroup.map_map c.componentQuotientL
      (MulAut.conj g).toMonoidHom e₀.toMonoidHom).symm
  rw [hh]
  exact he.imp And.right And.right

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
