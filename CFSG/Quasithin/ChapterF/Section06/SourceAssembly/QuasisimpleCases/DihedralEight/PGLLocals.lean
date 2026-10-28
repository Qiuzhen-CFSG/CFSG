module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.ProperResidualLocals
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PrimeExtension
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Theory.SpecificGroups.PSL2.CubicFourExclusion
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# The marked PGL2 row in the dihedral-eight branch

The proper PSL2 residual forces one good and one exceptional vertex.
The exceptional rotation-character model contains C3 times E4 and cannot
embed in odd PGL2. The remaining compatible amalgam is the reflection
model, with vertices S4 and D24. A Sylow four-group of the original
residual normalizes its cubic local residual; the involution-centralizer
calculation gives the additional prime congruence eleven or thirteen
modulo twenty-four.

Source: Aschbacher--Smith F.6.18(5), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GorensteinWalter
open Theory.GroupTheory.RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem reflection_amalgam_of_pgl_embedding
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (f : G →* PGL2 F) (hf : Function.Injective f) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.reflectionCharacter)) := by
  rcases h.mixed_eight_cases hcore hgood hbad hT with hi | hi
  · exact hi
  · obtain ⟨iso⟩ := hi
    let g := f.comp (G₂.subtype.comp
      (iso.right.symm.toMonoidHom.comp MixedEight.baseHom))
    have hg : Function.Injective g := hf.comp (G₂.subtype_injective.comp
      (iso.right.symm.injective.comp MixedEight.baseHom_injective))
    exact (Theory.PSL2.no_injective_cubic_four_product hF g hg).elim

/-- Actual compatible local markings in the proper prime PSL2 branch. -/
theorem reflection_amalgam_of_proper_psl_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hproper : pResidual 2 G ≠ ⊤) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL (pResidual 2 G) 2 p) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.reflectionCharacter)) := by
  obtain ⟨eG⟩ := pgl_prime_of_proper_psl_twoResidual hFstar hproper hlarge hm
  have hF : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  rcases mixed_vertices_of_proper_psl_residual h hcore hT hproper Fact.out hp
    (by decide : 1 ≤ 1) (by simpa using hm) with ⟨hg, hb⟩ | ⟨hg, hb⟩
  · exact .inl (reflection_amalgam_of_pgl_embedding h hcore hT hg hb hF
      eG.toMonoidHom eG.injective)
  · exact .inr (reflection_amalgam_of_pgl_embedding h.symm hcore
      (by simpa only [inf_comm G₂ G₁] using hT) hg hb hF eG.toMonoidHom eG.injective)

end CFSG.Quasithin.ChapterF.SourceAssembly
