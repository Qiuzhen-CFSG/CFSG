module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CoverRecovery
public import Theory.SpecificGroups.PSL3.UniversalProjection
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.G2Even.MarkedCover

/-!
# Recovering the nonbinary natural actors

The original L/O2(L) projection is injective for the SL3, Sp4 and G2 rows.
For SL3(4) the scalar-cover comparison is retained; other SL3 fields use
the universal projection. The symplectic and G2 cover theorems remove the
remaining two-group kernels. These results feed the literal Chapter11 input.
Source: Aschbacher--Smith A.3.5, I.1.1--4 and 12.2.2, pp.43,407--408,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

/-- Even SL3 recovery includes the scalar center and the exceptional field of
order four. The original surjection itself is proved injective. -/
theorem projection_injective_of_nonbinary_linearThree
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (F : BinaryField) (hF : 1 < F.degree)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    Function.Injective c.projection := by
  let := hq
  let := c.nontrivial
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := e.symm.surjective.nontrivial
  let f := e.toMonoidHom.comp c.projection
  have hf : Function.Surjective f := e.surjective.comp c.surjective
  let p := IsQuasisimple.centralQuotientEquiv f hf
  have h2 : Nat.card F.Carrier ≠ 2 := by
    rw [F.card_eq]
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    omega
  have hback : Nat.card (L ⧸ pCore 2 L) ≤
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
    by_cases h4 : Nat.card F.Carrier = 4
    · obtain ⟨g,hg,_⟩ := ChapterA.SQTKStructure.ReadyCoverCases.exists_psl3_four_scalar_cover
        (pCore_quotient_pCore_eq_bot 2) F.Carrier h4 p
      exact Nat.card_le_card_of_surjective g hg
    · let g := (Matrix.PSL3.UniversalProjection.projection_isUniversal h2 h4).lift
        (PerfectCentralCovering.centralQuotientCover p).toCovering
      exact Nat.card_le_card_of_surjective g.toMonoidHom g.surjective
  have hi : Function.Injective f :=
    ((Nat.bijective_iff_surjective_and_card f).mpr
      ⟨hf,le_antisymm hback (Nat.card_le_card_of_surjective f hf)⟩).1
  intro x y he
  exact hi (congrArg e he)

theorem projection_injective_of_nonbinary_symplectic
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (F : BinaryField) (hF : 1 < F.degree)
    (e : K ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    Function.Injective c.projection := by
  have hcard : 3 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    omega
  have hf := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.cover_injective
    hcard (c.modelCover hq e)
  intro x y he
  exact hf (congrArg e he)

theorem projection_injective_of_nonbinary_g2
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (F : BinaryField) (hF : 1 < F.degree)
    (e : K ≃* Atlas.G2.Model F.Carrier) : Function.Injective c.projection := by
  let := hq
  let := c.nontrivial
  let : Nontrivial (Atlas.G2.Model F.Carrier) := e.symm.surjective.nontrivial
  let f := e.toMonoidHom.comp c.projection
  have hf : Function.Surjective f := e.surjective.comp c.surjective
  let : IsQuasisimple (Atlas.G2.Model F.Carrier) := IsQuasisimple.of_surjective f hf
  let h := c.modelCover hq e
  have hi := (universalQuasisimpleCover_isUniversal (Atlas.G2.Model F.Carrier)).injective_of_pGroup_kernel
    (Atlas.G2.FiniteCover.universalKernel_isPGroup_of_card_pow F.card_eq (by omega))
    h.toCovering (pCore_quotient_pCore_eq_bot 2)
  intro x y he
  exact hi (congrArg e he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
