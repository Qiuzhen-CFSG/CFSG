module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Action
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections

/-!
# The actual binary degree-eight section

The faithful quotient of the conjugation action embeds in GL₈(2).
The central two-core quotient is its surjective image, so it is an
actual section of GL₈(2), with the literal original K as numerator.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterA.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The literal K/O₂,Z(K) is a section of the binary linear group. -/
theorem coreCentral_isSectionOf_binary_eight_of_kernel_le
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hcard : Nat.card (CentralQuotient E) ≤ 256)
    (hk : (centralAction E).ker ≤ centralPreimage (pCore 2 E.K)) :
    IsSectionOf (coreCentralQuotient E.K)
      (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 8) (CentralQuotient E) hcard
  let a : (E.K ⧸ (centralAction E).ker) →* MulAut (CentralQuotient E) :=
    QuotientGroup.kerLift (centralAction E)
  let q : (E.K ⧸ (centralAction E).ker) →*
      (E.K ⧸ centralPreimage (pCore 2 E.K)) :=
    QuotientGroup.map _ _ (MonoidHom.id E.K) hk
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (centralPreimage (pCore 2 E.K)) z
    exact ⟨QuotientGroup.mk' (centralAction E).ker k,rfl⟩
  let e := centralPreimageQuotientEquiv (pCore 2 E.K)
  exact (IsSectionOf.of_surjective (e.toMonoidHom.comp q) (e.surjective.comp hq)).ambient_injective
    (f.comp a) (hf.comp (QuotientGroup.kerLift_injective _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
