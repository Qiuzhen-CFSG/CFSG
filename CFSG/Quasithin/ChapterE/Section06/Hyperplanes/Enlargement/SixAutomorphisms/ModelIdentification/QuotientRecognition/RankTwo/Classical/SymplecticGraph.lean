module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.GraphFieldFixedResidual
/-!
# Excluding the symplectic graph-field branch

The fixed group of the explicit odd graph power is identified with the
concrete Suzuki matrix group, using its proved matrix-coordinate equivalence.
Suzuki order is prime to three, so this fixed group contains no A₆ subgroup.
The conjugacy transport also records a genuine ambient group equivalence
carrying an automorphism to its representative.

Source: Aschbacher–Smith, 16.1.4(7), printed p.1171; E.6.23, printed p.254.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The genuine graph-field fixed group has no A₆ subgroup. -/
theorem not_six_graph {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (S : Subgroup (Sp F))
    (hS : S ≤ (graphFieldAut (F := F) m).fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  let e := fixedEquivOfBinaryModel m hF (fixedSuzukiEquiv m)
  rintro ⟨s⟩
  let j := e.toMonoidHom.comp ((inclusion hS).comp s.symm.toMonoidHom)
  have hj : Function.Injective j :=
    e.injective.comp ((inclusion_injective hS).comp s.symm.injective)
  have hd := Subgroup.card_dvd_of_injective j hj
  rw [alternatingGroup.SixSubgroupObstructions.card_six] at hd
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm
    ((by decide : 3 ∣ 360).trans hd)

variable {D : Type*} [Group D]
omit [Finite F] [CharP F 2] in
/-- Actual automorphism conjugacy gives a compatible ambient equivalence. -/
theorem exists_compatible_of_isConj (e : D ≃* Sp F) (a : MulAut D) (b : MulAut (Sp F))
    (h : IsConj (MulAut.congr e a) b) : ∃ f : D ≃* Sp F, MulAut.congr f a = b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨e.trans c, ?_⟩
  apply MulEquiv.ext
  intro x
  exact congrArg (fun d : MulAut (Sp F) => d x) hc

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
