module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.SourceCases

/-!
# The doubled moving quotient has no central kernel

The action on U has dimension at most six. A surjective map onto two
natural binary three-spaces is therefore bijective, giving actual natural
coordinates on U and trivial intersection with C. The one-copy branch
retains its central kernel and is not declared split.

Source: Meierfrankenfeld–Stellmacher (1993), (3.2)(iii),(iv), p.863.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The actual U has at most six binary dimensions, before any splitting. -/
theorem U_card_le_64 (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) : Nat.card (U R (alpha R)) ≤ 64 := by
  let := geometry.U_elementary hb (alpha R) rfl
  let := finite_Z R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  have hd := AbelianCore.QuotientRecognition.ExtensionControl.finrank_le_six
    (Offenders.linearize (uAction source)) (uAction_full source geometry hb)
      (uAction_isFFModule source geometry hb)
  change Nat.card (Additive (U R (alpha R))) ≤ 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd)

/-- Two natural quotient copies already fill the dimension bound, so their
projection is an isomorphism. No central extension is discarded in the one-copy case. -/
theorem MovingQuotient.two_injective (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (q : MovingQuotient source 2) : Function.Injective q.projection := by
  let := finite_Z R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  apply (q.onto.bijective_of_nat_card_le ?_).1
  have hc : Nat.card (Multiplicative (Fin 2 → Fin 3 → ZMod 2)) = 64 := by
    simp [Nat.card_eq_fintype_card]
  rw [hc]
  exact U_card_le_64 source geometry hb

/-- The doubled moving layer has actual marked natural coordinates. -/
noncomputable def MovingQuotient.twoCopies (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (q : MovingQuotient source 2) : MovingCopies source 2 where
  marking := q.marking
  equiv := MulEquiv.ofBijective q.projection ⟨q.two_injective source geometry hb, q.onto⟩
  action := q.action

/-- The doubled branch has zero intersection between the moving and fixed parts. -/
theorem MovingQuotient.two_disjoint (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (q : MovingQuotient source 2) :
    Disjoint (fixedPart R) (U R (alpha R)) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  let u : U R (alpha R) := ⟨x, hx.2⟩
  have hk : u ∈ q.projection.ker := q.kernel.symm ▸ hx.1
  have hu : u = 1 := q.two_injective source geometry hb (hk.trans q.projection.map_one.symm)
  exact congrArg Subtype.val hu

/-- A checked partial dichotomy: the one-copy quotient keeps its full central
kernel; the doubled quotient is already an actual direct pair of natural modules.
The reconstruction of X and the order-two bound on the one-copy kernel remain open. -/
theorem moving_quotient_or_double (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    Nonempty (MovingQuotient source 1) ∨
      (Nonempty (MovingCopies source 2) ∧ Disjoint (fixedPart R) (U R (alpha R))) := by
  obtain ⟨m, hm, ⟨q⟩⟩ := exists_movingQuotient source geometry hb
  rcases hm with rfl | rfl
  · exact Or.inl ⟨q⟩
  · exact Or.inr ⟨⟨q.twoCopies source geometry hb⟩, q.two_disjoint source geometry hb⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
