module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source

/-!
# The expanded meaning of c(H/N) = 1 in the escape argument

The ambient group here is a finite local stabilizer, not the free amalgam.
Write D = N[H,Q]. The source notation says that [H,Q,L] lies in N and
H/D is the direct sum of its fixed part and its actual natural moving part.
We retain elementary abelianness of H/N, all relative quotient normalities,
the literal fixed preimage, and equivariant coordinates for the moving factor.
The quotient marking has kernel exactly Q. In particular no dimension or
constituent label replaces the asserted natural representation.

These are output types for (4.3.1)(iii), not hypotheses of (4.3).
Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.3.1)(iii), pp.882--883.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
variable {A : Type*} [Group A]

/-- The inverse image of [H/N,Q] in H. -/
def radicalPreimage (Q H N : Subgroup A) : Subgroup A := N ⊔ ⁅H, Q⁆

/-- The inverse image of the moving part of H / (N[H,Q]). -/
def movingPreimage (Q H N : Subgroup A) : Subgroup A :=
  radicalPreimage Q H N ⊔ ⁅H, (⊤ : Subgroup A)⁆

/-- A literal split natural section, including the actual conjugation action.
Normality is inside A; applications take A to be the vertex stabilizer. -/
structure SingleNaturalSection (π : A →* SL) (Q L H N : Subgroup A) where
  projection_surjective : Function.Surjective π
  projection_kernel : π.ker = Q
  kernel_le : N ≤ H
  normal_group : H.Normal
  normal_kernel : N.Normal
  elementary : letI := normal_kernel
    IsElementaryAbelian 2 (H ⧸ N.subgroupOf H)
  radical_normal : (radicalPreimage Q H N).Normal
  triple_le : ⁅⁅H, Q⁆, L⁆ ≤ N
  decomposition : letI := radical_normal
    H = movingPreimage Q H N ⊔ centralizerModulo H ⊤ (radicalPreimage Q H N)
  intersection : letI := radical_normal
    movingPreimage Q H N ⊓ centralizerModulo H ⊤ (radicalPreimage Q H N) =
      radicalPreimage Q H N
  natural : RankOnePairing.NaturalFactor π ⊤ (movingPreimage Q H N)
    (radicalPreimage Q H N)

/-- The natural moving section has order eight by its actual quotient
isomorphism. This statement alone is weaker than SingleNaturalSection. -/
theorem SingleNaturalSection.moving_quotient_card
    {π : A →* SL} {Q L H N : Subgroup A}
    (s : SingleNaturalSection π Q L H N) :
    letI := s.natural.kernel_normal
    Nat.card (movingPreimage Q H N ⧸
      (radicalPreimage Q H N).subgroupOf (movingPreimage Q H N)) = 8 := by
  let := s.natural.kernel_normal
  rw [Nat.card_congr s.natural.quotientEquiv.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
