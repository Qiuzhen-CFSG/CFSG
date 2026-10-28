module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Source
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.LinearRingEquiv
/-!
# The prime-seven boundary of the odd PSL₂ source branch

The actual exceptional isomorphism PSL₂(7) ≃ PSL₃(2) carries the original
normal component to the degree-one binary linear-three model. The checked
source theorem for that model forces degree greater than one whenever the
original Sylow normalizes an elementary subgroup of order at least four.
Thus this boundary is excluded with the original corefree maximal subgroup.

Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
/-- The original noncyclic elementary E.2.7 setup excludes PSL₂(7). -/
theorem prime_seven_source_not_elementary_four
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : (ChapterB.minimalParabolicMax T hP).normalCore = ⊥)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7)
    (eK : K ≃* PSL(2,F))
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card V) : False := by
  let := Fintype.ofFinite F
  let eF : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e := (eK.trans (psl2RingEquiv eF).symm).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup K := eK.isSimpleGroup
  let := hV
  have hh := Witnesses.LinearThree.one_lt_parameter (ZMod 2) (by norm_num : Nat.card (ZMod 2) = 2 ^ 1)
    K e T (by decide : 0 < 1) hgen hP hcore V hVT hVN hcard
  omega
end CFSG.Quasithin.ChapterE.Structure
