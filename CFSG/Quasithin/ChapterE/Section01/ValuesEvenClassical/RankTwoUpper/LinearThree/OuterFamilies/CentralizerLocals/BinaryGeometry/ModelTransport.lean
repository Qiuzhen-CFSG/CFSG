module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.DerivedAutomorphismAction

/-!
# The full binary automorphism group from an outer source actor

Coefficient-field transport identifies the marked socle with SL₃(2).
Its outer automorphism group has order two. An actor outside the socle
therefore makes the faithful ambient conjugation action surjective. The
resulting equivalence takes the literal socle to the inner automorphisms.
Neither SQTK nor a separate automorphism-coverage assumption is needed.

This supplies the actual ambient comparison for the binary centralizer
branch of Aschbacher--Smith E.1.14(1), printed p.214. The centralizer and
generation calculations remain separate model obligations.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- Coefficient transport followed by the inverse of the actual central quotient. -/
noncomputable def binarySocleEquiv (e : generalizedFitting G ≃* PSL(3,F))
    (hF : Nat.card F = 2) : generalizedFitting G ≃* Matrix.PSL3Two.SL := by
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (e.trans (Atlas.fieldEquivPSL 3 ef)).trans Matrix.PSL3Two.equiv.symm

variable [IsSimpleGroup (generalizedFitting G)]

/-- An outer actor forces the ambient group to be the full automorphism group. -/
noncomputable def binaryAmbientEquiv (e : generalizedFitting G ≃* PSL(3,F))
    (hF : Nat.card F = 2) (A : Subgroup G) (houter : ¬ A ≤ generalizedFitting G) :
    G ≃* MulAut Matrix.PSL3Two.SL := by
  have hc := SimpleSocle.centralizer_eq_bot (socle_nonabelian e)
  have ho : Nat.card (MulAut.Outer (generalizedFitting G)) = 2 :=
    (Nat.card_congr (MulAut.outerCongr (binarySocleEquiv e hF)).toEquiv).trans
      Matrix.PSL3Two.Automorphisms.card_outer_sl
  have hnt : generalizedFitting G ≠ ⊤ := by
    intro he
    exact houter (he ▸ le_top)
  have hb := MulAut.conjNormal_bijective_of_outer_card_le_index
    (generalizedFitting G) hc (ho ▸ (generalizedFitting G).one_lt_index_of_ne_top hnt)
  exact (MulEquiv.ofBijective MulAut.conjNormal hb).trans
    (MulAut.congr (binarySocleEquiv e hF))

/-- Innerness under this actual equivalence is precisely membership in the socle. -/
theorem binaryAmbientEquiv_comap_inner (e : generalizedFitting G ≃* PSL(3,F))
    (hF : Nat.card F = 2) (A : Subgroup G) (houter : ¬ A ≤ generalizedFitting G) :
    (MulAut.innerSubgroup Matrix.PSL3Two.SL).comap
      (binaryAmbientEquiv e hF A houter).toMonoidHom = generalizedFitting G := by
  change ((MulAut.innerSubgroup Matrix.PSL3Two.SL).comap
    (MulAut.congr (binarySocleEquiv e hF)).toMonoidHom).comap
    (MulAut.conjNormal : G →* MulAut (generalizedFitting G)) = _
  rw [← MulAut.map_innerSubgroup_congr (binarySocleEquiv e hF),
    Subgroup.comap_map_eq_self_of_injective (MulAut.congr (binarySocleEquiv e hF)).injective,
    MulAut.conjNormal_comap_innerSubgroup,
    SimpleSocle.centralizer_eq_bot (socle_nonabelian e), sup_bot_eq]

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
