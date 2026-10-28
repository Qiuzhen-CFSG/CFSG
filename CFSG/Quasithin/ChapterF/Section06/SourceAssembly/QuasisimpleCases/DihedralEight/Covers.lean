module

public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.Alternating.OddCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import GorensteinWalter.PSL2SchurMultiplier

/-!
# Actual odd central covers in the dihedral-eight branch

The universal SL2 cover has kernel of order two away from field order
nine. Consequently a quasisimple group with odd center and such a central
quotient is the actual PSL2 model. At order nine, the actual PSL2(9)-A6
comparison and the alternating universal-cover theorem leave A6 or its
concrete hexacode triple cover. The same alternating theorem identifies
the degree-seven alternative with A7 or the constructed triple cover.

Source: Aschbacher--Smith I.1.3 and F.6.18, printed pp.407 and 310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GLS3.Chapter5
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

theorem quasisimple_alternating_six_of_odd_center
    (hodd : Odd (Nat.card (center L)))
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6)) :
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases OddCentralCovers.odd_center_alternatives 6 (by decide) e hodd with hc | ⟨_, hc⟩
  · exact .inl ⟨OddCentralCovers.alternatingEquivOfCenterCardOne 6 e hc⟩
  · exact .inr (OddCentralCovers.triple_six_equiv_hexacode e hc)

theorem quasisimple_alternating_seven_of_odd_center
    (hodd : Odd (Nat.card (center L)))
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7)) :
    Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ≃* OddCentralCovers.TripleSeven) := by
  rcases OddCentralCovers.odd_center_alternatives 7 (by decide) e hodd with hc | ⟨_, hc⟩
  · exact .inl ⟨OddCentralCovers.alternatingEquivOfCenterCardOne 7 e hc⟩
  · exact .inr (OddCentralCovers.triple_seven_equiv e hc)

/-- The model map lifts through the actual central quotient except for
precisely the triple cover at field order nine. -/
theorem quasisimple_odd_psl2_of_odd_center
    (hodd : Odd (Nat.card (center L))) {q : ℕ} (hq : Odd q)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) :
    ClassicalGroup.IsPSL L 2 q ∨
      (q = 9 ∧ Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial PSL(2,F) := e.symm.surjective.nontrivial
  have ho : Odd (Nat.card F) := hF ▸ hq
  have hlarge := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    ho (Group.IsPerfect.not_isSolvable PSL(2,F))
  let : Fact (3 < Nat.card F) := ⟨hlarge⟩
  by_cases h9 : Nat.card F = 9
  · let a := Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 h9
    rcases quasisimple_alternating_six_of_odd_center hodd (e.trans a) with hj | hj
    · obtain ⟨j⟩ := hj
      exact .inl ⟨F, inferInstance, inferInstance, hF, ⟨j.trans a.symm⟩⟩
    · exact .inr ⟨hF.symm.trans h9, hj⟩
  · let f := PerfectCentralCovering.centralQuotientCover e
    have hd := Covering.coveringKernel_card_dvd_of_universal
      (GorensteinWalter.PSL2Cover.cover F)
      (GorensteinWalter.PSL2Cover.isUniversal_of_odd F ho h9) f.toCovering
    change Nat.card (PerfectCentralCovering.centralQuotientCover e).toMonoidHom.ker ∣
      Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker at hd
    rw [PerfectCentralCovering.centralQuotientCover_ker,
      show Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker = 2 from
        GorensteinWalter.sl2ProjectiveProjection_ker_card F ho] at hd
    have hc : Nat.card (center L) = 1 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hc | hc
      · exact hc
      · rw [hc] at hodd
        norm_num at hodd
    have hbot : f.toMonoidHom.ker = ⊥ := by
      rw [PerfectCentralCovering.centralQuotientCover_ker]
      exact (eq_bot_iff_card _).mpr hc
    let j := MulEquiv.ofBijective f.toMonoidHom
      ⟨f.toMonoidHom.ker_eq_bot_iff.mp hbot, f.surjective⟩
    exact .inl ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
