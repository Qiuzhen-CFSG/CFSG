module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.Reduction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.Geometry
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.PSL3.SmallSylowOddCore
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SL2.BinaryDihedral
public import Theory.SpecificGroups.DihedralSolvable
public import GorensteinWalter.PSL2Center

/-!
# The complete small Borel model inspection in E.6.19

The rank-one cases use actual Sylow pointwise innerness and the concrete
proper-overgroup theorem. Small PSL₃ root centralizers are two-groups.
Perfect central quotient transport retains every actual central two-cover
of PSL₃(4), with exactly the original acting group and involution centralizer.
The solvable PSL₂(2) and PSU₃(2) endpoints contradict the genuine
quasisimplicity of the detected component.

The final application uses the faithful induced action supplied by the
original E.6.19 geometry. It consumes no model inspection assumption and
no identification of an original fixed subspace with a model subspace.

Source: Aschbacher–Smith E.6.19, printed p.252 (PDF p.263), with the
Borel rows in E.6.8(1), pp.247–248, and Sylow geometry in F.1.3(1).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
open BenderSuzuki.MatrixGroups
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
variable {L : Subgroup G} {φ : H →* MulAut L} {E : Subgroup H}

/-- Binary PSL₂ models have the required odd-core conclusion on the original actors. -/
theorem binary_psl_two_oddCore_eq_bot {n : ℕ} (hn : 0 < n)
    (d : Theory.GroupAction.SylowFixedInvolution φ E)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  apply (d.equiv e).oddCore_eq_bot_of_sylow_overgroups
    (GorensteinWalter.psl2_center_eq_bot F) Theory.PSL2.aut_fixing_sylow_inner
  intro S M hSM hM
  exact (ChapterF.Source.rankOneSylowFacts_psl2 F n hn hF S).unique_maximal M hSM hM

/-- The actual PSU₃(4) model has trivial odd core in this involution centralizer. -/
theorem psu_three_four_oddCore_eq_bot
    (d : Theory.GroupAction.SylowFixedInvolution φ E)
    (hm : ClassicalGroup.IsPSU L 3 4) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨F,hfield,hfinite,J,hF,hconj,⟨e⟩⟩ := hm
  have hfixed : Nat.card {x : F // J.conj x = x} = 4 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
      (by decide) hF hconj
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv L e.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J 4 (by decide) hF hfixed
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    J.projective_isPerfect_of_fixed_card (by decide : 2 < 4) hF hfixed
  have hc : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  apply (d.equiv e).oddCore_eq_bot_of_sylow_overgroups hc
    (HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj J (n := 2)
      (by decide) hF hconj)
  intro S M hSM hM
  exact (ChapterF.Source.rankOneSylowFacts_psu3 J 2 (by decide) hF hconj S).unique_maximal
    M hSM hM

omit [Finite G] [Finite H] in
/-- The nonsimple binary linear endpoint cannot be a genuine quasisimple component. -/
theorem not_psl_two_two [IsQuasisimple L] (hm : ClassicalGroup.IsPSL L 2 2) : False := by
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF]
    decide)
  let j := (e.trans (Atlas.fieldEquivPSL 2 f)).trans
    Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm
  let : Group.IsSolvable (DihedralGroup 3) := GLS3.Chapter5.dihedralGroup_isSolvable 3
  let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
    (f := j.toMonoidHom) j.injective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact Group.IsPerfect.not_isSolvable L inferInstance

omit [Finite G] [Finite H] in
/-- The fixed-field-two unitary endpoint is solvable and cannot be quasisimple. -/
theorem not_psu_three_two [IsQuasisimple L] (hm : ClassicalGroup.IsPSU L 3 2) : False := by
  obtain ⟨F,hfield,hfinite,J,hF,hconj,⟨e⟩⟩ := hm
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    HermitianForm.FixedFieldTwo.projective_isSolvable J hF hconj
  let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact Group.IsPerfect.not_isSolvable L inferInstance

/-- Every actual small Borel model, including every specified central two-cover,
has trivial odd core in the original actor centralizer. -/
theorem smallBorel_oddCore_eq_bot [IsQuasisimple L]
    (d : Theory.GroupAction.SylowFixedInvolution φ E) (hm : SmallBorelModel L) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  rcases hm with h2 | h4 | h32 | h34 | hu2 | hu4 | hcover
  · exact (not_psl_two_two h2).elim
  · exact binary_psl_two_oddCore_eq_bot (n := 2) (by decide) d h4
  · obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := h32
    exact Matrix.PSL3.EvenInnerCentralizers.small_sylowFixedInvolution_oddCore_eq_bot
      F (n := 1) (by decide) (by decide) hF (d.equiv e)
  · obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := h34
    exact Matrix.PSL3.EvenInnerCentralizers.small_sylowFixedInvolution_oddCore_eq_bot
      F (n := 2) (by decide) (by decide) hF (d.equiv e)
  · exact (not_psu_three_two hu2).elim
  · exact psu_three_four_oddCore_eq_bot d hu4
  · obtain ⟨_,F,hfield,hfinite,hF,⟨e⟩⟩ := hcover
    exact Matrix.PSL3.EvenInnerCentralizers.small_sylowFixedInvolution_oddCore_eq_bot
      F (n := 2) (by decide) (by decide) hF (d.centralQuotient e)

omit [Finite H] in
/-- The actual detected component in E.6.19 cannot be any small Borel model. -/
theorem detected_not_smallBorel {A U V M : Subgroup G}
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hUV : U ≤ V) (hindex : A.relIndex U = 2)
    (d : DetectedComponent A U V L) : ¬ SmallBorelModel L := by
  intro hm
  let : IsQuasisimple L := d.quasisimple
  exact d.action_oddCore (smallBorel_oddCore_eq_bot
    (detected_sylowFixedInvolution h hA hUV hindex d) hm)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
