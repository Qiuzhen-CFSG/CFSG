module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.Contracts
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction

/-!
# Two-core existence reduced to marked odd-prime generation

A Sylow two-subgroup of the full centralizer of the original involution a
is Sylow in J₄. Sylow conjugacy therefore moves any proper Sylow overgroup
into one containing such a subgroup, and hence containing a. If its intrinsic
two-core is trivial, Baer–Suzuki supplies an odd-prime-order element inverted
by a inside that same overgroup. The certified ambient order restricts its
prime to 3, 5, 7, 11, 23, 29, 31, 37 or 43. The two marked generation inputs
then contradict properness. Finally the intrinsic core transports back
through the actual subgroup isomorphism.

This proves the assembly from `CentralSmallPrimeGeneration` and
`CentralLargePrimeGeneration`; neither input is discharged here. In particular,
the unconditional `maximalTwoCoreNontrivial` remains to be proved. No
maximal-overgroup cover, two-locality, elementary witness, or ambient simplicity
is assumed in the reduction. The imported Baer–Suzuki theorem and cardinality
certificate concern actual groups, not source-numbered records.

Source: Aschbacher–Smith A.1.2 and the sporadic Sylow-overgroup step of A.3.12,
printed pp.47–48, which cites Aschbacher (1986), Memoirs AMS 60, no.343;
Kleidman–Wilson (1988), pp.484–510. This elementary reduction isolates the
remaining exhaustive J₄ generation assertions from that source step.
-/

public section

open Subgroup Janko4
open BenderSuzuki.PFAppendixIII
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem odd_prime_support {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : q ∣ Nat.card Model) :
    q ∈ ({3, 5, 7, 11} : Finset ℕ) ∨ q ∈ ({23, 29, 31, 37, 43} : Finset ℕ) := by
  have h := Janko4.Simplicity.prime_dvd_model_order hq
    (by simpa only [Janko4.Cardinality.Thompson.model_card] using hd)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The exact marked obstruction in a subgroup containing the original a.
The odd-prime-order element belongs to M, and inversion is the literal
ambient conjugation action. No maximality assumption is needed. -/
theorem exists_inverted_odd_prime_of_twoCore_eq_bot
    (M : Subgroup Model) (haM : Janko4.a ∈ M) (hcore : pCore 2 M = ⊥) :
    ∃ q : ℕ, (q ∈ ({3, 5, 7, 11} : Finset ℕ) ∨
      q ∈ ({23, 29, 31, 37, 43} : Finset ℕ)) ∧
      ∃ r : Model, r ∈ M ∧ orderOf r = q ∧ (MulAut.conj Janko4.a) r = r⁻¹ := by
  let aM : M := ⟨Janko4.a, haM⟩
  have hoa : orderOf aM = 2 := by
    rw [← Subgroup.orderOf_coe, orderOf_a]
  have hi : IsInvolution aM := ((orderOf_eq_prime_iff).mp hoa).symm
  have hnot : aM ∉ pCore 2 M := by
    simpa only [hcore, Subgroup.mem_bot] using hi.ne_one
  obtain ⟨q, hq, hq2, r, hr, hinv⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime aM hi hnot
  have hr' : orderOf (r : Model) = q := by rwa [Subgroup.orderOf_coe]
  refine ⟨q, odd_prime_support hq hq2 ?_, (r : Model), r.property, hr', ?_⟩
  · rw [← hr']
    exact orderOf_dvd_natCard _
  · have hi' : IsInvolution Janko4.a := ((orderOf_eq_prime_iff).mp orderOf_a).symm
    have h := congrArg (fun x : M => (x : Model)) hinv
    simpa only [rightConjugateElem, aM, Subgroup.coe_mul, Subgroup.coe_inv,
      MulAut.conj_apply, hi'.inv_eq_self] using h

private theorem a_mem_centralizer_sylow
    (P : Sylow 2 (centralizer ({Janko4.a} : Set Model))) :
    Janko4.a ∈ (P : Subgroup (centralizer ({Janko4.a} : Set Model))).map
      (centralizer ({Janko4.a} : Set Model)).subtype := by
  have hc := Janko4.OuterReduction.OddIndex.centralizer_sylow_center P
  have hm : Janko4.a ∈ zpowers Janko4.a := mem_zpowers _
  rw [← hc] at hm
  obtain ⟨z, _, hz⟩ := hm
  change (z : Model) = Janko4.a at hz
  simpa only [hz] using z.property

/-- The two finite generation families rule out trivial intrinsic two-core
in every proper overgroup of a Sylow subgroup of the marked centralizer. -/
theorem twoCore_ne_bot_of_central_odd_prime_generation
    (hsmall : CentralSmallPrimeGeneration) (hlarge : CentralLargePrimeGeneration)
    (P : Sylow 2 (centralizer ({Janko4.a} : Set Model)))
    (M : Subgroup Model)
    (hPM : (P : Subgroup (centralizer ({Janko4.a} : Set Model))).map
      (centralizer ({Janko4.a} : Set Model)).subtype ≤ M) (hM : M ≠ ⊤) :
    pCore 2 M ≠ ⊥ := by
  intro hcore
  obtain ⟨q, hq, r, hrM, hr, hinv⟩ :=
    exists_inverted_odd_prime_of_twoCore_eq_bot M
      (hPM (a_mem_centralizer_sylow P)) hcore
  have hgen : closure (insert r
      ((P : Subgroup (centralizer ({Janko4.a} : Set Model))).map
        (centralizer ({Janko4.a} : Set Model)).subtype : Set Model)) = ⊤ := by
    rcases hq with hq | hq
    · exact hsmall P q hq r hr hinv
    · exact hlarge P q hq r hr hinv
  apply hM
  apply top_unique
  rw [← hgen]
  apply (closure_le M).mpr
  rintro x (rfl | hx)
  · exact hrM
  · exact hPM hx

/-- Application to the exact maximal-overgroup contract, with all Sylow and
intrinsic-core transports discharged. The two generation premises remain
independent mathematical obligations of this task's final assembly. -/
theorem maximalTwoCoreNontrivial_of_oddPrimeGeneration
    (hsmall : CentralSmallPrimeGeneration) (hlarge : CentralLargePrimeGeneration) :
    MaximalTwoCoreNontrivial := by
  intro S M hM hSM
  obtain ⟨P⟩ := Sylow.nonempty (p := 2)
    (G := centralizer ({Janko4.a} : Set Model))
  obtain ⟨T, hT⟩ := Janko4.OuterReduction.OddIndex.centralizer_sylow_is_ambient P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  let K := M.map e.toMonoidHom
  have hST : S.toSubgroup.map e.toMonoidHom = T.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  have hTK : T.toSubgroup ≤ K := by
    rw [← hST]
    exact map_mono hSM
  have hK : K ≠ ⊤ := by
    intro h
    apply hM.ne_top
    apply map_injective (f := e.toMonoidHom) e.injective
    change M.map e.toMonoidHom = (⊤ : Subgroup Model).map e.toMonoidHom
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact h
  have hcore := twoCore_ne_bot_of_central_odd_prime_generation hsmall hlarge P K
    (hT ▸ hTK) hK
  intro hzero
  apply hcore
  have he : (pCore 2 M).map (e.subgroupMap M).toMonoidHom = pCore 2 K :=
    @pCore_map_iso M K M.toGroup K.toGroup 2 (e.subgroupMap M)
  rw [← he, hzero, Subgroup.map_bot]
  rfl

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
