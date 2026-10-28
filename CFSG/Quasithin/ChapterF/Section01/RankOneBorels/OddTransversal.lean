module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.SylowOddTransversal
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.SpecificGroups.SL2.OddBorelTransversal
public import Theory.SpecificGroups.Suzuki.SylowIntersections
public import Theory.SpecificGroups.DihedralSolvable

/-!
# Odd transversals for the complete original rank-one catalogue

TI Sylows give odd representatives of the Suzuki and projective-unitary
Borel cosets. The unitary regular root action includes fixed-field order two;
the full special-unitary result lifts through its actual central projection.
The linear calculation and odd Hall complements handle the remaining rows.
The result retains the caller's Sylow and its literal normalizer, so it can
be applied before recognizing any enlarged local group.

Source: DGS, Groups and Graphs (1985), the odd neighbor transporter in 6.5,
printed p.122; Aschbacher--Smith F.1.1--F.1.3, pp.259--260.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source

private theorem odd_transversal_equiv {H K : Type*} [Group H] [Finite H] [Group K]
    (e : H ≃* K) (T : Sylow 2 H)
    (hh : ∀ R : Sylow 2 K, ∀ g : K,
      ∃ x : K, Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (R : Set K)) (g : H) :
    ∃ x : H, Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (T : Set H) := by
  apply e.toMonoidHom.exists_odd_coset_of_comap e.surjective _
    (normalizer (T.mapSurjective (f := e.toMonoidHom) e.surjective : Set K))
    (T.normalizer_comap_of_central_kernel e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le))
    (hh (T.mapSurjective (f := e.toMonoidHom) e.surjective)) g

private theorem linear_odd_transversal {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 (SL(2,F))) (g : SL(2,F)) :
    ∃ x : SL(2,F), Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (T : Set (SL(2,F))) := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (SL(2,F)) T U
  let f := (MulAut.conj a).toMonoidHom
  have hmap : T.mapSurjective (f := f) (MulAut.conj a).surjective = U := by
    exact ha
  have hn : (Matrix.SpecialLinearGroup.rankOneBorel F).comap f = normalizer (T : Set (SL(2,F))) := by
    have hh := T.normalizer_comap_of_central_kernel f (MulAut.conj a).surjective
      (by rw [f.ker_eq_bot (MulAut.conj a).injective]; exact bot_le)
    rw [hmap] at hh
    exact hh
  apply f.exists_odd_coset_of_comap (MulAut.conj a).surjective _ _ hn ?_ g
  intro b
  by_cases hb : b ∈ Matrix.SpecialLinearGroup.rankOneBorel F
  · exact ⟨1,by simp,by simpa using (Matrix.SpecialLinearGroup.rankOneBorel F).inv_mem hb⟩
  · exact Matrix.SpecialLinearGroup.exists_odd_borel_coset_mover b hb

private theorem standard_psu_odd_transversal {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ x, Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J)
  obtain ⟨ρ,o,R,_,_,_,_,_,_,hN,hreg,_⟩ :=
    Unitary.standard_psu_borel_data J n hn hcard hconj hJ
  let Ω := {l : Projectivization F (Fin 3 → F) // l ∈
    {l | ∃ (v : Fin 3 → F) (hv : v ≠ 0), l = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Ω := MulAction.compHom Ω ρ
  have hti := Sylow.eq_of_inf_ne_bot_of_regular_compl R (o : Ω) hN hreg
  apply T.exists_odd_normalizer_coset_of_ti hti ?_ g
  intro he
  have hh := (Unitary.standard_psu_facts J n hn hcard hconj hJ T).proper
  change normalizer ((T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Set (ProjectiveSpecialUnitaryMatrixGroup J)) < ⊤ at hh
  rw [he] at hh
  exact hh.ne ((⊥ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).normalizer_eq_top)

private theorem psu_odd_transversal {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ x, Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J)
  obtain ⟨C,hC⟩ := Unitary.FormTransport.exists_standard_basis J n hn hcard hconj
  exact odd_transversal_equiv (Unitary.FormTransport.projectiveEquiv J C hC) T
    (standard_psu_odd_transversal (Unitary.FormTransport.standardForm J) n hn hcard hconj rfl) g

/-- Every original source model has odd representatives for its actual Sylow-normalizer cosets,
including degree-one unitary covers, Sz(2), and D10. -/
theorem IsRankOneModel.odd_sylow_normalizer_transversal {H : Type*} [Group H]
    (hm : IsRankOneModel H) (T : Sylow 2 H) (g : H) :
    ∃ x : H, Odd (orderOf x) ∧ g⁻¹*x ∈ normalizer (T : Set H) := by
  let : Finite H := hm.finite
  cases hm with
  | linear n hn he =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
    let eSL : SL(2,F) ≃* PSL(2,F) := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    exact odd_transversal_equiv (e.trans eSL.symm) T linear_odd_transversal g
  | suzuki m he =>
    obtain ⟨e⟩ := he
    apply odd_transversal_equiv e T ?_ g
    intro R b
    cases m with
    | zero => exact R.exists_odd_normalizer_coset_of_solvable suzukiZero_isSolvable b
    | succ m =>
      apply R.exists_odd_normalizer_coset_of_ti (suzuki_sylow_eq_of_inf_ne_bot _ (Nat.succ_pos m)) ?_ b
      intro he
      have hh := (suzuki_rankOneSylowFacts (m+1) R).proper
      change normalizer ((R : Subgroup (SuzukiMatrixGroup (m+1))) : Set (SuzukiMatrixGroup (m+1))) < ⊤ at hh
      rw [he] at hh
      exact hh.ne ((⊥ : Subgroup (SuzukiMatrixGroup (m+1))).normalizer_eq_top)
  | projective_unitary n hn he =>
    obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := he
    exact odd_transversal_equiv e T (psu_odd_transversal J n hn hc hconj) g
  | special_unitary n hn he =>
    obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := he
    apply odd_transversal_equiv e T ?_ g
    intro R b
    let f := Unitary.suProjection J
    exact f.exists_odd_coset_of_comap (Unitary.suProjection_surjective J) _ _
      (R.normalizer_comap_of_central_kernel f (Unitary.suProjection_surjective J)
        (Unitary.suProjection_ker_central J))
      (psu_odd_transversal J n hn hc hconj (R.mapSurjective (Unitary.suProjection_surjective J))) b
  | dihedral he =>
    obtain ⟨e⟩ := he
    apply odd_transversal_equiv e T ?_ g
    exact fun R b => R.exists_odd_normalizer_coset_of_solvable (GLS3.Chapter5.dihedralGroup_isSolvable 5) b
end CFSG.Quasithin.ChapterF.Source
