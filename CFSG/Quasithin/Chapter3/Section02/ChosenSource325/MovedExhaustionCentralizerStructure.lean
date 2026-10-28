module
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# A moved subgroup in the component centralizer

Let K be a normal quasisimple subgroup and suppose O₂(H) = 1. A two-subgroup
B of C_H(K) acts faithfully on the embedded F*(C_H(K)). If B is nontrivial
and normal in A, it therefore moves an odd-prime core or an ordinary component
of that centralizer. In the former case coprime action constructs X = [O_p(C),B].
In the latter, take the actual A-orbit of the moved component. Both constructions
give A-invariant X ≤ C_H(K) with X = [X,B] and X nontrivial.

The prime restriction for a starred cubic actor is in
`MovedExhaustionCentralizerPrime`; the actual chosen-seed application is
`SeedAlternativesMovedExhaustionCentralizerStructure`. These are the structural
selection steps of D.3.9(2), not its later prime and component exclusions.
Those exclusions and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith, D.3.9(2), printed pp.200--201, used in D.3.13--18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem normalizes_commutator
    (A P B : Subgroup H) (hAP : A ≤ normalizer (P : Set H))
    (hAB : A ≤ normalizer (B : Set H)) :
    A ≤ normalizer (⁅P,B⁆ : Subgroup H) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hAP ha),
    mem_normalizer_iff_map_conj_eq.mp (hAB ha)]

private theorem coprime_commutator_idempotent
    (P B : Subgroup H) (hn : B ≤ normalizer (P : Set H))
    (hsolv : Group.IsSolvable P) (hc : Nat.Coprime (Nat.card B) (Nat.card P)) :
    ⁅⁅P,B⁆,B⁆ = ⁅P,B⁆ := by
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right P B)
  let _ : Normalizes B P := ⟨hn⟩
  have hi := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := P) (A := B) hsolv hc
  have hm := commutatorAction_subgroup_conj_map_eq_commutator P B hn
  have hh : (commutatorAction₂ (A := B) (G := P)).map P.subtype ≤ ⁅⁅P,B⁆,B⁆ := by
    rw [commutatorAction₂,commutatorSubgroup,MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨p,⟨b,a,ha,rfl⟩,rfl⟩
    have haM : (a : H) ∈ ⁅P,B⁆ := by
      rw [←hm]
      exact mem_map_of_mem P.subtype ha
    have hh := commutator_mem_commutator ((⁅P,B⁆).inv_mem haM) b.property
    change (a : H)⁻¹ * ((b : H) * (a : H) * (b : H)⁻¹) ∈ (⁅⁅P,B⁆,B⁆ : Subgroup H)
    simpa only [commutatorElement_def,inv_inv,
      conjMulDistribMulActionOfLeNormalizer_smul_coe,mul_assoc] using hh
  rwa [hi,hm] at hh

/-- A two-subgroup of the component centralizer acts faithfully on its
embedded generalized Fitting subgroup when the ambient two-core is trivial. -/
theorem component_centralizer_twoSubgroup_fitting_kernel
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥) (B : Subgroup H) (hB : IsPGroup 2 B)
    (hBC : B ≤ centralizer (K : Set H)) :
    B ⊓ centralizer ((generalizedFitting (centralizer (K : Set H))).map
      (centralizer (K : Set H)).subtype : Set H) = ⊥ := by
  let C := centralizer (K : Set H)
  let F := (generalizedFitting C).map C.subtype
  let D := B ⊓ centralizer (F : Set H)
  have hd : D ≤ centralizer (generalizedFitting H : Set H) := by
    apply le_centralizer_iff.mpr
    rw [generalizedFitting_eq_normal_component_sup_centralizer K]
    exact sup_le (le_centralizer_iff.mp (inf_le_left.trans hBC))
      (le_centralizer_iff.mp inf_le_right)
  have hp : D ≤ pCore 2 H := le_pCore_of_le_fitting D (hB.to_le inf_le_left)
    (hd.trans centralizer_generalizedFitting_le_fitting)
  exact bot_unique (hp.trans hcore.le)

omit [Finite H] in
/-- Moving one component by a normal subgroup B of A moves its entire
A-orbit by B. Relative normalization, rather than ambient normality of the
selected component, suffices. -/
theorem component_orbit_moved_by_normal_actor
    (J A B : Subgroup H) (hJ : IsComponent H J)
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set H)) (hm : ⁅J,B⁆ ≠ ⊥) :
    ⁅componentOrbit J A,B⁆ = componentOrbit J A := by
  have hJB : J ≤ ⁅J,B⁆ := by
    rcases hJ.commutator_dichotomy B with hz | he
    · exact (hm hz).elim
    · exact he.symm ▸ le_componentOrbit J B
  have hn := le_normalizer_componentOrbit J A
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (hBA.trans hn))
  exact iSup_conjugates_le_of_le_normalizer J A _
    (hJB.trans (commutator_mono (le_componentOrbit J A) le_rfl))
    (normalizes_commutator A (componentOrbit J A) B hn hAB)

/-- A nontrivial two-subgroup B in the centralizer produces an actual
A-invariant subgroup X = [X,B]. The alternatives retain a normal odd-prime
core or a literal A-orbit of an ordinary component. The later cubic/model
argument must reduce the odd prime to three and exclude Suzuki components. -/
theorem exists_moved_subgroup_in_component_centralizer
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hcore : pCore 2 H = ⊥)
    (A B : Subgroup H) (hB : IsPGroup 2 B) (hBn : B ≠ ⊥)
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set H))
    (hBC : B ≤ centralizer (K : Set H)) :
    ∃ X : Subgroup H, X ≤ centralizer (K : Set H) ∧
      A ≤ normalizer (X : Set H) ∧ X ≠ ⊥ ∧ ⁅X,B⁆ = X ∧
      ((∃ p : ℕ, p.Prime ∧ Odd p ∧
          X ≤ (pCore p (centralizer (K : Set H))).map (centralizer (K : Set H)).subtype ∧
          IsPGroup p X) ∨
        ∃ J : Subgroup H, IsComponent H J ∧ J ≤ centralizer (K : Set H) ∧
          X = componentOrbit J A) := by
  classical
  let C := centralizer (K : Set H)
  have hK : IsComponent H K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hCcore : pCore 2 C = ⊥ := hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2 hcore
  by_cases hF : (fittingSubgroup C).map C.subtype ≤ centralizer (B : Set H)
  · obtain hm | ⟨J,hJ,hJH,hm⟩ :=
      moves_normal_component_or_centralizer_component K B hB hBn hcore hF
    · exact (hm (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp hBC))).elim
    let J' := J.map C.subtype
    let X := componentOrbit J' A
    have hJC : J' ≤ C := map_subtype_le J
    have hXC : X ≤ C := iSup_conjugates_le_of_le_normalizer J' A C hJC
      (by rw [normalizer_eq_top]; exact le_top)
    refine ⟨X,hXC,le_normalizer_componentOrbit J' A,?_,
      component_orbit_moved_by_normal_actor J' A B hJH hBA hAB hm,
      Or.inr ⟨J',hJH,hJC,rfl⟩⟩
    intro hz
    exact hJH.isCComponent.ne_bot (bot_unique ((le_componentOrbit J' A).trans hz.le))
  · have hex : ∃ p : ℕ, p.Prime ∧
        ¬ (pCore p C).map C.subtype ≤ centralizer (B : Set H) := by
      by_contra! hn
      apply hF
      rw [fitting_eq_sup_pCore,Subgroup.map_iSup]
      apply iSup_le
      intro p
      exact hn p.val.val (Nat.prime_of_mem_primeFactors p.val.property)
    obtain ⟨p,hp,hm⟩ := hex
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      apply hm
      rw [he,hCcore,Subgroup.map_bot]
      exact bot_le
    let P := (pCore p C).map C.subtype
    let X := ⁅P,B⁆
    let : P.Normal := inferInstance
    have hXP : X ≤ P := commutator_le_left _ _
    have hP : IsPGroup p P := pCore_isPGroup.map C.subtype
    have hXn : X ≠ ⊥ := fun he => hm (commutator_eq_bot_iff_le_centralizer.mp he)
    refine ⟨X,hXP.trans (map_subtype_le _),
      normalizes_commutator A P B (by rw [normalizer_eq_top]; exact le_top) hAB,
      hXn,?_,Or.inl ⟨p,hp,hp.odd_of_ne_two hp2,hXP,hP.to_le hXP⟩⟩
    exact coprime_commutator_idempotent P B
      (by rw [normalizer_eq_top]; exact le_top)
      (@IsNilpotent.to_isSolvable _ _ hP.isNilpotent)
      (IsPGroup.coprime_card_of_ne 2 p hp2.symm B P hB hP)


end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
