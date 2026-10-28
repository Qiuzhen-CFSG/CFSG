module

public import CFSG.Quasithin.ChapterE.Section04.MathieuM22
public import CFSG.Quasithin.ChapterE.Section04.MathieuM24
public import CFSG.Quasithin.ChapterE.Section04.MathieuModules
public import Theory.Mathieu.M24.TwoLocalExtensions
public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.TailMaximal
public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.PrimeFactor
public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.QuasisimpleFactor.OuterSylow

/-!
# Mathieu module bounds from the actual small local quotients

For a generating family of Sylow overgroups with intrinsic two-core quotients
S₃ or S₅, the proved local invariance branches give the rank-budget bound.
The S₃ branch uses the prime-order generalized Fitting subgroup. In S₅ that
subgroup is A₅, and its index two proves the outer quotient is a two-group;
the local quotient isomorphism transports this fact to the actual overgroup.
No normality assertion for arbitrary outer Sylow subgroups is used.

The genuine M₂₂ pair, including odd central covers and outer extensions, has
rank costs two and one. The M₂₄ triple has rank cost at most one per member.
We retain their quotient isomorphisms throughout the argument and count the
finite families with repetitions removed. Generation by F*(G) and the Sylow
subgroup converts the strict fixed-space inequality into the noncentralization
hypothesis of the rank-budget theorem. This proves all of E.4.3(2).

For E.4.3(3), simplicity and the composite order of the native M₂₄ identify
its generalized Fitting subgroup and central quotient. The proved faithfulness
and strict Sylow fixed-space inequalities apply (2) to the actual code and
cocode. Restriction along the genuine M₂₃ point-stabilizer embedding, followed
by an intertwining linear equivalence, gives both source module bounds.

As in the source proof and application, the local condition concerns
F*(H/O₂(H)); the printed E.4.2 statement instead writes F*(H)/O₂(H).
This module proves the needed small-quotient specialization and E.4.3(2–3),
independently of the remaining general E.4.2 branches and the M₁₂ case.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2–3,
printed pp.241–242 (PDF pp.252–253); code and cocode definitions in H.13.1,
printed p.395.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound
namespace CFSG.Quasithin.ChapterE.ValueBound.MathieuBounds
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem symmetricFive_fitting_quotient_isTwoGroup :
    IsPGroup 2 ((Equiv.Perm (Fin 5)) ⧸ generalizedFitting (Equiv.Perm (Fin 5))) := by
  have h : IsPGroup 2 ((Equiv.Perm (Fin 5)) ⧸ alternatingGroup (Fin 5)) := by
    apply IsPGroup.of_card (n := 1)
    change (alternatingGroup (Fin 5)).index = 2
    exact alternatingGroup.index_eq_two
  exact h.of_equiv (QuotientGroup.quotientMulEquivOfEq
    SmallQuotients.symmetricFive_generalizedFitting_eq_alternating).symm

private theorem eventual_invariance_of_symmetric_quotient
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)))
    {k j : ℕ} (hmk : j + primeRank 2 (H ⧸ pCore 2 H) ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G)) :
    ∀ n, j + primeRank 2 (H ⧸ pCore 2 H) ≤ n →
      H ≤ subspaceStabilizer ρ
        (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    apply LocalControl.eventual_invariance_of_prime_generalizedFitting ρ T H hTH hmk _ hn
    rw [Nat.card_congr (generalizedFittingEquiv e).toEquiv]
    exact SmallQuotients.symmetricThree_generalizedFitting_card_prime
  · obtain ⟨e⟩ := he
    let : IsQuasisimple (generalizedFitting (Equiv.Perm (Fin 5))) :=
      SmallQuotients.symmetricFive_generalizedFitting_isQuasisimple
    let : IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H)) :=
      IsQuasisimple.of_mulEquiv (generalizedFittingEquiv e).symm
    apply LocalControl.eventual_invariance_of_quasisimple_two_quotient
      ρ T H hTH le_rfl hmk hn
    exact symmetricFive_fitting_quotient_isTwoGroup.of_equiv
      (QuotientGroup.congr _ _ e (map_generalizedFitting e)).symm

/-- The adequate E.4.2 bound for a generating family with actual S₃ or S₅ local quotients. -/
theorem moduleA_le_of_symmetric_quotients
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hL : IsQuasisimple (generalizedFitting G))
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ (T : Subgroup G))
    (Δ : Finset (Subgroup G))
    (hT : ∀ H ∈ Δ, (T : Subgroup G) ≤ H)
    (hΔgen : sSup (Δ : Set (Subgroup G)) = ⊤)
    (hquot : ∀ H ∈ Δ,
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    moduleA ρ ≤ (localRankBudget Δ : ℕ∞) := by
  let : IsQuasisimple (generalizedFitting G) := hL
  have hΔ : IsGeneratingFamily T Δ := by
    refine ⟨hT, hΔgen, ?_⟩
    intro H hH
    rcases hquot H hH with he | he
    · obtain ⟨e⟩ := he
      exact MathieuM22.isLocalOvergroup_of_quotientEquiv H e
        (Or.inr SmallQuotients.symmetricThree_generalizedFitting_card_prime)
    · obtain ⟨e⟩ := he
      exact MathieuM22.isLocalOvergroup_of_quotientEquiv H e
        (Or.inl SmallQuotients.symmetricFive_generalizedFitting_isQuasisimple)
  apply LocalControl.moduleA_le_of_local_eventual_invariance ρ T
    (generalizedFitting G) hcore hgen
    (fixedSpace_sylow_not_le_component ρ hgen hfixed) Δ hΔ
  intro j H hH hm hn
  exact eventual_invariance_of_symmetric_quotient ρ T H (hT H hH) (hquot H hH) hm hn

/-- E.4.3(2) for the M₂₂ central quotient, including odd covers and outer extensions. -/
theorem moduleA_le_three_of_m22
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (_hρ : Function.Injective ρ) (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22)
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ (T : Subgroup G)) :
    moduleA ρ ≤ 3 := by
  classical
  obtain ⟨P⟩ := MathieuM22.nonempty_parabolicPair hcore hL e T
  let Δ : Finset (Subgroup G) := {P.first, P.second}
  have hT : ∀ H ∈ Δ, (T : Subgroup G) ≤ H := by
    intro H hH
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact P.sylow_le_first
    · exact P.sylow_le_second
  have hgen : sSup (Δ : Set (Subgroup G)) = ⊤ := by
    simpa only [Δ, Finset.coe_insert, Finset.coe_singleton, sSup_pair] using P.generate
  have hquot : ∀ H ∈ Δ,
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
    intro H hH
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact Or.inr ⟨P.firstQuotient⟩
    · exact Or.inl ⟨P.secondQuotient⟩
  have hbudget : localRankBudget Δ ≤ 3 := by
    have h₁ : primeRank 2 (P.first ⧸ pCore 2 P.first) ≤ 2 :=
      (primeRank_equiv 2 P.firstQuotient).le.trans SmallQuotients.symmetricFive_primeRank_le_two
    have h₂ : primeRank 2 (P.second ⧸ pCore 2 P.second) ≤ 1 :=
      (primeRank_equiv 2 P.secondQuotient).le.trans SmallQuotients.symmetricThree_primeRank_le_one
    by_cases he : P.first = P.second
    · simp only [Δ, he, Finset.insert_eq_of_mem (Finset.mem_singleton_self P.second),
        localRankBudget, Finset.sum_singleton]
      omega
    · simpa only [Δ, localRankBudget, Finset.sum_pair he] using Nat.add_le_add h₁ h₂
  exact (moduleA_le_of_symmetric_quotients ρ T hcore hL
    (MathieuM22.fitting_sup_sylow hL e T) hfixed Δ hT hgen hquot).trans (by exact_mod_cast hbudget)

/-- E.4.3(2) for the actual M₂₄ central quotient. -/
theorem moduleA_le_three_of_m24
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (_hρ : Function.Injective ρ) (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M24)
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ (T : Subgroup G)) :
    moduleA ρ ≤ 3 := by
  classical
  obtain ⟨P, hT, hgen, _, hquot⟩ := m24_sylow_overgroups hcore hL e T
  let Δ := Finset.univ.image P
  have hΔT : ∀ H ∈ Δ, (T : Subgroup G) ≤ H := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact hT i
  have hΔgen : sSup (Δ : Set (Subgroup G)) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact iSup_le fun i => le_sSup (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hΔquot : ∀ H ∈ Δ,
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
    intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact Or.inl (hquot i)
  have hbudget : localRankBudget Δ ≤ 3 := by
    have hrank : ∀ H ∈ Δ, primeRank 2 (H ⧸ pCore 2 H) ≤ 1 := by
      intro H hH
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
      exact (primeRank_equiv 2 (hquot i).some).le.trans
        SmallQuotients.symmetricThree_primeRank_le_one
    calc
      localRankBudget Δ ≤ ∑ H ∈ Δ, 1 := Finset.sum_le_sum hrank
      _ = Δ.card := by simp
      _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_image_le
      _ = 3 := by simp
  exact (moduleA_le_of_symmetric_quotients ρ T hcore hL
    (m24_component_sup_sylow hL e T) hfixed Δ hΔT hΔgen hΔquot).trans (by exact_mod_cast hbudget)

/-- E.4.3(2), with both genuine central-quotient alternatives. -/
theorem moduleA_le_three_of_m22_or_m24
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (hρ : Function.Injective ρ) (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hL : IsQuasisimple (generalizedFitting G))
    (he : Nonempty ((generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22) ∨
      Nonempty ((generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M24))
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ (T : Subgroup G)) :
    moduleA ρ ≤ 3 := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact moduleA_le_three_of_m22 ρ hρ T hcore hL e hfixed
  · obtain ⟨e⟩ := he
    exact moduleA_le_three_of_m24 ρ hρ T hcore hL e hfixed

private theorem native_m24_center : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  let := Group.commGroupOfCenterEqTop h
  have hp := IsSimpleGroup.prime_card (α := M24)
  rw [m24_order] at hp
  norm_num at hp

private theorem native_m24_quasisimple : IsQuasisimple M24 := by
  let := m24_isSimpleGroup
  let : Group.IsPerfect M24 := by
    constructor
    rcases (inferInstance : (_root_.commutator M24).Normal).eq_bot_or_eq_top with hb | ht
    · have hc := (commutator_eq_bot_iff_center_eq_top M24).mp hb
      rw [native_m24_center] at hc
      exact (bot_ne_top hc).elim
    · exact ht
  exact ⟨((QuotientGroup.quotientMulEquivOfEq native_m24_center).trans
    (QuotientGroup.quotientBot (G := M24))).isSimpleGroup⟩

private theorem native_m24_fitting_eq_top : generalizedFitting M24 = ⊤ := by
  let : IsQuasisimple M24 := native_m24_quasisimple
  let : IsQuasisimple (⊤ : Subgroup M24) := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  exact top_unique (component_le_generalizedFitting M24 ⊤
    ⟨(inferInstance : (⊤ : Subgroup M24).Normal).isSubnormal, inferInstance⟩)

private noncomputable def native_m24_fitting_equiv : generalizedFitting M24 ≃* M24 :=
  (MulEquiv.subgroupCongr native_m24_fitting_eq_top).trans Subgroup.topEquiv

private theorem native_m24_fitting_center : center (generalizedFitting M24) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hm : native_m24_fitting_equiv x ∈ center M24 :=
    (Subgroup.centerCongr native_m24_fitting_equiv ⟨x, hx⟩).property
  rw [native_m24_center, mem_bot] at hm
  exact native_m24_fitting_equiv.injective (hm.trans (map_one _).symm)

private noncomputable def native_m24_central_quotient :
    (generalizedFitting M24) ⧸ center (generalizedFitting M24) ≃* M24 :=
  ((QuotientGroup.quotientMulEquivOfEq native_m24_fitting_center).trans
    QuotientGroup.quotientBot).trans native_m24_fitting_equiv

/-- The bound for the native eleven-dimensional M₂₄ code, with all inputs discharged. -/
theorem moduleA_m24Code_le_three : moduleA MathieuCode.codeRepresentation ≤ 3 := by
  let : IsQuasisimple M24 := native_m24_quasisimple
  let T : Sylow 2 M24 := Classical.choice inferInstance
  exact moduleA_le_three_of_m24 MathieuCode.codeRepresentation MathieuCode.code_faithful T
    m24_twoCore (IsQuasisimple.of_mulEquiv (G := M24)
      (H := generalizedFitting M24) native_m24_fitting_equiv.symm)
    native_m24_central_quotient (MathieuCode.code_fixedSpace_lt_sylow T)

/-- The bound for the native eleven-dimensional M₂₄ cocode, with all inputs discharged. -/
theorem moduleA_m24Cocode_le_three : moduleA MathieuCode.cocodeRepresentation ≤ 3 := by
  let : IsQuasisimple M24 := native_m24_quasisimple
  let T : Sylow 2 M24 := Classical.choice inferInstance
  exact moduleA_le_three_of_m24 MathieuCode.cocodeRepresentation MathieuCode.cocode_faithful T
    m24_twoCore (IsQuasisimple.of_mulEquiv (G := M24)
      (H := generalizedFitting M24) native_m24_fitting_equiv.symm)
    native_m24_central_quotient (MathieuCode.cocode_fixedSpace_lt_sylow T)

omit [Finite G] in
/-- E.4.3(3) for any representation genuinely isomorphic to the M₂₃ code. -/
theorem moduleA_le_three_of_isM23Code (ρ : Representation (ZMod 2) G V)
    (h : MathieuCode.IsM23Code ρ) : moduleA ρ ≤ 3 :=
  (moduleA_le_m24Code_of_isM23Code ρ h).trans moduleA_m24Code_le_three

omit [Finite G] in
/-- E.4.3(3) for any representation genuinely isomorphic to the M₂₃ cocode. -/
theorem moduleA_le_three_of_isM23Cocode (ρ : Representation (ZMod 2) G V)
    (h : MathieuCode.IsM23Cocode ρ) : moduleA ρ ≤ 3 :=
  (moduleA_le_m24Cocode_of_isM23Cocode ρ h).trans moduleA_m24Cocode_le_three

omit [Finite G] in
/-- E.4.3(3), with the source code or cocode alternative and no numerical premise. -/
theorem moduleA_le_three_of_isM23Code_or_isM23Cocode
    (ρ : Representation (ZMod 2) G V)
    (h : MathieuCode.IsM23Code ρ ∨ MathieuCode.IsM23Cocode ρ) : moduleA ρ ≤ 3 := by
  rcases h with h | h
  · exact moduleA_le_three_of_isM23Code ρ h
  · exact moduleA_le_three_of_isM23Cocode ρ h

/-- The actual code representation restricted along the native point stabilizer. -/
theorem moduleA_m23Code_le_three : moduleA MathieuCode.m23CodeRepresentation ≤ 3 :=
  moduleA_m23Code_le.trans moduleA_m24Code_le_three

/-- The actual cocode representation restricted along the native point stabilizer. -/
theorem moduleA_m23Cocode_le_three : moduleA MathieuCode.m23CocodeRepresentation ≤ 3 :=
  moduleA_m23Cocode_le.trans moduleA_m24Cocode_le_three

end CFSG.Quasithin.ChapterE.ValueBound.MathieuBounds
