module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.Identification
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.Centrality
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct

/-!
# The simultaneous Fitting complement

Choose one order-two minimal offender for each distinct cubic factor. Their
plane groups commute, so these offenders generate a two-group T. The
commutators with F(G) generate exactly F=[F(G),J*]. Moreover an element of
F(G) fixed by T centralizes every plane group: each plane group is generated
by its chosen offender and its cubic factor, and the cubic factors are
central in F(G). The remaining generators of J* already centralize F(G).
Thus C_F(G)(T)=C_F(G)(J*), and coprime action gives F(G)=F C_F(G)(J*).

The same decomposition shows [F,T]=F. Apply abelian coprime action to F,
which is central in F(G), to prove the intersection is trivial. All subgroup
relations retain their original embeddings in G. These are the generation
and disjointness inputs for the parent's inclusion-compatible product map.

Source: Aschbacher–Smith, B.1.9(2), printed pp.71–72 (PDF pp.82–83).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- One offender from each cubic plane gives a two-group with the full
Fitting commutator and the same fixed subgroup in F(G) as J*. -/
private theorem exists_fitting_two_actor
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧
      ⁅fittingSubgroup G, T⁆ = fittingMoved ρ ∧
      fittingSubgroup G ⊓ centralizer (T : Set G) =
        fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G) := by
  classical
  have hchoice : ∀ i : Fin (cubicCount ρ), ∃ A, IsMinimalBestOffender ρ A ∧
      ⁅fittingSubgroup G, A⁆ ≠ ⊥ ∧ cubicFactor ρ i = ⁅fittingSubgroup G, A⁆ :=
    fun i => cubicFactor_mem ρ i
  choose A hA hn hX using hchoice
  have hfamily (i) : A i ∈ planeOffenders ρ (cubicFactor ρ i) :=
    ⟨hA i, hn i, (hX i).symm⟩
  have hcard (i) : Nat.card (A i) = 2 := by
    obtain ⟨d⟩ := hlocal (A i) (hA i) (hn i)
    exact d.actor_card
  have htwo (i) : IsPGroup 2 (A i) := IsPGroup.of_card (n := 1) (by simpa using hcard i)
  have hnorm (i j) : A i ≤ normalizer (A j : Set G) := by
    by_cases hij : i = j
    · subst j
      exact (A i).le_normalizer
    · exact ((offender_le_planeGroup ρ (hfamily i)).trans
        ((planeGroups_commute ρ hρ hlocal (cubicFactor_mem ρ i)
          (cubicFactor_mem ρ j) (fun he => hij (cubicFactor_injective ρ he))).trans
          (centralizer_le (offender_le_planeGroup ρ (hfamily j))))).trans
        (centralizer_le_normalizer _)
  let T := ⨆ i, A i
  have hT : IsPGroup 2 T := Theory.GroupTheory.isPGroup_iSup_of_normalizes A htwo hnorm
  have hTJ : T ≤ minimalGenerated ρ := iSup_le fun i => minimal_le ρ (hA i)
  have hcomm : ⁅fittingSubgroup G, T⁆ = fittingMoved ρ := by
    dsimp only [T]
    rw [commutator_iSup_of_normal_left]
    simp_rw [← hX]
    exact cubicFactor_iSup ρ
  refine ⟨T, hT, hcomm, le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hTJ))⟩
  let D := fittingSubgroup G ⊓ centralizer (T : Set G)
  have hDF : D ≤ fittingSubgroup G := inf_le_left
  have hDT : D ≤ centralizer (T : Set G) := inf_le_right
  have hDJ : D ≤ centralizer (minimalGenerated ρ : Set G) := by
    apply le_centralizer_iff.mpr
    rw [minimalGenerated_eq_planeGroups_sup]
    refine sup_le (iSup_le fun i => ?_) ?_
    · rw [planeGroup_eq_local ρ hρ hlocal (hfamily i)]
      refine sup_le ?_ ?_
      · exact ((cubicFactor_le ρ i).trans
          (fittingMoved_le_centralizer_fitting ρ hcore hlocal)).trans (centralizer_le hDF)
      · exact (le_iSup A i).trans (le_centralizer_iff.mp hDT)
    · exact (iSup_le fun B => iSup_le fun hB => hB.2).trans (centralizer_le hDF)
  exact le_inf hDF hDJ

/-- Coprime action of the selected two-group gives generation. Its moved
subgroup is central in F(G), so abelian coprime action gives disjointness. -/
private theorem fitting_complement
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    fittingSubgroup G = fittingMoved ρ ⊔
      (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) ∧
    Disjoint (fittingMoved ρ)
      (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) := by
  obtain ⟨T, hT, hcomm, hfix⟩ := exists_fitting_two_actor ρ hρ hcore hlocal
  have hcop : Nat.Coprime (Nat.card T) (Nat.card (fittingSubgroup G)) := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rw [hn]
    exact (fitting_odd_of_twoCore_eq_bot hcore).coprime_two_left.pow_left n
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime
    (fittingSubgroup G) T le_normalizer_of_normal inferInstance hcop
  rw [hcomm] at hsplit
  refine ⟨by simpa only [hfix] using hsplit, ?_⟩
  have hiter : ⁅fittingMoved ρ, T⁆ = fittingMoved ρ := by
    apply le_antisymm (commutator_le_left _ _)
    rw [← hcomm]
    apply commutator_le.mpr
    intro x hx t ht
    have hx' : x ∈ fittingMoved ρ ⊔ (fittingSubgroup G ⊓ centralizer (T : Set G)) :=
      hsplit ▸ hx
    obtain ⟨m, hm, c, hc, rfl⟩ := mem_sup_of_normal_left.mp hx'
    have hct : ⁅c, t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centralizer_iff.mp hc.2 t ht).symm)
    rw [commutatorElement_mul_left_eq_conj_mul, hct, mul_one, mul_inv_cancel, one_mul]
    rw [hcomm]
    exact commutator_mem_commutator hm ht
  have hMF : fittingMoved ρ ≤ fittingSubgroup G := (fittingMoved_le ρ).trans inf_le_left
  have habel : IsMulCommutative (fittingMoved ρ) :=
    le_centralizer_iff_isMulCommutative.mp
      ((fittingMoved_le_centralizer_fitting ρ hcore hlocal).trans (centralizer_le hMF))
  let := habel
  have hdis := commutator_disjoint_centralizer_of_coprime (fittingMoved ρ) T
    le_normalizer_of_normal (hcop.of_dvd_right (card_dvd_of_le hMF))
  rw [hiter] at hdis
  apply disjoint_def.mpr
  intro x hx hc
  have hcT : x ∈ fittingSubgroup G ⊓ centralizer (T : Set G) := hfix.symm ▸ hc
  exact hdis.le_bot ⟨hx, hx, hcT.2⟩

/-- The simultaneous generation assertion in B.1.9(2), using the literal
centralizer of all minimal best offenders in the original Fitting subgroup. -/
theorem fitting_eq_fittingMoved_sup_centralizer
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    fittingSubgroup G = fittingMoved ρ ⊔
      (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) :=
  (fitting_complement ρ hρ hcore hlocal).1

/-- The two factors of the simultaneous Fitting decomposition intersect
trivially, as subgroups of the original ambient group. -/
theorem fittingMoved_disjoint_fitting_centralizer
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    Disjoint (fittingMoved ρ)
      (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) :=
  (fitting_complement ρ hρ hcore hlocal).2

end CFSG.Quasithin.ChapterB.FittingStructure
