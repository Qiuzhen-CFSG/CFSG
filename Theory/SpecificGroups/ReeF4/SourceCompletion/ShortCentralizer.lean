module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortRoot
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LongCentralizer
public import Theory.SpecificGroups.ReeF4.ParabolicSubgroupCores
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Short-root centralizer placement in the general Ree group

The actual PSL₂ subgroup centralizing the fourth root curve survives under
conjugation. Its perfectness puts it in the full centralizer's solvable
residual, whose order is therefore divisible by three. Borel–Tits normalizer
coverage places a conjugate centralizer in a full parabolic; the three-free
Suzuki parabolic is excluded. The central involution lies in the two-core of
its nonsolvable centralizer, hence in the specified linear root radical.

This proves the native placement used in F.4.27(4)(ii), at every m > 0,
including q = 8. No ambient recognition or involution exhaustion is assumed.
Source: Aschbacher–Smith, printed pp.288,295 (`refs/quasithin.pdf`);
GLS3 Theorem 3.1.3 and §§2.3,2.6 (`refs/KGroup/GLS3/chapter3.tex`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.SourceCompletion
open Parabolics LargeLocalSeeds EvenInvolutionGeometry
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

private theorem linear_three (m : ℕ) : 3 ∣ Nat.card (LinearQuotient m) :=
  (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := CoefficientField m) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans
      (card_subgroup_dvd_card _)

private theorem centralizer_cover {m : ℕ} (hm : 0 < m)
    (x : Model m) (hx : orderOf x = 2) :
    ∃ (g : Model m) (s : Side),
      centralizer ({(MulAut.conj g) x} : Set (Model m)) ≤ parabolic m s := by
  have hne : zpowers x ≠ ⊥ := by
    intro h
    have he := zpowers_eq_bot.mp h
    simp [he] at hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨g,s,hg⟩ := ConverseParabolics.normalizer_cover hm (zpowers x) hne hp
  have hCN : centralizer ({x} : Set (Model m)) ≤ normalizer (zpowers x : Set (Model m)) := by
    rw [←centralizer_closure ({x} : Set (Model m)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  refine ⟨g,s,?_⟩
  rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g),←parabolic_eq_rootParabolic]
  exact (map_mono hCN).trans hg

private theorem involution_mem_centralizer_core {X : Type*} [Group X] [Finite X]
    (x : X) (hx : orderOf x = 2) : x ∈ (centralizer ({x} : Set X)).pCoreIn 2 := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  have hC : zpowers x ≤ centralizer ({x} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hn : centralizer ({x} : Set X) ≤ normalizer (zpowers x : Set X) := by
    rw [←centralizer_closure ({x} : Set X),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  exact le_pCoreIn_of_normalizes hp hC hn (mem_zpowers x)

/-- Every native short-root involution centralizes an actual PSL₂ subgroup. -/
theorem short_centralizer_embedding {m : ℕ} (hm : 0 < m)
    {t : Model m} (ht : IsShortRootInvolution t) :
    ∃ f : LinearQuotient m →* centralizer ({t} : Set (Model m)),
      Function.Injective f := by
  obtain ⟨a,ha,hconj⟩ := ht
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  obtain ⟨f,hf,hfc⟩ := short_root_linear_centralizer_embedding hm a
  let j : LinearQuotient m →* Model m := (MulAut.conj g).toMonoidHom.comp
    ((parabolic m .linear).subtype.comp f)
  have hj : Function.Injective j := (MulAut.conj g).injective.comp
    ((parabolic m .linear).subtype_injective.comp hf)
  have hjC (y : LinearQuotient m) : j y ∈ centralizer ({t} : Set (Model m)) := by
    have hc := (hfc y).map (MulAut.conj g).toMonoidHom
    change Commute (j y) (g * shortRootElement m a * g⁻¹) at hc
    rw [hg] at hc
    exact mem_centralizer_singleton_iff.mpr hc.eq
  exact ⟨j.codRestrict _ hjC,(MonoidHom.injective_codRestrict _ _ _).mpr hj⟩

/-- The full native short-root centralizer has nonsolvable perfect residual. -/
theorem short_centralizer_not_solvable {m : ℕ} (hm : 0 < m)
    {t : Model m} (ht : IsShortRootInvolution t) :
    ¬ Group.IsSolvable (centralizer ({t} : Set (Model m))) := by
  obtain ⟨f,hf⟩ := short_centralizer_embedding hm ht
  intro hc
  let := hc
  let := linearQuotient_simple m hm
  let := linearQuotient_perfect m hm
  exact Group.IsPerfect.not_isSolvable (LinearQuotient m)
    (Group.isSolvable_of_isSolvable_injective hf)

/-- Three divides the solvable residual, rather than merely an outer torus. -/
theorem short_centralizer_residual_three_dvd {m : ℕ} (hm : 0 < m)
    {t : Model m} (ht : IsShortRootInvolution t) :
    3 ∣ Nat.card (solvableResidual (centralizer ({t} : Set (Model m)))) := by
  obtain ⟨f,hf⟩ := short_centralizer_embedding hm ht
  let := linearQuotient_perfect m hm
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hle := le_solvableResidual_of_isPerfect f.range
  let j := f.codRestrict _ (fun x => hle ⟨x,rfl⟩)
  exact (linear_three m).trans (card_dvd_of_injective j
    ((MonoidHom.injective_codRestrict _ _ _).mpr hf))

/-- Full centralizer containment places the short involution in the literal root radical. -/
theorem short_mem_radical_of_centralizer_le {m : ℕ} (hm : 0 < m)
    {t : Model m} (ht : IsShortRootInvolution t)
    (hC : centralizer ({t} : Set (Model m)) ≤ parabolic m .linear) :
    t ∈ radical m .linear :=
  ParabolicSubgroupCores.pCoreIn_le_radical hm .linear _ hC
    (short_centralizer_not_solvable hm ht)
    (involution_mem_centralizer_core t (orderOf_of_isShortRootInvolution ht))

/-- A short-root involution has a representative in the linear radical whose entire native centralizer lies in the linear parabolic. -/
theorem short_centralizer_placement {m : ℕ} (hm : 0 < m)
    (a : CoefficientField m) (ha : a ≠ 0) :
    ∃ t : Model m, IsConj (shortRootElement m a) t ∧ orderOf t = 2 ∧
      t ∈ radical m .linear ∧
      centralizer ({t} : Set (Model m)) ≤ parabolic m .linear := by
  obtain ⟨g,s,hC⟩ := centralizer_cover hm _ (shortRootElement_orderOf m ha)
  let t := (MulAut.conj g) (shortRootElement m a)
  have ht : IsShortRootInvolution t := ⟨a,ha,isConj_iff.mpr ⟨g,rfl⟩⟩
  have h3 : 3 ∣ Nat.card (centralizer ({t} : Set (Model m))) :=
    (short_centralizer_residual_three_dvd hm ht).trans (card_subgroup_dvd_card _)
  have hs : s = .linear := by
    cases s with
    | linear => rfl
    | suzuki =>
      have hh := h3.trans (card_dvd_of_le hC)
      rw [←parabolic_eq_rootParabolic] at hh
      exact (ConverseParabolics.suzuki_parabolic_three_free hm hh).elim
  subst s
  exact ⟨t,isConj_iff.mpr ⟨g,rfl⟩,orderOf_of_isShortRootInvolution ht,
    short_mem_radical_of_centralizer_le hm ht hC,hC⟩

end ReeF4.SourceCompletion
