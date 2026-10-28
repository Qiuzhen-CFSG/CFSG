module

public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.PrescribedPrime
public import CFSG.Quasithin.ChapterG.Section08.G09Extraction
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Residuals
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Dihedral extraction for the fifth observation of G.9.2

Thompson's extraction and its prescribed-prime refinement supply all four
`DihedralExtraction` clauses, conditional only on the universal G.8.2 input.
The ordinary and relative product proofs remain in the G.8 modules, without
requiring this consumer adapter.

For prime selection, a noncentral residual generator has a noncentral Sylow
subgroup in its cyclic subgroup. Nilpotence places that subgroup in the
corresponding core of X. Coprimeness of the generator's order excludes three
and five for the {3,5}-residual. If that residual centralizes the actor, any
noncentral core detected by the three-residual must therefore be the five-core.
If the three-residual centralizes the actor, its Sylow supplement shows that
the action on the three-core is faithful; extraction there gives only cubic
factors. The proof retains the residual definitions and the ambient images of
O_p(X), with no assumption of normality of X in G.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.8.6–8,
printed p.350, and the fifth observation in G.9.2, printed p.352 (combined
manuscript of 1 March 2004).
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem prime_subgroup_le_core (X Y : Subgroup G)
    (hX : Group.IsNilpotent X) {p : ℕ} [Fact p.Prime]
    (hY : IsPGroup p Y) (hYX : Y ≤ X) : Y ≤ (pCore p X).map X.subtype := by
  let _ := hX
  obtain ⟨S, hS⟩ := hY.comap_subtype (K := X) |>.exists_le_sylow
  have hcore : (S : Subgroup X) ≤ pCore p X := le_sSup ⟨inferInstance, S.isPGroup'⟩
  have hm := map_mono (f := X.subtype) (hS.trans hcore)
  change (Y.subgroupOf X).map X.subtype ≤ _ at hm
  rwa [map_subgroupOf_eq_of_le hYX] at hm

private theorem exists_noncentral_core_of_element (A X : Subgroup G)
    (hX : Group.IsNilpotent X) (x : G) (hx : x ∈ X)
    (hnon : x ∉ centralizer (A : Set G)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ orderOf x ∧
      ¬ A ≤ centralizer ((pCore p X).map X.subtype : Set G) := by
  by_contra! h
  apply hnon
  have hZ : zpowers x ≤ centralizer (A : Set G) := by
    rw [← Sylow.iSup_sylow_map_eq_top (N := zpowers x), Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hp => ?_
    let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hpd : p ∣ orderOf x := by
      simpa only [Nat.card_zpowers] using Nat.dvd_of_mem_primeFactors hp
    let S : Subgroup G := (default : Sylow p (zpowers x)).map (zpowers x).subtype
    have hSX : S ≤ X := (map_subtype_le _).trans (zpowers_le.mpr hx)
    have hSP : IsPGroup p S := (default : Sylow p (zpowers x)).isPGroup'.map _
    exact (prime_subgroup_le_core X S hX hSP hSX).trans
      (le_centralizer_iff.mp (h p (Fact.out : p.Prime) hpd))
  exact hZ (mem_zpowers x)


private theorem exists_noncentral_three_generator (A X : Subgroup G)
    (hnon : ⁅threeResidual X, A⁆ ≠ ⊥) :
    ∃ x : G, x ∈ X ∧ Nat.Coprime 3 (orderOf x) ∧
      x ∉ centralizer (A : Set G) := by
  by_contra! h
  apply hnon
  apply commutator_eq_bot_iff_le_centralizer.mpr
  let R := pResidual 3 X
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 3
    ((pResidual_eq_top_iff 3 R).mpr (isPPerfect_pResidual 3))
  have hC : (⊤ : Subgroup R) ≤
      (centralizer (A : Set G)).comap (X.subtype.comp R.subtype) := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact h x.val.val x.val.property (by simpa using hx)
  rintro x ⟨y, hy, rfl⟩
  exact hC (show (⟨y, hy⟩ : R) ∈ ⊤ from trivial)

/-- Noncentrality of the three-residual detects a noncentral prime core
at an odd prime other than three. -/
theorem exists_noncentral_prime_core_of_threeResidual
    (A X : Subgroup G) (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnon : ⁅threeResidual X, A⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≠ 3 ∧
      ¬ A ≤ centralizer ((pCore p X).map X.subtype : Set G) := by
  obtain ⟨x, hx, ho, hxc⟩ := exists_noncentral_three_generator A X hnon
  obtain ⟨p, hp, hd, hn⟩ := exists_noncentral_core_of_element A X hX x hx hxc
  have hord : orderOf x ∣ Nat.card X := by
    simpa using orderOf_dvd_natCard (⟨x, hx⟩ : X)
  refine ⟨p, hp, hodd.of_dvd_nat (hd.trans hord), ?_, hn⟩
  intro he
  subst p
  exact ((Nat.prime_three.coprime_iff_not_dvd).mp ho) hd

/-- The literal {3,5}-residual detects a prime greater than five. -/
theorem exists_large_prime_core_of_threeFiveResidual
    (A X : Subgroup G) (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnon : ⁅threeFiveResidual X, A⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧
      ¬ A ≤ centralizer ((pCore p X).map X.subtype : Set G) := by
  have hex : ∃ x : G, x ∈ X ∧ Nat.Coprime (orderOf x) 15 ∧
      x ∉ centralizer (A : Set G) := by
    by_contra! h
    apply hnon
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (Subgroup.closure_le _).mpr (fun x hx => h x hx.1 hx.2)
  obtain ⟨x, hx, ho, hxc⟩ := hex
  obtain ⟨p, hp, hd, hn⟩ := exists_noncentral_core_of_element A X hX x hx hxc
  have hord : orderOf x ∣ Nat.card X := by
    simpa using orderOf_dvd_natCard (⟨x, hx⟩ : X)
  have hpo : Odd p := hodd.of_dvd_nat (hd.trans hord)
  have hpc : Nat.Coprime p 15 := ho.of_dvd_left hd
  refine ⟨p, hp, ?_, hn⟩
  by_contra hle
  have hlt : p < 6 := by omega
  interval_cases p <;> norm_num at *

omit [Finite G] in
private theorem prime_core_le_threeFiveResidual (X : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    (pCore p X).map X.subtype ≤ threeFiveResidual X := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hc : Nat.Coprime p 15 := by
    have hc3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.ne_one))
    have hc5 : Nat.Coprime p 5 := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      exact hp5 (((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left hp.ne_one))
    exact hc3.mul_right hc5
  rintro x ⟨y, hy, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨y.property, ?_⟩
  have ho := (pCore_isPGroup (p := p) (G := X)).orderOf_coprime hc
    (⟨y, hy⟩ : pCore p X)
  simpa using ho

/-- If only the three-residual is noncentral, the five-core is noncentral. -/
theorem five_core_noncentral_of_residuals
    (A X : Subgroup G) (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hc : ⁅threeFiveResidual X, A⁆ = ⊥) (hn : ⁅threeResidual X, A⁆ ≠ ⊥) :
    ¬ A ≤ centralizer ((pCore 5 X).map X.subtype : Set G) := by
  obtain ⟨p, hp, _, hp3, hnon⟩ :=
    exists_noncentral_prime_core_of_threeResidual A X hX hodd hn
  have hp5 : p = 5 := by
    by_contra h
    exact hnon (le_centralizer_iff.mpr
      ((prime_core_le_threeFiveResidual X hp hp3 h).trans
        (commutator_eq_bot_iff_le_centralizer.mp hc)))
  simpa only [hp5] using hnon

/-- Centralizing the three-residual leaves a faithful action on the three-core. -/
theorem faithful_three_core_of_threeResidual
    (A X : Subgroup G) (hX : Group.IsNilpotent X)
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (hc : ⁅threeResidual X, A⁆ = ⊥) :
    A ⊓ centralizer ((pCore 3 X).map X.subtype : Set G) = ⊥ := by
  let _ := hX
  let S : Sylow 3 X := default
  have hS : (S : Subgroup X) = pCore 3 X :=
    le_antisymm (le_sSup ⟨inferInstance, S.isPGroup'⟩)
      (pCore_isPGroup.le_sylow_of_normal S)
  have hgen := congrArg (fun K : Subgroup X => K.map X.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [hS, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hgen
  apply bot_unique
  intro a ha
  apply hfaith.le
  refine ⟨ha.1, ?_⟩
  have hca : threeResidual X ≤ centralizer ({a} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (((commutator_eq_bot_iff_le_centralizer.mp hc) hx) a ha.1).symm
  have hpa : (pCore 3 X).map X.subtype ≤ centralizer ({a} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (ha.2 x hx)
  have hXa : X ≤ centralizer ({a} : Set G) :=
    hgen ▸ sup_le hca hpa
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hXa hx)

/-- G.8.6 and G.8.8 discharge all four dihedral extraction clauses used
in the fifth observation of G.9.2. The only conditional input is G.8.2. -/
theorem dihedralExtraction_of_faithfulComplement
    (hComplement : FaithfulComplementTheorem G)
    (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) : DihedralExtraction A X n := by
  apply dihedralExtraction_of_products
  · obtain ⟨D, hAD, hDX, _⟩ :=
      dihedral_extraction hComplement A X hA hX hodd hnorm hfaith n hcard
    exact ⟨D, hAD, hDX⟩
  · intro hc
    let Y := (pCore 3 X).map X.subtype
    have hYX : Y ≤ X := map_subtype_le _
    have hY : IsPGroup 3 Y := pCore_isPGroup.map X.subtype
    obtain ⟨D, hAD, hDY, hDp⟩ := dihedral_extraction hComplement A Y hA
      (dihedral_nilpotent_le hX hYX) (hodd.of_dvd_nat (card_dvd_of_le hYX))
      (hnorm.trans (normalizer_le_normalizer_characteristic_image X (pCore 3 X)))
      (faithful_three_core_of_threeResidual A X hX hfaith hc) n hcard
    refine ⟨D, hAD, hDY.trans (sup_le_sup_right hYX A), ?_⟩
    intro i
    obtain ⟨k, hk⟩ := hY.exists_card_eq
    have hd : D.prime i ∣ 3 := (D.prime_isPrime i).dvd_of_dvd_pow (hk ▸ hDp i)
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left (D.prime_isPrime i).ne_one
  · intro hc
    obtain ⟨p, hp, hpl, hnon⟩ :=
      exists_large_prime_core_of_threeFiveResidual A X hX hodd hc
    obtain ⟨hn, D, hAD, hDX, hfirst, _⟩ := lemma_G_8_8_of_faithfulComplement
      hComplement A X hA hX hodd hnorm hfaith p hp hnon n hcard
    exact ⟨D, hAD, hDX, ⟨⟨0, hn⟩, by rwa [hfirst]⟩⟩
  · intro hc hn
    obtain ⟨hn, D, hAD, hDX, hfirst, _⟩ := lemma_G_8_8_of_faithfulComplement
      hComplement A X hA hX hodd hnorm hfaith 5 (by decide)
      (five_core_noncentral_of_residuals A X hX hodd hc hn) n hcard
    exact ⟨D, hAD, hDX, ⟨⟨0, hn⟩, hfirst⟩⟩

end CFSG.Quasithin.ChapterG.Section08

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

/-- The actual G.9.2 hypotheses supply the group-theoretic extraction inputs. -/
theorem Hypothesis.dihedralExtraction_of_faithfulComplement
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    {A X : Subgroup G} {n : ℕ} (h : Hypothesis ρ A X n)
    (hComplement : CFSG.Quasithin.ChapterG.Section08.FaithfulComplementTheorem G) :
    DihedralExtraction A X n :=
  CFSG.Quasithin.ChapterG.Section08.dihedralExtraction_of_faithfulComplement
    hComplement A X h.elementary h.nilpotent h.odd_order h.normalizes
    h.faithful_on_X n h.card_actor

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
