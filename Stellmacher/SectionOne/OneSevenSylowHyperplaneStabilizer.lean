module

public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Stellmacher.TwoSupportHyperplaneAction

/-!
# Setwise stabilizer of a Sylow-invariant hyperplane

With two canonical one-seven factors and no fixed complement, their
order-four commutator supports are disjoint and span the module. Ambient
conjugation permutes the supports, while Sylow transitivity supplies a
swap. A Sylow-invariant hyperplane of order eight contains neither support.

The two-support action theorem therefore makes the fourth power of every
setwise stabilizer element trivial. The setwise stabilizer is consequently
a two-group containing the given Sylow subgroup, so Sylow maximality gives
the required containment. This uses the actual module action and proves
setwise control, rather than replacing setwise preservation by pointwise
fixing or assuming a coordinate classification.

Source: Stellmacher (1.7)(c) and the final R₀,C₀ paragraph of (9.3), journal
p.50/PDF p.40 of `refs/files/stellmacher-n-group.pdf`. Ambient normalizer
transport and the remaining odd-layer contradiction are separate steps.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem stabilizer_pair_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (sylow : Sylow 2 G)
    (hfixed : FixedPoints.subgroup
      (oneE (V := V) (sylow : Subgroup G)) V = ⊥)
    (htwo : (oneSevenFactors (G := G) (V := V)).card = 2) :
    ∃ D F : Subgroup G, D ≠ F ∧
      (∀ K, K ∈ oneSevenFactors (G := G) (V := V) ↔ K = D ∨ K = F) ∧
      IsOneSevenFactor (V := V) D ∧ IsOneSevenFactor (V := V) F ∧
      commutatorAction D V ⊔ commutatorAction F V = ⊤ ∧
      Disjoint (commutatorAction D V) (commutatorAction F V) := by
  classical
  obtain ⟨D, F, hne, hpair⟩ := Finset.card_eq_two.mp htwo
  have hD : IsOneSevenFactor (V := V) D :=
    (mem_oneSevenFactors_iff D).mp (by rw [hpair]; simp)
  have hF : IsOneSevenFactor (V := V) F :=
    (mem_oneSevenFactors_iff F).mp (by rw [hpair]; simp)
  let factors : Fin 2 → Subgroup G := ![D, F]
  have hfac : ∀ index, IsOneSevenFactor (V := V) (factors index) := by
    intro index
    fin_cases index
    · exact hD
    · exact hF
  have hinj : Function.Injective factors := by
    intro first second heq
    fin_cases first <;> fin_cases second <;> simp_all [factors]
  have hE : oneSevenGenerated (G := G) (V := V) = ⨆ index, factors index := by
    apply le_antisymm
    · apply sSup_le
      intro K hK
      have hmem := (mem_oneSevenFactors_iff K).mpr hK
      rw [hpair] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact le_iSup factors 0
      · exact le_iSup factors 1
    · exact iSup_le fun index => le_sSup (hfac index)
  have hfix : FixedPoints.subgroup (oneSevenGenerated (G := G) (V := V)) V = ⊥ := by
    rw [← (oneSeven_global_identification h sylow).2]
    exact hfixed
  have hprod := oneSevenFactor_module_product h factors hfac hinj _ hE
  have hsup := hprod.1
  rw [iSup_option, hfix, bot_sup_eq] at hsup
  have hsup' : commutatorAction D V ⊔ commutatorAction F V = ⊤ := by
    apply top_unique
    rw [hsup]
    apply iSup_le
    intro index
    fin_cases index
    · exact le_sup_left
    · exact le_sup_right
  exact ⟨D, F, hne, (by intro K; rw [hpair]; simp), hD, hF, hsup',
    hprod.2.1 (some 0) (some 1) (by decide)⟩

private theorem oneSeven_sylow_invariant_hyperplane_support_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (sylow : Sylow 2 G)
    (hgen : oneE (V := V) (sylow : Subgroup G) ⊔
      (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) (⊤ : Subgroup G))
    (hfixed : FixedPoints.subgroup
      (oneE (V := V) (sylow : Subgroup G)) V = ⊥)
    (htwo : (oneSevenFactors (G := G) (V := V)).card = 2)
    (hyperplane : Subgroup V)
    (hinvariant : IsInvariant sylow V hyperplane)
    (hcard : Nat.card hyperplane = 8) :
    ∃ U W : Subgroup V, U ⊔ W = ⊤ ∧ Disjoint U W ∧
      Nat.card U = 4 ∧ Nat.card W = 4 ∧ ¬ U ≤ hyperplane ∧ ¬ W ≤ hyperplane ∧
      ∀ actor : G,
        ((∀ vector ∈ U, actor • vector ∈ U) ∧
          (∀ vector ∈ W, actor • vector ∈ W)) ∨
        ((∀ vector ∈ U, actor • vector ∈ W) ∧
          (∀ vector ∈ W, actor • vector ∈ U)) := by
  classical
  obtain ⟨D, F, hne, hpair, hD, hF, hsup, hdis⟩ :=
    stabilizer_pair_data h sylow hfixed htwo
  let U := commutatorAction D V
  let W := commutatorAction F V
  have hUcard : Nat.card U = 4 := hD.2.2.1
  have hWcard : Nat.card W = 4 := hF.2.2.1
  have hVcard : Nat.card V = 16 := by
    have hnorm : W ≤ Subgroup.normalizer (U : Set V) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint U W hnorm hdis
    change Nat.card (commutatorAction D V ⊔ commutatorAction F V : Subgroup V) = _ at hprod
    simpa [hsup, hUcard, hWcard] using hprod
  have hDmem := (hpair D).mpr (Or.inl rfl)
  have hFmem := (hpair F).mpr (Or.inr rfl)
  have hperm (actor : G) :
      (D.conjBy actor = D ∧ F.conjBy actor = F) ∨
      (D.conjBy actor = F ∧ F.conjBy actor = D) := by
    have hd := (hpair _).mp ((mem_oneSevenFactors_iff _).mpr (hD.conjBy D actor))
    have hf := (hpair _).mp ((mem_oneSevenFactors_iff _).mpr (hF.conjBy F actor))
    have hconjne : D.conjBy actor ≠ F.conjBy actor :=
      fun heq => hne (Subgroup.map_injective (MulAut.conj actor).injective heq)
    rcases hd with hd | hd <;> rcases hf with hf | hf
    · exact (hconjne (hd.trans hf.symm)).elim
    · exact Or.inl ⟨hd, hf⟩
    · exact Or.inr ⟨hd, hf⟩
    · exact (hconjne (hd.trans hf.symm)).elim
  have htransport (K L : Subgroup G) (actor : G) (heq : K.conjBy actor = L)
      (vector : V) (hvector : vector ∈ commutatorAction K V) :
      actor • vector ∈ commutatorAction L V := by
    rw [← heq, ← RankOneThreeGroupAssembly.commutatorAction_conjBy K actor]
    exact ⟨vector, hvector, rfl⟩
  obtain ⟨swap, hswap⟩ := oneSeven_factor_orbit_transitive h sylow hgen hunique
    D hDmem F hFmem
  have hswap' : F.conjBy (swap : G) = D := by
    rcases hperm swap with hp | hp
    · exact (hne (hp.1.symm.trans hswap)).elim
    · exact hp.2
  have hproper : ¬ (⊤ : Subgroup V) ≤ hyperplane := by
    intro htop
    have heq : hyperplane = ⊤ := top_unique htop
    have hc : Nat.card hyperplane = Nat.card V := by simp [heq]
    omega
  have hnotU : ¬ U ≤ hyperplane := by
    intro hu
    apply hproper
    rw [← hsup]
    refine sup_le hu ?_
    intro vector hvector
    exact (hinvariant.invariant swap vector).mpr
      (hu (htransport F D swap hswap' vector hvector))
  have hnotW : ¬ W ≤ hyperplane := by
    intro hw
    apply hproper
    rw [← hsup]
    refine sup_le ?_ hw
    intro vector hvector
    exact (hinvariant.invariant swap vector).mpr
      (hw (htransport D F swap hswap vector hvector))
  refine ⟨U, W, hsup, hdis, hUcard, hWcard, hnotU, hnotW, ?_⟩
  intro actor
  rcases hperm actor with hp | hp
  · exact Or.inl ⟨htransport D D actor hp.1, htransport F F actor hp.2⟩
  · exact Or.inr ⟨htransport D F actor hp.1, htransport F D actor hp.2⟩

private theorem setwise_stabilizer_le_sylow_of_pow_four
    {G V : Type u} [Group G] [Group V] [MulAction G V]
    (sylow : Sylow 2 G) (hyperplane : Subgroup V)
    (hinvariant : IsInvariant sylow V hyperplane)
    (hfour : ∀ actor : G,
      (∀ vector : V, vector ∈ hyperplane ↔ actor • vector ∈ hyperplane) →
        actor ^ 4 = 1)
    (actor : G)
    (hsetwise : ∀ vector : V, vector ∈ hyperplane ↔ actor • vector ∈ hyperplane) :
    actor ∈ (sylow : Subgroup G) := by
  let stabilizer : Subgroup G :=
    { carrier := {element | ∀ vector : V,
        vector ∈ hyperplane ↔ element • vector ∈ hyperplane}
      one_mem' := by intro vector; simp only [one_smul]
      mul_mem' := by
        intro first second hfirst hsecond vector
        rw [mul_smul]
        exact (hsecond vector).trans (hfirst (second • vector))
      inv_mem' := by
        intro element helement vector
        simpa only [smul_inv_smul] using (helement (element⁻¹ • vector)).symm }
  have hsylow : (sylow : Subgroup G) ≤ stabilizer := by
    intro element helement vector
    exact hinvariant.invariant ⟨element, helement⟩ vector
  have htwo : IsPGroup 2 stabilizer := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro element
    refine ⟨2, ?_⟩
    apply Subtype.ext
    exact hfour element element.property
  have heq : stabilizer = (sylow : Subgroup G) := sylow.is_maximal' htwo hsylow
  rw [← heq]
  exact hsetwise

public theorem oneSeven_sylow_invariant_hyperplane_stabilizer_le_sylow
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (sylow : Sylow 2 K)
    (hgen : oneE (V := V) (sylow : Subgroup K) ⊔
      (sylow : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup K) (⊤ : Subgroup K))
    (hfixed : FixedPoints.subgroup
      (oneE (V := V) (sylow : Subgroup K)) V = ⊥)
    (htwo : (oneSevenFactors (G := K) (V := V)).card = 2)
    (hyperplane : Subgroup V)
    (hinvariant : IsInvariant sylow V hyperplane)
    (hcard : Nat.card hyperplane = 8)
    (actor : K)
    (hsetwise : ∀ vector : V, vector ∈ hyperplane ↔ actor • vector ∈ hyperplane) :
    actor ∈ (sylow : Subgroup K) := by
  obtain ⟨U, W, hsup, hdis, hU, hW, hnotU, hnotW, hperm⟩ :=
    oneSeven_sylow_invariant_hyperplane_support_data
      h sylow hgen hunique hfixed htwo hyperplane hinvariant hcard
  apply setwise_stabilizer_le_sylow_of_pow_four sylow hyperplane hinvariant
    (fun element helement => ?_) actor hsetwise
  exact two_support_hyperplane_setwise_pow_four_eq_one h.action_faithful
    U W hyperplane hsup hdis hU hW hcard hnotU hnotW element helement (hperm element)

end Stellmacher.SectionOne
