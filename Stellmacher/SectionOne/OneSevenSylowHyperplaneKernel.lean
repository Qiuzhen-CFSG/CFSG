module

public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.FinCases

/-!
# Faithfulness on a Sylow-invariant hyperplane

When the canonical one-seven family has two factors and its fixed complement
vanishes, its two order-four supports form the whole module. Every actor
permutes these supports, and Sylow transitivity supplies an actor swapping
them. A Sylow-invariant subgroup of order eight therefore contains neither
support, so its join with either support is the whole module.

An actor fixing the hyperplane cannot swap the supports: its intersection
with one support would be trivial, forcing a subgroup of order thirty-two
inside the order-sixteen module. If the actor preserves both supports, the
two joins show that it fixes each support pointwise. Faithfulness of the
original action then makes the actor trivial.

This intrinsic action calculation supplies the invariant rank-three kernel
step in Stellmacher (9.3), final R₀,C₀ paragraph, journal p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`. No group-model identification or
transvection classification is assumed.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem hyperplane_pair_data
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
  have hfac : ∀ i, IsOneSevenFactor (V := V) (factors i) := by
    intro i
    fin_cases i
    · exact hD
    · exact hF
  have hinj : Function.Injective factors := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all [factors]
  have hE : oneSevenGenerated (G := G) (V := V) = ⨆ i, factors i := by
    apply le_antisymm
    · apply sSup_le
      intro K hK
      have hmem := (mem_oneSevenFactors_iff K).mpr hK
      rw [hpair] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact le_iSup factors 0
      · exact le_iSup factors 1
    · exact iSup_le fun i => le_sSup (hfac i)
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
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  exact ⟨D, F, hne, (by intro K; rw [hpair]; simp), hD, hF, hsup',
    hprod.2.1 (some 0) (some 1) (by decide)⟩

private theorem hyperplane_sup_eq_top
    {V : Type u} [Group V] [Finite V]
    (H U : Subgroup V) (hV : Nat.card V = 16)
    (hH : Nat.card H = 8) (hnot : ¬ U ≤ H) : H ⊔ U = ⊤ := by
  have hbound : Nat.card (H ⊔ U : Subgroup V) ≤ 16 := by
    simpa [hV] using (Nat.card_le_card_of_injective _ (H ⊔ U).subtype_injective)
  have hlarge : 8 < Nat.card (H ⊔ U : Subgroup V) := by
    by_contra hn
    have heq : H = H ⊔ U := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exact hnot (heq ▸ le_sup_right)
  obtain ⟨multiple, heq⟩ := Subgroup.card_dvd_of_le (show H ≤ H ⊔ U from le_sup_left)
  rw [hH] at heq
  have hcard : Nat.card (H ⊔ U : Subgroup V) = 16 := by omega
  apply Subgroup.eq_of_le_of_card_ge le_top
  simp [hV, hcard]

private theorem fixes_support_of_sup
    {G V : Type u} [Group G] [Group V] [IsMulCommutative V]
    [MulDistribMulAction G V]
    (H U W : Subgroup V) (hdis : Disjoint U W) (hsup : H ⊔ W = ⊤)
    (actor : G) (hfix : ∀ v ∈ H, actor • v = v)
    (hU : ∀ v ∈ U, actor • v ∈ U) (hW : ∀ v ∈ W, actor • v ∈ W) :
    ∀ v ∈ U, actor • v = v := by
  intro v hv
  have hdeltaU : v⁻¹ * (actor • v) ∈ U := U.mul_mem (U.inv_mem hv) (hU v hv)
  have hdeltaW : v⁻¹ * (actor • v) ∈ W := by
    have hmem : v ∈ H ⊔ W := by rw [hsup]; trivial
    obtain ⟨base, hbase, tail, htail, rfl⟩ := Subgroup.mem_sup.mp hmem
    have heq : (base * tail)⁻¹ * (actor • (base * tail)) =
        tail⁻¹ * (actor • tail) := by
      rw [smul_mul', hfix base hbase, mul_inv_rev]
      group
    rw [heq]
    exact W.mul_mem (W.inv_mem htail) (hW tail htail)
  exact (inv_mul_eq_one.mp (hdis.le_bot ⟨hdeltaU, hdeltaW⟩)).symm

private theorem fixing_swapping_pair_impossible
    {G V : Type u} [Group G] [Group V] [Finite V] [IsMulCommutative V]
    [MulDistribMulAction G V]
    (H U W : Subgroup V) (hdis : Disjoint U W)
    (hV : Nat.card V = 16) (hH : Nat.card H = 8) (hU : Nat.card U = 4)
    (actor : G) (hfix : ∀ v ∈ H, actor • v = v)
    (hswap : ∀ v ∈ U, actor • v ∈ W) : False := by
  have hinter : Disjoint H U := by
    apply disjoint_iff_inf_le.mpr
    intro v hv
    exact hdis.le_bot ⟨hv.2, hfix v hv.1 ▸ hswap v hv.2⟩
  have hnorm : U ≤ Subgroup.normalizer (H : Set V) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcard := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint H U hnorm hinter
  have hbound := Nat.card_le_card_of_injective _ (H ⊔ U).subtype_injective
  rw [hcard, hH, hU, hV] at hbound
  omega

public theorem oneSeven_sylow_invariant_hyperplane_fixing_eq_bot
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
    fixingSubgroup G (hyperplane : Set V) = ⊥ := by
  classical
  obtain ⟨D, F, hne, hpair, hD, hF, hsup, hdis⟩ :=
    hyperplane_pair_data h sylow hfixed htwo
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
      (v : V) (hv : v ∈ commutatorAction K V) :
      actor • v ∈ commutatorAction L V := by
    rw [← heq, ← RankOneThreeGroupAssembly.commutatorAction_conjBy K actor]
    exact ⟨v, hv, rfl⟩
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
    intro v hv
    exact (hinvariant.invariant swap v).mpr (hu (htransport F D swap hswap' v hv))
  have hnotW : ¬ W ≤ hyperplane := by
    intro hw
    apply hproper
    rw [← hsup]
    refine sup_le ?_ hw
    intro v hv
    exact (hinvariant.invariant swap v).mpr (hw (htransport D F swap hswap v hv))
  have hsupU := hyperplane_sup_eq_top hyperplane U hVcard hcard hnotU
  have hsupW := hyperplane_sup_eq_top hyperplane W hVcard hcard hnotW
  apply le_bot_iff.mp
  intro actor hactor
  have hfix : ∀ v ∈ hyperplane, actor • v = v := (mem_fixingSubgroup_iff (M := G)).mp hactor
  rcases hperm actor with hp | hp
  · have hU := htransport D D actor hp.1
    have hW := htransport F F actor hp.2
    have hfixU := fixes_support_of_sup hyperplane U W hdis hsupW actor hfix hU hW
    have hfixW := fixes_support_of_sup hyperplane W U hdis.symm hsupU actor hfix hW hU
    rw [← h.action_faithful]
    apply (mem_fixingSubgroup_iff (M := G)).mpr
    intro v _
    have hv : v ∈ U ⊔ W := by rw [hsup]; trivial
    obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [smul_mul', hfixU left hleft, hfixW right hright]
  · exact (fixing_swapping_pair_impossible hyperplane U W hdis hVcard hcard hUcard
      actor hfix (htransport D F actor hp.1)).elim


end Stellmacher.SectionOne
