module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# The fixed-space contradiction in the hyperplane enlargements

Two actual conjugates suffice: their hyperplane fixed spaces intersect in
corank at most two and centralize the whole conjugate-generated subgroup.
Its full fixed space is invariant under M_V, escapes M, and therefore lies
in Γ below m. E.6.13 excludes it. This also excludes any proposed overgroup
of corank two containing every conjugate, without assuming that overgroup
itself is M_V-invariant.

The residual lemma keeps the local centralizer C_M(A) explicit. In particular
it does not silently replace it by C_G(A) in the L₄(2)/L₅(2) argument.

Source: Aschbacher–Smith, E.6.22–23, printed pp.254–255 (PDF pp.265–266).
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

omit [Finite G] in
/-- The normalizer of V and the normalizer of Y preserve their common fixed space. -/
theorem fixedSpace_normalized {A Y : Subgroup G}
    (hAV : A ≤ normalizer (V : Set G)) (hAY : A ≤ normalizer (Y : Set G)) :
    A ≤ normalizer (V ⊓ centralizer (Y : Set G) : Set G) :=
  (le_inf hAV (hAY.trans (normalizer_le_normalizer_centralizer Y))).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- Conjugation preserving V transports its full fixed space. -/
theorem fixedSpace_conjugate (L : Subgroup G) (g : G)
    (hg : g ∈ normalizer (V : Set G)) :
    (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      V ⊓ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hV : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    hV, Theory.Quasithin.map_centralizer]

/-- At most two conjugates, each fixing a hyperplane, give orbit corank at most two. -/
theorem orbit_fixedSpace_corank_le_two [IsElementaryAbelian 2 V]
    {U L : Subgroup G} (hU : IsHyperplane V U)
    (hLU : L ≤ centralizer (U : Set G))
    (hcard : (conjugates M V L).ncard ≤ 2) :
    subgroupCorank V (V ⊓ centralizer (componentOrbit L (localNormalizer M V) : Set G)) ≤ 2 := by
  classical
  let N := localNormalizer M V
  have hone : L ∈ conjugates M V L := by
    refine ⟨1, ?_⟩
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    change L.map (MulAut.conj (1 : G)).toMonoidHom = L
    rw [h1, map_id]
  have htwo : ∃ g : N, ∀ k : N,
      L.map (MulAut.conj (k : G)).toMonoidHom = L ∨
        L.map (MulAut.conj (k : G)).toMonoidHom = L.map (MulAut.conj (g : G)).toMonoidHom := by
    by_cases hall : ∀ k : N, L.map (MulAut.conj (k : G)).toMonoidHom = L
    · exact ⟨1, fun k => Or.inl (hall k)⟩
    · push Not at hall
      obtain ⟨g, hg⟩ := hall
      refine ⟨g, fun k => ?_⟩
      by_contra! hn
      have hlt : 2 < (conjugates M V L).ncard := (Set.two_lt_ncard_iff).mpr
        ⟨L, L.map (MulAut.conj (g : G)).toMonoidHom,
          L.map (MulAut.conj (k : G)).toMonoidHom,
          hone, ⟨g, rfl⟩, ⟨k, rfl⟩, Ne.symm hg, Ne.symm hn.1, Ne.symm hn.2⟩
      omega
  obtain ⟨g, hg⟩ := htwo
  let F := V ⊓ centralizer (L : Set G)
  have hUF : U ≤ F := le_inf hU.1 (le_centralizer_iff.mp hLU)
  have hFc : subgroupCorank V F ≤ 1 := by
    simpa only [hU.2] using subgroupCorank_antitone (V := V) hUF
  have hgV : (g : G) ∈ normalizer (V : Set G) := g.property.2
  have hsmall : subgroupCorank V (F ⊓ F.map (MulAut.conj (g : G)).toMonoidHom) ≤ 2 := by
    have hh := corank_inf_le (V := V) F (F.map (MulAut.conj (g : G)).toMonoidHom)
    rw [corank_conjugate V F g hgV] at hh
    omega
  apply (subgroupCorank_antitone (show F ⊓ F.map (MulAut.conj (g : G)).toMonoidHom ≤
      V ⊓ centralizer (componentOrbit L N : Set G) from ?_)).trans hsmall
  refine le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mpr ?_)
  apply iSup_le
  intro k
  rcases hg k with hk | hk
  · rw [hk]
    exact le_centralizer_iff.mpr (inf_le_left.trans inf_le_right)
  · rw [hk]
    apply le_centralizer_iff.mpr
    exact inf_le_right.trans ((fixedSpace_conjugate L g hgV) ▸ inf_le_right)

/-- E.6.13 excludes a small invariant fixed space of an escaping subgroup. -/
theorem no_small_invariant_fixedSpace [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    {Y : Subgroup G} (he : ¬ Y ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : subgroupCorank V (V ⊓ centralizer (Y : Set G)) < localM V) : False := by
  have hescape : ¬ centralizer (V ⊓ centralizer (Y : Set G) : Set G) ≤ M :=
    fun hC => he ((le_centralizer_iff.mpr inf_le_right).trans hC)
  exact h13 _ (small_escape_mem h inf_le_left hc hescape)
    (fixedSpace_normalized h.sylow_le_normalizer hn)

/-- The common final contradiction of E.6.22 and E.6.23. -/
theorem no_two_conjugates [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hm : 2 < localM V) {U L : Subgroup G} (hU : IsHyperplane V U)
    (hLU : L ≤ centralizer (U : Set G)) (he : ¬ L ≤ M)
    (hcard : (conjugates M V L).ncard ≤ 2) : False := by
  apply no_small_invariant_fixedSpace h h13
    (fun hY => he ((le_componentOrbit L _).trans hY))
  · exact (le_inf h.sylow_le h.sylow_le_normalizer).trans
      (le_normalizer_componentOrbit L (localNormalizer M V))
  · exact lt_of_le_of_lt (orbit_fixedSpace_corank_le_two hU hLU hcard) hm

/-- The proper-enlargement branch only needs containment of the orbit in X.
No equality or invariance of X is assumed. -/
theorem no_small_overgroup_of_all_conjugates [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    {A L X : Subgroup G} (hAV : A ≤ V) (hc : subgroupCorank V A < localM V)
    (hXA : X ≤ centralizer (A : Set G)) (he : ¬ L ≤ M)
    (hall : ∀ g ∈ localNormalizer M V, L.map (MulAut.conj g).toMonoidHom ≤ X) : False := by
  have hYX : componentOrbit L (localNormalizer M V) ≤ X :=
    iSup_le fun g => hall g g.property
  apply no_small_invariant_fixedSpace h h13
    (fun hY => he ((le_componentOrbit L _).trans hY))
  · exact (le_inf h.sylow_le h.sylow_le_normalizer).trans
      (le_normalizer_componentOrbit L (localNormalizer M V))
  · exact lt_of_le_of_lt (subgroupCorank_antitone
      (le_inf hAV (le_centralizer_iff.mp (hYX.trans hXA)))) hc

/-- Once the further enlargement contains every conjugate, the proposed
proper A₆ enlargement has a forbidden small invariant fixed space. -/
theorem no_proper_six_enlargement [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hsix : SixOrbitContainment M V)
    {U A L X : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hL : SmallBlock U L) (he : ¬ L ≤ M) (hA : A ∈ obstructionFamily M V)
    (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hX : ProperSixEnlargement V U A L X) : False := by
  have hm := (lemma_E_6_16_1 h h15 hUh (fun hh => he (hL.1.trans hh))).2.1
  exact no_small_overgroup_of_all_conjugates h h13 hA.1 (by omega)
    hX.component.1 he (hsix U hU hUh L hL he A hA hAU hc X hX)

/-- Every two-subgroup of C_M(A) centralizes V when the corank of A is below m.
This uses O^{2′}, whose quotient has odd order, not O² or O₂. -/
theorem local_two_subgroup_centralizes [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {A R : Subgroup G} (hAV : A ≤ V) (hc : subgroupCorank V A < localM V)
    (hRp : IsPGroup 2 R) (hRM : R ≤ M) (hRA : R ≤ centralizer (A : Set G)) :
    R ≤ centralizer (V : Set G) := by
  have hRC : R ≤ M ⊓ centralizer (A : Set G) := le_inf hRM hRA
  have hp := le_primeToResidual_of_isPGroup
    (hRp.of_equiv (subgroupOfEquivOfLe hRC).symm)
  intro x hx
  exact (h.oddCentralizerCondition_of_small hAV hc
    (mem_map_of_mem _ (hp (show (⟨x, hRC hx⟩ : ↥(M ⊓ centralizer (A : Set G))) ∈
      R.subgroupOf (M ⊓ centralizer (A : Set G)) from hx)))).2

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
