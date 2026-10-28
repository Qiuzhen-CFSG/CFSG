module
public import Theory.GroupAction.RankThreeBinaryFixedFactorIndependence
/-!
# A single orbit of rank-three binary fixed factors

An elementary binary group A of order eight acts on nontrivial elementary
cubic F. A group T acts on A and F compatibly with that supplied action.
If F has no whole-A fixed points and is irreducible under T, all nontrivial
coatom fixed factors form one orbit under the actual pointwise T-action.

Compatibility transports fixed subgroups. Coprime fixed-point generation
provides one active factor. The join of its orbit is nontrivial and invariant,
so irreducibility makes it all of F. Full independence of the coatom fixed
factors excludes any active factor outside that orbit. No T-transitivity
or two-group hypothesis is assumed.

This is the Sylow-transitivity argument after Stellmacher (8.6)(21), printed
p.45. The count consumer applies the orbit-cardinality theorem when T is a
two-group; the c3 action consumer transports properties between the actual
factors. All three supplied actions remain unchanged.
-/

open scoped Pointwise IsMulCommutative
public theorem rank_three_binary_fixed_factors_single_orbit
    {A F T : Type*} [Group A] [Finite A] [Group F] [Finite F] [Nontrivial F]
    [Group T] [Finite T] [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F]
    [MulDistribMulAction T A] [MulDistribMulAction T F] [MulDistribMulAction A F]
    (hA : Nat.card A = 8)
    (hcompat : ∀ (t : T) (a : A) (x : F), t • (a • x) = (t • a) • (t • x))
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (hirr : ∀ H : Subgroup F, IsInvariant T F H → H = ⊥ ∨ H = ⊤) :
    ∃ K : Subgroup A, K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥ ∧
      {L : Subgroup A | L.index = 2 ∧ FixedPoints.subgroup L F ≠ ⊥} = MulAction.orbit T K := by
  classical
  have htransport_le (t : T) (K : Subgroup A) :
      t • FixedPoints.subgroup K F ≤ FixedPoints.subgroup (t • K : Subgroup A) F := by
    intro y hy a
    obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists y t _).mp hy
    obtain ⟨b, hb, heq⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists (a : A) t K).mp a.property
    change (a : A) • (t • x) = t • x
    rw [← heq, ← hcompat]
    exact congrArg (fun z : F => t • z) (hx ⟨b, hb⟩)
  have htransport (t : T) (K : Subgroup A) :
      t • FixedPoints.subgroup K F = FixedPoints.subgroup (t • K : Subgroup A) F := by
    apply le_antisymm (htransport_le t K)
    rw [Subgroup.subset_pointwise_smul_iff]
    exact (htransport_le t⁻¹ (t • K)).trans_eq
      (congrArg (fun M : Subgroup A => FixedPoints.subgroup M F) (inv_smul_smul t K))
  have hindex (t : T) (K : Subgroup A) : (t • K).index = K.index :=
    K.index_map_equiv (MulDistribMulAction.toMulAut T A t)
  have hnonbot (t : T) (K : Subgroup A) (hK : FixedPoints.subgroup K F ≠ ⊥) :
      FixedPoints.subgroup (t • K : Subgroup A) F ≠ ⊥ := by
    intro hbot
    have hh := congrArg (fun H : Subgroup F => t⁻¹ • H)
      ((htransport t K).trans hbot)
    exact hK (by simpa using hh)
  have hexists : ∃ K : Subgroup A, K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥ := by
    let _ : CommGroup A := IsMulCommutative.instCommGroup
    let _ : Fact (IsPGroup 3 F) := ⟨IsElementaryAbelian.isPGroup 3 F⟩
    have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
      (G := F) (A := A) (q := 3) (show Nat.Coprime (Nat.card A) 3 by rw [hA]; decide)
    by_contra hnone
    have hbot : (⊤ : Subgroup F) ≤ ⊥ := by
      rw [← hgen]
      refine iSup₂_le fun K hK => ?_
      have hdiv : K.index ∣ 2 := by
        rw [Subgroup.index_eq_card, ← hK.exponent_eq_card]
        exact (Group.exponent_quotient_dvd K).trans
          (IsElementaryAbelian.exponent_dvd_p 2 A)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
      · rw [Subgroup.index_eq_one.mp hone, hfull]
      · have hz : FixedPoints.subgroup K F = ⊥ := by
          by_contra hne
          exact hnone ⟨K, htwo, hne⟩
        rw [hz]
    exact top_ne_bot (le_antisymm hbot bot_le)
  obtain ⟨K, hKindex, hKne⟩ := hexists
  let J : Subgroup F := ⨆ t : T, FixedPoints.subgroup (t • K : Subgroup A) F
  have hJstable (t : T) : t • J ≤ J := by
    change (⨆ s : T, FixedPoints.subgroup (s • K : Subgroup A) F).map
      (MulDistribMulAction.toMulAut T F t).toMonoidHom ≤ J
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    change t • FixedPoints.subgroup (s • K : Subgroup A) F ≤ J
    rw [htransport, ← mul_smul]
    exact le_iSup (fun r : T => FixedPoints.subgroup (r • K : Subgroup A) F) (t * s)
  have hJinv : IsInvariant T F J := by
    constructor
    intro t x
    constructor
    · intro hx
      exact hJstable t (Subgroup.smul_mem_pointwise_smul x t J hx)
    · intro hx
      have hh := hJstable t⁻¹ (Subgroup.smul_mem_pointwise_smul (t • x) t⁻¹ J hx)
      simpa only [inv_smul_smul] using hh
  have hJtop : J = ⊤ := by
    rcases hirr J hJinv with hbot | htop
    · have hle : FixedPoints.subgroup K F ≤ J := by
        have heq := congrArg (fun M : Subgroup A => FixedPoints.subgroup M F) (one_smul T K)
        exact heq ▸ le_iSup (fun t : T => FixedPoints.subgroup (t • K : Subgroup A) F) (1 : T)
      exact (hKne (le_bot_iff.mp (hbot ▸ hle))).elim
    · exact htop
  have hind := rank_three_binary_fixed_factors_independent (F := F) hA hfull
  have hactive : {L : Subgroup A | L.index = 2 ∧ FixedPoints.subgroup L F ≠ ⊥} =
      MulAction.orbit T K := by
    ext L
    constructor
    · rintro ⟨hLindex, hLne⟩
      by_contra hout
      have hle : J ≤ ⨆ M : {M : Subgroup A // M.index = 2},
          ⨆ (_ : M ≠ ⟨L, hLindex⟩), FixedPoints.subgroup M.val F := by
        refine iSup_le fun t => ?_
        have hne : (⟨t • K, (hindex t K).trans hKindex⟩ :
            {M : Subgroup A // M.index = 2}) ≠ ⟨L, hLindex⟩ := by
          intro heq
          apply hout
          exact ⟨t, congrArg Subtype.val heq⟩
        exact le_iSup_of_le ⟨t • K, (hindex t K).trans hKindex⟩
          (le_iSup_of_le hne le_rfl)
      have hdis := (hind ⟨L, hLindex⟩).mono_right hle
      rw [hJtop] at hdis
      exact hLne (disjoint_top.mp hdis)
    · rintro ⟨t, rfl⟩
      exact ⟨(hindex t K).trans hKindex, hnonbot t K hKne⟩
  exact ⟨K,hKindex,hKne,hactive⟩
