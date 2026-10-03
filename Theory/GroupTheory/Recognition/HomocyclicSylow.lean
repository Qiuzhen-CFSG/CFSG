module

public import Theory.Character.HomocyclicSylowKernel
public import Theory.GroupTheory.SylowCentralizerCore
public import Theory.GroupTheory.NormalAbelianSylowKleinFrattini
public import Theory.GroupTheory.PGroup.RankTwoHomocyclicFrattini
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Brauer's rank-two homocyclic Sylow theorem

A finite group with trivial odd core and Sylow two-subgroup
`C_(2^n) × C_(2^n)`, for `n ≥ 2`, has that Sylow subgroup normal.
If its normalizer centralizes it, Burnside transfer and the trivial odd core
make it the whole group. Otherwise Brauer's character argument supplies a
proper normal overgroup. Induction on the group order gives normality there,
and characteristicity of a normal Sylow subgroup gives normality in the
original group.

Normality also gives self-centralization and, in the absence of normal
subgroups of index two, index three. The separate solvable and already-normal
endpoints remain valid for the Klein four Sylow subgroup; the bound two is
needed only for the character argument establishing unconditional normality.

Source: R. Brauer, *Some applications of the theory of blocks of characters
of finite groups. II*, §VI, Theorem 1, pp.317–320. The principal-block
construction is proved in `Theory.Character.HomocyclicSylowKernel`.
-/

private theorem commutative_of_equiv_prod_zmod
    {U : Type*} [Group U] {n : ℕ}
    (e : U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    IsMulCommutative U :=
  ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩

/-- The solvable case of homocyclic Sylow normality, valid even for a Klein
four Sylow subgroup. -/
public theorem normal_homocyclic_sylow_of_isSolvable
    {K : Type*} [Group K] [Finite K]
    (hsolvable : Group.IsSolvable K) (hcore : pPrimeCore 2 K = ⊥)
    (U : Sylow 2 K) {n : ℕ}
    (e : U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (U : Subgroup K).Normal := by
  let : IsMulCommutative U := commutative_of_equiv_prod_zmod e
  exact U.normal_of_isMulCommutative_of_isSolvable hsolvable hcore

/-- Normality gives all the remaining conclusions of the homocyclic Sylow
statement used in Alperin–Brauer–Gorenstein, II.3, Proposition 4. -/
public theorem homocyclic_sylow_structure_of_normal
    {K : Type*} [Group K] [Finite K]
    (hcore : pPrimeCore 2 K = ⊥)
    (hno : ∀ N : Subgroup K, N.Normal → N.index ≠ 2)
    (U : Sylow 2 K) [(U : Subgroup K).Normal] {n : ℕ} (hn : 1 ≤ n)
    (e : U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (U : Subgroup K).index = 3 ∧ Subgroup.centralizer (U : Set K) = U := by
  let : IsMulCommutative U := commutative_of_equiv_prod_zmod e
  let : IsKleinFour (U ⧸ frattini U) :=
    isKleinFour_frattini_quotient_of_equiv_prod_zmod hn e
  exact ⟨U.index_eq_three_of_normal_of_kleinFour_frattini hcore hno,
    U.centralizer_eq_self_of_normal_of_pPrimeCore_eq_bot hcore⟩

universe u

open Subgroup in
/-- Brauer's homocyclic Sylow theorem: trivial odd core forces a rank-two
homocyclic Sylow two-subgroup of exponent at least four to be normal.
No hypothesis on normal subgroups of index two is needed for normality. -/
public theorem normal_homocyclic_sylow
    {G : Type u} [Group G] [Finite G] (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (S : Subgroup G).Normal := by
  let P : ℕ → Prop := fun k => ∀ (H : Type u) [Group H] [Finite H],
    Nat.card H = k → pPrimeCore 2 H = ⊥ → ∀ (T : Sylow 2 H),
    (T ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) →
    (T : Subgroup H).Normal
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro H _ _ hcard hcore T e
      by_cases hNC : normalizer (T : Set H) ≤ centralizer (T : Set H)
      · let f := MonoidHom.transferSylow T hNC
        have hfker : f.ker = ⊥ := by
          apply bot_unique
          rw [← hcore]
          exact le_sSup ⟨inferInstance,
            Nat.prime_two.coprime_iff_not_dvd.mpr
              (MonoidHom.not_dvd_card_ker_transferSylow T hNC)⟩
        have hHp : IsPGroup 2 H := T.isPGroup'.of_injective f
          ((MonoidHom.ker_eq_bot_iff f).mp hfker)
        have htop := T.is_maximal' (hHp.to_subgroup ⊤) le_top
        rw [← htop]
        infer_instance
      · obtain ⟨N, hN, hproper, hTN⟩ := exists_proper_normal_overgroup_of_homocyclic_sylow hcore T hn e hNC
        let : N.Normal := hN
        let U := T.subtype hTN
        have hcoreN : pPrimeCore 2 N = ⊥ := by
          have hmap : (pPrimeCore 2 N).map N.subtype = ⊥ :=
            pPrimeCore_eq_bot_iff.mp hcore _ inferInstance
              (Nat.Coprime.of_dvd_right (card_map_dvd _ N.subtype)
                pPrimeCore_coprime_card)
          exact map_injective (f := N.subtype) Subtype.val_injective
            (by simpa only [Subgroup.map_bot] using hmap)
        have hless : Nat.card N < k := by
          rw [← hcard]
          have hx : ∃ x : H, x ∉ N := by
            by_contra h
            push Not at h
            exact hproper (eq_top_iff.mpr (fun x _ => h x))
          obtain ⟨x, hx⟩ := hx
          exact Finite.card_subtype_lt hx
        have he : U ≃* T := subgroupOfEquivOfLe hTN
        have hUn : (U : Subgroup N).Normal :=
          ih (Nat.card N) hless N rfl hcoreN U (he.trans e)
        let : (U : Subgroup N).Characteristic := U.characteristic_of_normal hUn
        have hmapn : ((U : Subgroup N).map N.subtype).Normal := inferInstance
        have heq : (U : Subgroup N).map N.subtype = (T : Subgroup H) :=
          map_subgroupOf_eq_of_le hTN
        rwa [heq] at hmapn
  exact hP (Nat.card G) G rfl hcore S e

/-- The homocyclic Sylow structure used in Alperin–Brauer–Gorenstein,
II.3, Proposition 4: normality, index three, and self-centralization. -/
public theorem homocyclic_sylow_structure
    {K : Type*} [Group K] [Finite K]
    (hcore : pPrimeCore 2 K = ⊥)
    (hno : ∀ N : Subgroup K, N.Normal → N.index ≠ 2)
    (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (U : Subgroup K).Normal ∧ (U : Subgroup K).index = 3 ∧
      Subgroup.centralizer (U : Set K) = U := by
  let hnormal : (U : Subgroup K).Normal := normal_homocyclic_sylow hcore U hn e
  exact ⟨hnormal, homocyclic_sylow_structure_of_normal hcore hno U (by omega) e⟩
