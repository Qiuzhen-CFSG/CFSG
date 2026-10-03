module

public import Theory.GroupTheory.IsolatedFourTwoGroup
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Normal elementary subgroups near an isolated four

An isolated elementary four in a finite two-group prevents a larger normal
binary elementary subgroup. A central involution in the normal subgroup lies
in the isolated four. Conjugation by another element of the four has fixed
space of order at most two; the involution fixed-displacement count bounds the
normal subgroup by four. This gives the normal-eight case of the connectivity
criterion without an ambient fusion assumption.

Source: GLS, volume 2, Corollary 10.22(ii), following Lemma 10.21(iii),
`refs/KGroup/GLS2/ChapterC.tex`.
-/

open scoped IsMulCommutative
namespace Subgroup

public theorem card_normal_elementary_le_four_of_maximal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (V E : Subgroup P) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 E]
    [E.Normal] (hV : Nat.card V = 4)
    (hmax : ∀ B : Subgroup P, IsElementaryAbelian 2 B → V ≤ B → B ≤ V) :
    Nat.card E ≤ 4 := by
  classical
  by_contra! hE
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, htne, htZ⟩ := exists_nontrivial_center_mem_normal (p := 2) E
  have htneP : (t : P) ≠ 1 := fun h => htne (Subtype.ext h)
  have ht2 : (t : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ t.property
  have htV : (t : P) ∈ V := involution_mem_of_maximal_elementary_four V hmax t ht2
    (fun v _ => mem_center_iff.mp htZ v)
  have hVE : ¬ V ≤ E := by
    intro h
    have hc := card_le_of_le (hmax E inferInstance h)
    omega
  obtain ⟨a, haV, haE⟩ := SetLike.not_le_iff_exists.mp hVE
  have ha1 : a ≠ 1 := fun h => haE (h ▸ E.one_mem)
  have hat : (t : P) ≠ a := fun h => haE (h ▸ t.property)
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ haV
  have hcomm : Commute (t : P) a := (mem_center_iff.mp htZ a).symm
  let : IsKleinFour (closure ({(t : P), a} : Set P)) :=
    isKleinFour_closure_pair (t : P) a (by simpa [pow_two] using ht2)
      (by simpa [pow_two] using ha2) htneP ha1 hat hcomm
  have hgen : closure ({(t : P), a} : Set P) = V := by
    apply eq_of_le_of_card_ge
    · exact (closure_le _).mpr (by intro x hx; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl <;> assumption)
    · rw [hV, IsKleinFour.card_four]
  let aN : normalizer (E : Set P) := ⟨a, by rw [normalizer_eq_top]; trivial⟩
  let f := E.normalizerMonoidHom aN
  have hf2 : f ^ 2 = 1 := by
    change (E.normalizerMonoidHom aN) ^ 2 = 1
    rw [← map_pow, show aN ^ 2 = 1 from Subtype.ext ha2, map_one]
  let F := FixedPoints.subgroup (zpowers f) E
  let B := F.map E.subtype
  have hBE : B ≤ E := map_subtype_le _
  have hBV : B ≤ V := by
    rintro b ⟨bE, hbE, rfl⟩
    apply involution_mem_of_maximal_elementary_four V hmax bE
      (elemPow_eq_one_of_isElementaryAbelian _ bE.property)
    have hfix := hbE ⟨f, mem_zpowers f⟩
    have hfixP := congrArg E.subtype hfix
    change a * (bE : P) * a⁻¹ = (bE : P) at hfixP
    have hCb : V ≤ centralizer ({(bE : P)} : Set P) := by
      rw [← hgen]
      apply (closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp htZ bE).symm
      · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfixP)
    exact fun v hv => mem_centralizer_singleton_iff.mp (hCb hv)
  have hBlt : B < V := lt_of_le_of_ne hBV (by
    intro heq
    exact haE (hBE (heq.symm ▸ haV)))
  have hFlt : Nat.card F < 4 := by
    by_contra! hc
    apply hBlt.ne
    apply eq_of_le_of_card_ge hBV
    simpa only [B, card_map_of_injective E.subtype_injective, hV] using hc
  have hFtwo : IsPGroup 2 F := (IsElementaryAbelian.isPGroup 2 E).to_subgroup F
  obtain ⟨n, hn⟩ := hFtwo.exists_card_eq
  have hnlt : n < 2 := by
    by_contra! hn2
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
    omega
  have hFle : Nat.card F ≤ 2 := by interval_cases n <;> simp_all
  obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data f hf2
  have hc := card_le_of_le hle
  change Nat.card (commutatorAction (zpowers f) E) ≤ Nat.card F at hc
  change Nat.card E = Nat.card F * Nat.card (commutatorAction (zpowers f) E) at hcount
  nlinarith
end Subgroup

namespace Subgroup
public theorem card_normal_elementary_le_four_of_isolated_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (V E : Subgroup P) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 E]
    [E.Normal] (hV : Nat.card V = 4)
    (hiso : ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set P) → W = V) : Nat.card E ≤ 4 :=
  card_normal_elementary_le_four_of_maximal_four hP V E hV
    (maximal_elementary_of_isolated_four V hV hiso)

public theorem card_normal_elementary_le_four_of_isolated_four_in_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4) (hVS : V ≤ S)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  let VS := V.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 VS := IsElementaryAbelian.subgroupOf hVS
  have hVScard : Nat.card VS = 4 := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv]
  apply card_normal_elementary_le_four_of_isolated_four S.isPGroup' VS E hVScard
  intro W hWe hW hWC
  let : IsElementaryAbelian 2 W := hWe
  have heq : W.map (S : Subgroup G).subtype = V :=
    hiso _ (IsElementaryAbelian.map _) (by
      simpa only [card_map_of_injective (S : Subgroup G).subtype_injective] using hW)
      (map_subtype_le _) (by
        rintro x ⟨w, hw, rfl⟩ v hv
        exact congrArg Subtype.val (hWC hw ⟨v, hVS hv⟩ hv))
  apply map_injective (S : Subgroup G).subtype_injective
  rw [heq, map_subgroupOf_eq_of_le hVS]
end Subgroup

namespace Subgroup
public theorem card_omega_center_eq_two_of_isolated_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A V : Subgroup P) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 V]
    (hA : 8 ≤ Nat.card A) (hV : Nat.card V = 4)
    (hiso : ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set P) → W = V) :
    Nat.card (omega₁ (center P) (p := 2)) = 2 := by
  obtain ⟨U, hUn, hUe, hU⟩ := hP.exists_normal_elementaryAbelian_four A hA
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  obtain ⟨t, ht, htZ, -, hVT, -⟩ :=
    exists_central_generator_inf_of_isolated_four hP A U V hA hU hV hiso
  let O := omega₁ (center P) (p := 2)
  let Z := O.map (center P).subtype
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hZC : Z ≤ center P := map_subtype_le _
  have hZV : Z ≤ V := by
    intro z hz
    exact involution_mem_of_maximal_elementary_four V
      (maximal_elementary_of_isolated_four V hV hiso) z
      (elemPow_eq_one_of_isElementaryAbelian _ hz)
      (fun v _ => mem_center_iff.mp (hZC hz) v)
  have hZline : Z ≤ zpowers t := by
    rw [← hVT]
    exact le_inf hZV (hZC.trans (center_le_centralizer _))
  have htO : (⟨t, htZ⟩ : center P) ∈ O := by
    apply subset_closure
    change (⟨t, htZ⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    change t ^ (2 ^ 1) = 1
    simpa only [pow_one, ht] using pow_orderOf_eq_one t
  have hlineZ : zpowers t ≤ Z := zpowers_le.mpr (mem_map_of_mem (center P).subtype htO)
  have hZeq := le_antisymm hZline hlineZ
  have hc := congrArg (fun B : Subgroup P => Nat.card B) hZeq
  simpa only [Z, card_map_of_injective (center P).subtype_injective, Nat.card_zpowers, ht] using hc
end Subgroup

namespace Subgroup
public theorem exists_distinct_commuting_four_of_normal_elementary_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E V : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 V]
    (hE : 8 ≤ Nat.card E) (hV : Nat.card V = 4) :
    ∃ W : Subgroup P, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
      W ≤ centralizer (V : Set P) ∧ W ≠ V := by
  classical
  by_contra h
  have hiso : ∀ W : Subgroup P, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (V : Set P) → W = V := by
    intro W hWe hW hWC
    by_contra hne
    exact h ⟨W, hWe, hW, hWC, hne⟩
  have hb := card_normal_elementary_le_four_of_isolated_four hP V E hV hiso
  omega
end Subgroup

