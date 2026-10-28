module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure.Parabolic
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Constructing the local hypothesis in 12.8.4(1)

For each J∈H_z, its nontrivial two-core places J in a maximal two-local
containing the actual ambient Sylow T. Even characteristic restricts to J.
The literal flag gives both Sylows, all point normalizations and the correct
embedded residual L₁. Higher-rank irreducibility comes from the existing
ambient natural marking; at rank two, the orders two and four suffice.
The elementary instance on the tilded seed is its actual quotient image.

The flag and earlier setup consequences remain the constructions of
qt-12-08-setup and qt-12-08-preliminary. In rank two those consequences
come from RankTwoHypothesis, with S₃ acting through LT/O₂(LT). No full
L action or natural marking in dimension two is assumed here.

Source: Aschbacher--Smith, Hypothesis 12.8.1 and Lemma 12.8.4(1),
printed pp.849--850; Hypothesis G.2.1, printed p.332.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The elementary seed has an elementary image in the literal tilde quotient. -/
theorem localKernel_tilde_seed_elementary : IsElementaryAbelian 2 (F.tilde V) := by
  let : IsElementaryAbelian 2 (V.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  exact IsElementaryAbelian.map _

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The exceptional solvable-residual nodes at n=5 do not include node one. -/
theorem localKernel_L₁ (L J : Subgroup G) :
    (ChapterG.Section02.Setup.L₁
      { V := V, V₁ := F.Vi 1, L := L, T := (T : Subgroup G), H := J }) = F.Li L 1 := by
  simp only [ChapterG.Section02.Setup.L₁, ChapterG.Section02.Setup.G₁, Li, Gi]
  norm_num
  rfl

omit [IsElementaryAbelian 2 V] in
/-- Even characteristic passes through a maximal two-local containing the actual Sylow. -/
theorem localKernel_characteristicTwo {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M J : Subgroup G) (hJ : J ∈ F.Hz L M) : HasCharacteristicTwo J := by
  have hTJ : (T : Subgroup G) ≤ J := fun x hx => hJ.1.2 (Or.inr hx)
  have hQ : pCore 2 J ≠ ⊥ := by
    intro he
    apply hJ.1.1
    change (pCore 2 J).map J.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨N, hN, hJN⟩ := exists_twoLocal_overgroup_normalizer J (pCore 2 J) hQ pCore_isPGroup
  obtain ⟨R, hNR, hR⟩ := Finite.exists_le_maximal hN
  have hJR : J ≤ R := J.le_normalizer.trans (hJN.trans hNR)
  have hTR : (T : Subgroup G) ≤ R := hTJ.trans hJR
  have hh : HasCharacteristicTwo (J.subgroupOf R) :=
    centralizer_pCore_le_of_sylow_le (T.subtype hTR) (J.subgroupOf R)
      (comap_mono hTJ) (hG.evenCharacteristic T R hR hTR)
  exact hh.of_equiv (subgroupOfEquivOfLe hJR)

/-- Irreducibility of [V₁,V], using only subgroup orders in dimension two. -/
theorem localKernel_irreducible (L : Subgroup G) (hn : 2 ≤ n)
    (hLV : L ≤ normalizer (V : Set G))
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (W : Subgroup G) (hpW : F.Vi 1 ≤ W) (hWV : W ≤ V)
    (hLW : F.Li L 1 ≤ normalizer (W : Set G)) : W = F.Vi 1 ∨ W = V := by
  by_cases hn3 : 3 ≤ n
  · let := F.localKernel_tilde_seed_elementary
    obtain ⟨A⟩ := hnatural hn3
    exact F.invariant_subgroup_of_ambient_natural A hn3 W hpW hWV hLW
  · have hn2 : n = 2 := by omega
    have hV : Nat.card V = 4 := by
      have hc := F.card n le_rfl
      rw [F.last] at hc
      simpa [hn2] using hc
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
    have hw := card_le_of_le hpW
    have hd : Nat.card W ∣ 2 ^ 2 := by simpa [hV] using card_dvd_of_le hWV
    obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
    interval_cases k
    · norm_num [hkcard, hp] at hw
    · left
      exact (eq_of_le_of_card_ge hpW (by simpa [hp] using hkcard.le)).symm
    · right
      exact eq_of_le_of_card_ge hWV (by simpa [hV] using hkcard.ge)

/-- Construct the complete G.2.1 hypothesis for the original local subgroup J. -/
theorem localKernel_hypothesis {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M J : Subgroup G) (hn : 2 ≤ n)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hJ : J ∈ F.Hz L M) :
    ChapterG.Section02.Setup.Hypothesis
      { V := V, V₁ := F.Vi 1, L := L, T := (T : Subgroup G), H := J } := by
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := F.last ▸ F.invariant n
  have hTJ : (T : Subgroup G) ≤ J := fun x hx => hJ.1.2 (Or.inr hx)
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hL1 := F.localKernel_L₁ L J
  refine {
    elementary := inferInstance
    point_ne_bot := by
      change F.Vi 1 ≠ ⊥
      intro he
      rw [he, Subgroup.card_bot] at hp
      omega
    point_le := F.le_seed 1
    residual := hres
    V_le_T := hVT
    T_normalizes_point := F.invariant 1
    T_normalizes_V := hTV
    T_normalizes_L := hTL
    sylow_LT := ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
    H_le := hJ.2.1
    local_le := by rw [hL1]; exact sup_le (fun x hx => hJ.1.2 (Or.inl hx)) hTJ
    sylow_H := ⟨T.subtype hTJ, map_subgroupOf_eq_of_le hTJ⟩
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (F.localKernel_characteristicTwo hG L M J hJ)
    local_normalizes_V := by rw [hL1]; exact sup_le ((F.Li_le L 1).trans (inf_le_left.trans hLV)) hTV
    quotient_nonzero := ?_
    irreducible := ?_ }
  · intro he
    change F.Vi 1 = V at he
    have hc := card_le_of_le (F.le_seed 2)
    have hVcard : Nat.card V = 2 := (congrArg (fun A : Subgroup G => Nat.card A) he).symm.trans hp
    rw [hVcard, F.card 2 hn] at hc
    norm_num at hc
  · intro W hpW hWV hnorm
    rw [hL1] at hnorm
    exact F.localKernel_irreducible L hn hLV hnatural W hpW hWV (le_sup_left.trans hnorm)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
