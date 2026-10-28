module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Uniqueness
public import Theory.GroupTheory.PrimePowerGenerated
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!+# Elementary deductions in the remaining S₃ case

The plane-normalizer bound forces the component to act nontrivially on
`V₁`, and consequently distinguishes its centralizer in `S` from that of
`Y₊`. Minimality gives `I = LS` once `Y₊ ≤ L`: the common Sylow subgroup
is essential here, since it puts the nontrivial normal subgroup `O₂(I)`
inside `LS`.

These are deductions used in Aschbacher--Smith 15.3.43(c) and the paragraph
preceding (e), combined manuscript (1 March 2004), printed p.1139. They
do not establish the component containment or the model exclusions.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne

open Subgroup

variable {G : Type*} [Group G]

/-- `O^{3′}(X)`, embedded in the ambient group. This uses all elements
of three-power order, not merely the elements of order three in `θ(X)`. -/
def threeResidualIn (X : Subgroup G) : Subgroup G :=
  (primePowerGenerated 3 X).map X.subtype

/-- The numerical consequence of (a) used to exclude the diagonal Borel.
Every three-subgroup of `X` lies in `O^{3′}(X)`. Its order therefore divides
three when this residual has two-core of index three. -/
theorem threeRank_le_one_of_residual_index [Finite G] {Y X : Subgroup G}
    (hY : Y = threeResidualIn X) (hindex : (pCore 2 Y).index = 3) :
    primeRank 3 X ≤ 1 := by
  let P : Sylow 3 X := default
  have hPY : (P : Subgroup X).map X.subtype ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := P.isPGroup' (⟨x, hx⟩ : P)
    rw [hY]
    exact mem_map.mpr ⟨x, mem_primePowerGenerated_of_pow
      (congrArg (fun a : P => (a : X)) hn), rfl⟩
  let f : P →* Y := {
    toFun := fun x => ⟨(x : X), hPY (mem_map.mpr ⟨x, x.property, rfl⟩)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : G)) h))
  have hd : Nat.card P ∣ Nat.card Y := card_dvd_of_injective f hf
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hcard : Nat.card Y = 2 ^ k * 3 := by
    rw [← (pCore 2 Y).card_mul_index, hk, hindex]
  rw [hcard] at hd
  obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (2 ^ k) := by
    rw [hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left j).pow_right k
  exact P.primeRank_le_one_of_isCyclic
    (isCyclic_of_card_dvd_prime (hcop.dvd_mul_left.mp hd))

/-- A subgroup of `M_I` of three-rank greater than one contradicts (a).
The diagonal-action argument must construct the actual Borel together with
the diagonal actor and its rank bound before using this lemma. -/
theorem no_high_three_rank_subgroup [Finite G] {Yplus M I B : Subgroup G}
    (hY : Yplus = threeResidualIn (M ⊓ I))
    (hindex : (pCore 2 Yplus).index = 3) (hB : B ≤ M ⊓ I) :
    ¬ 1 < primeRank 3 B := by
  have hmono := Theory.GroupTheory.primeRank_le_of_injective 3
    (Subgroup.inclusion hB) (Subgroup.inclusion_injective hB)
  exact not_lt_of_ge (hmono.trans (threeRank_le_one_of_residual_index hY hindex))

/-- Clause (c), from (b), the plane-normalizer control in 15.3.11(3),
and `L ≰ M` from 15.3.33(3). -/
theorem plane_action_and_distinct_centralizers
    {V₁ Yplus S M L : Subgroup G}
    (hV₁S : V₁ ≤ S) (hcentral : ⁅V₁, Yplus⁆ = ⊥)
    (hnorm : normalizer (V₁ : Set G) ≤ M) (hL : ¬ L ≤ M) :
    ⁅V₁, L⁆ ≠ ⊥ ∧ S ⊓ centralizer (Yplus : Set G) ≠
      S ⊓ centralizer (L : Set G) := by
  have hact : ⁅V₁, L⁆ ≠ ⊥ := by
    intro h
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
    exact hL (hc.trans ((Subgroup.centralizer_le_normalizer _).trans hnorm))
  refine ⟨hact, ?_⟩
  intro he
  have hle : V₁ ≤ S ⊓ centralizer (Yplus : Set G) :=
    le_inf hV₁S (commutator_eq_bot_iff_le_centralizer.mp hcentral)
  rw [he] at hle
  exact hact (commutator_eq_bot_iff_le_centralizer.mpr (hle.trans inf_le_right))

/-- Normalizer control prevents the outside component from centralizing `Y₊`.
This justifies the nontrivial projection used after the diagonal case. -/
theorem component_action_ne_bot
    {Yplus M I L : Subgroup G} (hLI : L ≤ I) (hL : ¬ L ≤ M)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I) :
    ⁅L, Yplus⁆ ≠ ⊥ := by
  intro hc
  have hLn : L ≤ normalizer (Yplus : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (Subgroup.centralizer_le_normalizer _)
  exact hL ((le_inf hLI hLn).trans (hN.le.trans inf_le_left))

/-- The minimal outside overgroup equals `LS` after `Y₊ ≤ L` is proved.
The nontrivial two-core required for membership of the outside family is
constructed from `O₂(I)`; it is not a separate local-existence premise. -/
theorem eq_component_join_sylow
    {Yplus S M I L : Subgroup G}
    (hI : I ∈ minimalOutsideFamily Yplus S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hLI : L ≤ I) (hYL : Yplus ≤ L) (hL : ¬ L ≤ M) : I = L ⊔ S := by
  have hSI : S ≤ I := le_sup_right.trans hI.1.1.2
  have hJI : L ⊔ S ≤ I := sup_le hLI hSI
  have hcoreS : I.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow I P
  have hcoreJ : I.pCoreIn 2 ≤ (L ⊔ S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hcoreS.trans le_sup_right)
      (hJI.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  have hJ : L ⊔ S ∈ outsideFamily Yplus S M := by
    refine ⟨⟨?_, sup_le_sup hYL le_rfl⟩, ?_⟩
    · intro he
      exact hI.1.1.1 (eq_bot_iff.mpr (he ▸ hcoreJ))
    · intro h
      exact hL (le_sup_left.trans h)
  exact hI.eq_of_ge hJ hJI

end CFSG.Quasithin.Chapter15.Section03.RankOne
