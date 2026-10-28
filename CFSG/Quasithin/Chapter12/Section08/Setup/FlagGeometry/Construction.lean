module

public import Theory.GroupTheory.PrimeRankElementary
public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.MarkedGeneration

/-!
# Constructing the invariant flag from the original Sylow action

Transport the image of T under the flag-independent LT action to a Sylow
of the full binary linear group. Its complete flag stabilizer supplies
all initial subspaces. Pulling them back to the original V constructs the
flag; reconstruction of invariant subspaces and their dimensions proves
uniqueness, including the zero and terminal members. The elementary order
also recovers the source two-rank, and the first cut has its ambient generator.
No flag, uniqueness, or local source conclusion is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation 12.8.2 and
Lemma 12.8.3, printed pp.849–850 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] {V : Subgroup G}
  [IsElementaryAbelian 2 V] {m : ℕ}

private noncomputable def seedCoordinates [Finite G] (hc : Nat.card V = 2 ^ (m + 1)) :
    Additive V ≃ₗ[ZMod 2] Space (m + 1) := by
  have hd : Module.finrank (ZMod 2) (Additive V) = m + 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    exact (h.trans (by rw [Nat.card_zmod])).symm.trans hc
  exact (Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hd).equivFun

private noncomputable def seedSpace (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (A : Subgroup G) : Submodule (ZMod 2) (Space (m + 1)) :=
  ((AddSubgroup.toZModSubmodule 2) (A.subgroupOf V).toAddSubgroup).map β.toLinearMap

private theorem mem_seedSpace (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (A : Subgroup G) (v : V) :
    β (Additive.ofMul v) ∈ seedSpace β A ↔ (v : G) ∈ A := by
  rw [seedSpace, Submodule.mem_map_equiv, β.symm_apply_apply]
  rfl

private noncomputable def seedSubgroup (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (W : Submodule (ZMod 2) (Space (m + 1))) : Subgroup G :=
  ((W.comap β.toLinearMap).toAddSubgroup.toSubgroup).map V.subtype

private theorem seedSubgroup_le (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (W : Submodule (ZMod 2) (Space (m + 1))) : seedSubgroup β W ≤ V :=
  map_subtype_le _

private theorem mem_seedSubgroup (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (W : Submodule (ZMod 2) (Space (m + 1))) (v : V) :
    (v : G) ∈ seedSubgroup β W ↔ β (Additive.ofMul v) ∈ W := by
  change (∃ w : V, β (Additive.ofMul w) ∈ W ∧ (w : G) = v) ↔ _
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem seedSpace_seedSubgroup (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (W : Submodule (ZMod 2) (Space (m + 1))) : seedSpace β (seedSubgroup β W) = W := by
  ext w
  obtain ⟨v, rfl⟩ := β.surjective w
  exact (mem_seedSpace β _ v.toMul).trans (mem_seedSubgroup β W v.toMul)

private theorem seedSpace_injective (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    {A B : Subgroup G} (hA : A ≤ V) (hB : B ≤ V)
    (he : seedSpace β A = seedSpace β B) : A = B := by
  apply le_antisymm
  · intro a ha
    exact (mem_seedSpace β B ⟨a, hA ha⟩).mp (he ▸ (mem_seedSpace β A ⟨a, hA ha⟩).mpr ha)
  · intro b hb
    exact (mem_seedSpace β A ⟨b, hB hb⟩).mp (he.symm ▸ (mem_seedSpace β B ⟨b, hB hb⟩).mpr hb)

private theorem seedSpace_card (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    {A : Subgroup G} (hA : A ≤ V) : Nat.card (seedSpace β A) = Nat.card A := by
  let W := (AddSubgroup.toZModSubmodule 2) (A.subgroupOf V).toAddSubgroup
  calc
    Nat.card (seedSpace β A) = Nat.card W :=
      Nat.card_congr (W.equivMapOfInjective β.toLinearMap β.injective).toEquiv.symm
    _ = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv

private theorem seedSubgroup_card (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (W : Submodule (ZMod 2) (Space (m + 1))) : Nat.card (seedSubgroup β W) = Nat.card W := by
  rw [← seedSpace_card β (seedSubgroup_le β W), seedSpace_seedSubgroup]

private noncomputable def initialSpace (b : Basis m) (i : ℕ) :
    Submodule (ZMod 2) (Space (m + 1)) :=
  Submodule.span (ZMod 2) (b '' {j : Fin (m + 1) | j.val < i})

private theorem initialSpace_mono (b : Basis m) : Monotone (initialSpace b) := by
  intro i j hij
  exact Submodule.span_mono (Set.image_mono (fun _ hk => Nat.lt_of_lt_of_le hk hij))

private theorem initialSpace_cut (b : Basis m) (i : Fin m) :
    initialSpace b (i.val + 1) = cutSpace b i := by
  unfold initialSpace cutSpace
  congr 2
  ext j
  exact Nat.lt_succ_iff

private theorem initialSpace_last (b : Basis m) : initialSpace b (m + 1) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
  intro j
  exact Submodule.subset_span ⟨j, j.isLt, rfl⟩

private theorem initialSpace_finrank (b : Basis m) (i : ℕ) (hi : i ≤ m + 1) :
    Module.finrank (ZMod 2) (initialSpace b i) = i := by
  classical
  have he : b '' {j : Fin (m + 1) | j.val < i} =
      Set.range (fun j : {j : Fin (m + 1) // j.val < i} => b j.val) := by
    ext x
    simp
  have hlin : LinearIndependent (ZMod 2)
      (fun j : {j : Fin (m + 1) // j.val < i} => b j.val) :=
    b.linearIndependent.comp _ Subtype.val_injective
  let e : {j : Fin (m + 1) // j.val < i} ≃ Fin i :=
    { toFun := fun j => ⟨j.val.val, j.property⟩
      invFun := fun j => ⟨⟨j.val, by omega⟩, j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [initialSpace, he, finrank_span_eq_card hlin, Fintype.card_congr e, Fintype.card_fin]

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry

namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open scoped IsMulCommutative
variable {G : Type*} [Group G] {V : Subgroup G}
  [IsElementaryAbelian 2 V] {m : ℕ}

private theorem seedAction_mem_parabolic
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
    (J : Subgroup G) (hJV : J ≤ normalizer (V : Set G))
    (A : Subgroup G) (hA : A ≤ V) (x : J) :
    InvariantFlag.naturalFlagActorEquiv β (setupSeedAction J V hJV x) ∈
      parabolic (seedSpace β A) ↔ (x : G) ∈ normalizer (A : Set G) := by
  let a := setupSeedAction J V hJV x
  have hc (v : V) :
      InvariantFlag.naturalFlagActorEquiv β a (β (Additive.ofMul v)) ∈ seedSpace β A ↔
        (a v : G) ∈ A := by
    rw [InvariantFlag.naturalFlagActorEquiv_intertwines, mem_seedSpace]
  constructor
  · intro hx
    rw [mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact (hc ⟨v, hA hv⟩).mp ((hx _).mpr ((mem_seedSpace β A _).mpr hv))
    · intro hv
      have hvV : v ∈ V := (mem_normalizer_iff.mp (hJV x.property) v).mpr (hA hv)
      exact (mem_seedSpace β A ⟨v, hvV⟩).mp ((hx _).mp ((hc ⟨v, hvV⟩).mpr hv))
  · intro hx w
    obtain ⟨v, rfl⟩ := β.surjective w
    exact (hc v.toMul).trans ((mem_normalizer_iff.mp hx _).symm.trans
      (mem_seedSpace β A v.toMul).symm)

private theorem initialSpace_stable (b : Basis m) (i : ℕ) :
    cutStabilizer b Set.univ ≤ parabolic (initialSpace b i) := by
  by_cases hi0 : i = 0
  · subst i
    have he : initialSpace b 0 = ⊥ := Submodule.finrank_eq_zero.mp
      (initialSpace_finrank b 0 (Nat.zero_le _))
    rw [he]
    intro a ha v
    simp
  by_cases hin : m + 1 ≤ i
  · have he : initialSpace b i = ⊤ := top_unique (by
      rw [← initialSpace_last b]
      exact initialSpace_mono b hin)
    rw [he]
    intro a ha v
    simp
  · let j : Fin m := ⟨i - 1, by omega⟩
    have hj : j.val + 1 = i := by dsimp [j]; omega
    rw [← hj, initialSpace_cut]
    intro a ha
    exact (mem_cutStabilizer b Set.univ a).mp ha j (Set.mem_univ _)

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry

namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V] {m : ℕ}

/-- Construct a complete flag from the full image of the original Sylow. -/
private noncomputable def flagOfSylowCoordinates
    (hLV : L ≤ normalizer (V : Set G)) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (b : Basis m)
    (hT : ∀ x : (L ⊔ (T : Subgroup G) : Subgroup G), (x : G) ∈ T →
      InvariantFlag.naturalFlagActorEquiv β
        (setupSeedAction _ V (sup_le hLV hTV) x) ∈ cutStabilizer b Set.univ) :
    InvariantFlag T V (m + 1) where
  Vi i := seedSubgroup β (initialSpace b i)
  le_seed i := seedSubgroup_le β _
  monotone := by
    intro i j hij x hx
    have hxV := seedSubgroup_le β _ hx
    apply (mem_seedSubgroup β _ ⟨x, hxV⟩).mpr
    exact initialSpace_mono b hij ((mem_seedSubgroup β _ ⟨x, hxV⟩).mp hx)
  card i hi := by
    rw [seedSubgroup_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, initialSpace_finrank b i hi]
  last := by
    rw [initialSpace_last]
    apply le_antisymm (seedSubgroup_le β _)
    intro v hv
    exact (mem_seedSubgroup β _ ⟨v, hv⟩).mpr (Submodule.mem_top)
  invariant i := by
    intro t ht
    let x : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht⟩
    apply (seedAction_mem_parabolic β _ (sup_le hLV hTV) _ (seedSubgroup_le β _) x).mp
    rw [seedSpace_seedSubgroup]
    exact initialSpace_stable b i (hT x ht)

/-- The original Sylow image constructs the flag and proves uniqueness in
all dimensions. No flag or uniqueness assumption occurs among the inputs. -/
theorem exists_marked_flag
    (hc : Nat.card V = 2 ^ (m + 1))
    (hLV : L ≤ normalizer (V : Set G)) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V (sup_le hLV hTV))) :
    ∃ (F : InvariantFlag T V (m + 1))
      (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (b : Basis m),
      (∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i) ∧
      ∀ i, i ≤ m + 1 → ∀ A : Subgroup G, A ≤ V → Nat.card A = 2 ^ i →
        (T : Subgroup G) ≤ normalizer (A : Set G) → A = F.Vi i := by
  let β := seedCoordinates hc
  let e := InvariantFlag.naturalFlagActorEquiv β
  let f := setupSeedAction (L ⊔ (T : Subgroup G)) V (sup_le hLV hTV)
  let S := ((T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    hfull).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer S
  have hT (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (hx : (x : G) ∈ T) :
      e (f x) ∈ cutStabilizer b Set.univ := by
    rw [← hb]
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  let F := flagOfSylowCoordinates hLV hTV β b hT
  have hspace (i : ℕ) : seedSpace β (F.Vi i) = initialSpace b i :=
    seedSpace_seedSubgroup β _
  refine ⟨F, β, b, ?_, ?_⟩
  · intro i
    exact (hspace (i.val + 1)).trans (initialSpace_cut b i)
  · intro i hi A hA hcard hnorm
    have hd : Module.finrank (ZMod 2) (seedSpace β A) = i := by
      apply Nat.pow_right_injective (by decide : 1 < 2)
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := seedSpace β A)
      rw [Nat.card_zmod, seedSpace_card β hA, hcard] at hh
      exact hh.symm
    apply seedSpace_injective β hA (F.le_seed i)
    rw [hspace]
    by_cases hi0 : i = 0
    · rw [hi0] at hd ⊢
      exact (Submodule.finrank_eq_zero.mp hd).trans
        (Submodule.finrank_eq_zero.mp (initialSpace_finrank b 0 (Nat.zero_le _))).symm
    by_cases hin : i = m + 1
    · rw [hin] at hd ⊢
      rw [initialSpace_last]
      apply Submodule.eq_top_of_finrank_eq
      simpa only [Module.finrank_fin_fun] using hd
    have h0 : seedSpace β A ≠ ⊥ := by
      intro he
      rw [he, finrank_bot] at hd
      omega
    have h1 : seedSpace β A ≠ ⊤ := by
      intro he
      rw [he, finrank_top, Module.finrank_fin_fun] at hd
      omega
    have hstable : cutStabilizer b Set.univ ≤ parabolic (seedSpace β A) := by
      rw [← hb]
      rintro a ⟨c, ⟨x, hx, rfl⟩, rfl⟩
      exact (seedAction_mem_parabolic β _ (sup_le hLV hTV) A hA x).mpr (hnorm hx)
    obtain ⟨j, hj⟩ := fullFlag_invariant_subspace b _ h0 h1 hstable
    have hji : j.val + 1 = i := by
      rw [hj, cutSpace_finrank] at hd
      exact hd
    rw [← hji, initialSpace_cut]
    exact hj

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry

namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- For the actual elementary seed, its source two-rank is its binary dimension. -/
theorem primeRank_eq_of_card [IsElementaryAbelian 2 V] (hc : Nat.card V = 2 ^ n) :
    primeRank 2 V = n := by
  apply le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le V hc.le)
  have htE : IsElementaryAbelian 2 (⊤ : Subgroup V) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) x.val) }
  have hh := (primeRank_le_iff_elementary_card_le V).mp (le_refl (primeRank 2 V))
    (⊤ : Subgroup V) htE
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv, hc] at hh
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh

omit [Finite G] in
/-- The first cut has a nonidentity generator in the original ambient group. -/
theorem exists_point_generator (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    ∃ z : G, z ≠ 1 ∧ F.Vi 1 = zpowers z := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have hne : F.Vi 1 ≠ ⊥ := by intro he; simp [he] at hc
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he := zpowers_eq_top_of_prime_card hc hz
  have hm := congrArg (fun A : Subgroup (F.Vi 1) => A.map (F.Vi 1).subtype) he
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact ⟨z, fun h => hz (Subtype.ext h), hm.symm⟩

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
