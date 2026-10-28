module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreGrowth.Centralizers
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The torus and odd centralizer action in Lemma 15.3

The commuting product K×Y embeds in the original point stabilizer and acts
by conjugation on V. Under the contrary involution hypothesis, every
nonidentity actor has its fixed subgroup inside A. Coprime fixed-point
generation forces this abelian actor to be cyclic when A<V. Thus |Y| is
coprime to q−1. Its free action on V minus A also gives
(q−1)|Y| dividing |V|−q. This is the numerical content of (15C), obtained
on the original group without changing its quotient-action conventions.

Source: GLS IV, Chapter 2, Lemma 15.3, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
open scoped Pointwise
universe u

private theorem cyclic_of_fixed_subgroups_le
    {P B : Type*} [Group P] [Finite P] [CommGroup B] [Finite B]
    [MulDistribMulAction B P] (hP : IsPGroup 2 P) (hodd : Odd (Nat.card B))
    (N : Subgroup P) (hne : N ≠ ⊤)
    (hfix : ∀ b : B, b ≠ 1 → ∀ x : P, b • x = x → x ∈ N) : IsCyclic B := by
  by_contra hncyc
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := P) (A := B) (q := 2) hodd.coprime_two_right
  apply hne
  apply top_unique
  rw [← hgen]
  apply iSup₂_le
  intro Y hY
  have hYne : Y ≠ ⊥ := by
    intro he
    subst Y
    let : IsCyclic (B ⧸ (⊥ : Subgroup B)) := hY
    exact hncyc (isCyclic_of_surjective (QuotientGroup.quotientBot (G := B))
      (QuotientGroup.quotientBot (G := B)).surjective)
  obtain ⟨b, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  intro x hx
  exact hfix b.val (fun he => hbne (Subtype.ext he)) x (hx b)

private theorem card_actor_dvd_complement
    {P B : Type*} [Group P] [Finite P] [Group B] [Finite B]
    [MulDistribMulAction B P] (N : Subgroup P)
    (hinv : ∀ b : B, ∀ x : P, b • x ∈ N ↔ x ∈ N)
    (hfix : ∀ b : B, b ≠ 1 → ∀ x : P, b • x = x → x ∈ N) :
    Nat.card B ∣ Nat.card P - Nat.card N := by
  classical
  let X := {x : P // x ∉ N}
  let : MulAction B X := {
    smul b x := ⟨b • (x : P), fun he => x.property ((hinv b x).mp he)⟩
    one_smul x := Subtype.ext (one_smul B (x : P))
    mul_smul a b x := Subtype.ext (mul_smul a b (x : P)) }
  have hstab (x : X) : MulAction.stabilizer B x = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    by_contra hbne
    exact x.property (hfix b hbne x (congrArg Subtype.val hb))
  have hcount := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd
    (G := B) (X := X) hstab)
  have hXcard : Nat.card X = Nat.card P - Nat.card N := by
    let : Fintype P := Fintype.ofFinite P
    change Nat.card {x : P // ¬ x ∈ N} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, hXcard] at hcount
  exact ⟨Nat.card (Quotient (MulAction.orbitRel B X)), by
    simpa only [Nat.mul_comm] using hcount⟩

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "K" => residualCommutator M t
local notation "J" => centralizer (L : Set G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

public theorem Context.torus_disjoint_centralizer : Disjoint K J := by
  apply disjoint_def.mpr
  intro x hx hj
  by_contra hne
  have hzL : z ∈ L := d.distinguished_le (subset_closure ⟨d.z_mem, d.z_mem_M⟩)
  have hzC : z ∈ centralizerClosure Z x := subset_closure
    ⟨d.z_mem, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hj z hzL)⟩
  rw [d.torus_centralizerClosure_eq_bot hx hne] at hzC
  exact (d.minimal.disconnected.involutions z d.z_mem).ne_one hzC

/-- The coprimality and cardinal consequences of (15C), for every odd cyclic subgroup of J. -/
public theorem Context.torus_centralizer_product_arithmetic
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) (hlt : A < V)
    (Y : Subgroup G) (hYJ : Y ≤ J) (hYcyc : IsCyclic Y) (hYodd : Odd (Nat.card Y)) :
    Nat.Coprime (2 ^ n - 1) (Nat.card Y) ∧
      (2 ^ n - 1) * Nat.card Y ∣ Nat.card V - 2 ^ n := by
  let : IsCyclic K := d.torus_structure.2.1
  let : IsCyclic Y := hYcyc
  let : CommGroup K := IsMulCommutative.instCommGroup
  let : CommGroup Y := IsMulCommutative.instCommGroup
  let B := K × Y
  have hKL : K ≤ L := by rw [d.torus_structure.1]; exact inf_le_right
  have hcomm (k : K) (y : Y) : Commute (k : G) (y : G) :=
    mem_centralizer_iff.mp (hYJ y.property) k (hKL k.property)
  let f : B →* G := (K).subtype.noncommCoprod (Y).subtype hcomm
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨Subtype.val_injective,
      Subtype.val_injective, by
        rw [range_subtype, range_subtype]
        exact d.torus_disjoint_centralizer.mono_right hYJ⟩
  have hfM (b : B) : f b ∈ M := by
    have hkD : (b.1 : G) ∈ residualPairStabilizer M t ⊓ L :=
      d.torus_structure.1 ▸ b.1.property
    exact M.mul_mem hkD.1.1
      (centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M
        (hYJ b.2.property)).1
  have hMV : M ≤ normalizer (V : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 M).le_normalizer_map M.subtype
  let rho : B →* MulAut V := (V).normalizerMonoidHom.comp
    (f.codRestrict (normalizer (V : Set G)) (fun b => hMV (hfM b)))
  let : MulDistribMulAction B V := MulDistribMulAction.compHom V rho
  let N := (A).subgroupOf V
  have hNcard : Nat.card N = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe d.distinguished_le_point_twoCore).toEquiv).trans
      d.distinguished_elementary_card.2
  have hNne : N ≠ ⊤ := by
    intro he
    apply hlt.ne
    have hh := congrArg (Subgroup.map (V).subtype) he
    rw [map_subgroupOf_eq_of_le d.distinguished_le_point_twoCore,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hfix (b : B) (hb : b ≠ 1) (v : V) (hv : b • v = v) : v ∈ N := by
    have he := congrArg Subtype.val hv
    change f b * (v : G) * (f b)⁻¹ = (v : G) at he
    have hc : Commute (v : G) (f b) := (mul_inv_eq_iff_eq_mul.mp he).symm
    exact d.point_twoCore_join_centralizer_le_distinguished hinv Y hYJ
      (mul_mem_sup b.1.property b.2.property)
      (fun h => hb (hf (h.trans f.map_one.symm)))
      ⟨v.property, mem_centralizer_singleton_iff.mpr hc⟩
  have hBodd : Odd (Nat.card B) := by
    rw [Nat.card_prod]
    exact d.torus_odd.mul hYodd
  have hV : IsPGroup 2 V := (pCore_isPGroup (p := 2) (G := M)).map M.subtype
  let : IsCyclic B := cyclic_of_fixed_subgroups_le hV hBodd N hNne hfix
  have hcop := coprime_card_of_isCyclic_prod K Y
  rw [d.torus_structure.2.2.1] at hcop
  refine ⟨hcop, ?_⟩
  have hInv (b : B) (v : V) : b • v ∈ N ↔ v ∈ N := by
    have hbA : f b ∈ normalizer (A : Set G) := by
      rw [distinguishedClosure_normalizer d.minimal.disconnected]
      exact hfM b
    change f b * (v : G) * (f b)⁻¹ ∈ A ↔ (v : G) ∈ A
    exact (mem_normalizer_iff.mp hbA v).symm
  have hd := card_actor_dvd_complement N hInv hfix
  rw [Nat.card_prod, d.torus_structure.2.2.1, hNcard] at hd
  exact hd

/-- Every odd prime divisor of J avoids q−1 under the contrary source hypothesis. -/
public theorem Context.centralizer_coprime_split_of_involutions
    (hinv : ∀ v ∈ V, PFAppendixIII.IsInvolution v → v ∈ A) (hlt : A < V) :
    Nat.Coprime (Nat.card J) (2 ^ n - 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpJ hpK
  have hpodd := d.torus_odd.of_dvd_nat (d.torus_structure.2.2.1.symm ▸ hpK)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  have hyG : orderOf (y : G) = p := (orderOf_coe y).trans hy
  have hc := (d.torus_centralizer_product_arithmetic hinv hlt (zpowers (y : G))
    (zpowers_le.mpr y.property) inferInstance (by rw [Nat.card_zpowers, hyG]; exact hpodd)).1
  rw [Nat.card_zpowers, hyG] at hc
  exact hp.not_dvd_one (by simpa only [hc] using Nat.dvd_gcd hpK (dvd_refl p))

end BenderSuzuki.ZD.LinearExclusion
