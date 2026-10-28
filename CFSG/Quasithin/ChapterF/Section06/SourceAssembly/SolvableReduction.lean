module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SolvableReduction.Cover
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.PStar.ExtensionCentralSylow
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The solvable Goldschmidt reduction F.6.9

Let X centralize O³(F(G)). The genuine SQTK cover makes every q-subgroup,
for q outside {2,3}, centralize O₃(G). A Sylow q-subgroup of X therefore
centralizes F(G); Fitting self-centralization puts it in F(G), and coprime
torsion puts it in O³(F(G)). It is consequently central in X. Transfer
makes Oᑫ(X) prime to q. This characteristic residual contains the supplied
local two-residual and is normal in G. Its product with the opposite local
group is G, excluding q from the order of G.

The argument applies prime by prime and retains the original SQTK
surjection. It replaces the printed Hall-subgroup choice by central-Sylow
transfer while proving the same complete assertion.

Source: Aschbacher--Smith, F.6.9, printed p.306,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Both original local groups have no prime divisors outside {2,3}. -/
theorem local_isTwoThreeGroup (h : IsGoldschmidtTriple G₁ G₂) :
    IsPiGroup twoThreePrimes G₁ := by
  apply (IsPiGroup_iff _ _).mpr
  intro q hq
  have hc : (pCore 2 G₁).index = 6 := by
    rw [index_eq_card, Nat.card_congr h.quotient_left.some.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G₁)).exists_card_eq
  rw [← (pCore 2 G₁).index_mul_card, hc, hn] at hq
  rcases q.property.dvd_mul.mp hq with hs | hs
  · have hh : q.val ∣ 2 ∨ q.val ∣ 3 := q.property.dvd_mul.mp hs
    exact hh.imp (fun h => (Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp h)
      (fun h => (Nat.prime_dvd_prime_iff_eq q.property Nat.prime_three).mp h)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
      (q.property.dvd_of_dvd_pow hs))

omit [Finite G] in
private theorem prime_subgroup_le_fitting_residual
    {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (A : Subgroup G) (hA : IsPGroup q A) (hAF : A ≤ fittingSubgroup G) :
    A ≤ (pResidual 3 (fittingSubgroup G)).map (fittingSubgroup G).subtype := by
  intro a ha
  let b : fittingSubgroup G := ⟨a, hAF ha⟩
  have hb : b ∈ pResidual 3 (fittingSubgroup G) := by
    apply mem_pResidual_of_orderOf_coprime
    obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
    have hbpow : b ^ (q ^ n) = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) hn
    exact (((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3)).pow_right n).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hbpow)
  exact mem_map_of_mem (fittingSubgroup G).subtype hb

private theorem centralizes_fitting_of_two_parts
    (A : Subgroup G)
    (hR : A ≤ centralizer ((pResidual 3 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype : Set G))
    (hP : A ≤ centralizer (pCore 3 G : Set G)) :
    A ≤ centralizer (fittingSubgroup G : Set G) := by
  let S : Sylow 3 (fittingSubgroup G) := Classical.choice inferInstance
  have hS : (S : Subgroup (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤ pCore 3 G :=
    Sylow.map_le_pCore inferInstance inferInstance 3 S
  have he := congrArg (Subgroup.map (fittingSubgroup G).subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  apply le_centralizer_iff.mpr
  rw [← he]
  exact sup_le (le_centralizer_iff.mp hR) (hS.trans (le_centralizer_iff.mp hP))

omit [Finite G] in
private theorem subgroup_le_prime_residual_of_coprime
    {q : ℕ} (hq : q.Prime) (L X : Subgroup G) (hLX : L ≤ X)
    (hcop : Nat.Coprime q (Nat.card L)) :
    L ≤ (pResidual q X).map X.subtype := by
  intro x hx
  let a : X := ⟨x, hLX hx⟩
  have ha : a ∈ pResidual q X := by
    let : Fact q.Prime := ⟨hq⟩
    apply mem_pResidual_of_orderOf_coprime
    apply hcop.of_dvd_right
    simpa only [a, orderOf_mk] using orderOf_dvd_natCard (⟨x, hx⟩ : L)
  exact mem_map_of_mem X.subtype ha

variable {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}

/-- The left-hand alternative of the literal F.6.9 centralization hypothesis. -/
theorem isTwoThreeGroup_of_left_residual_centralizes_fitting_residual
    (hH : IsSQTK K H) (f : H →* G) (hf : Function.Surjective f)
    (hsolv : Group.IsSolvable G) (h : IsGoldschmidtTriple G₁ G₂)
    (hc : (pResidual 2 G₁).map G₁.subtype ≤
      centralizer ((pResidual 3 (fittingSubgroup G)).map
        (fittingSubgroup G).subtype : Set G)) :
    IsPiGroup twoThreePrimes G := by
  apply (IsPiGroup_iff _ _).mpr
  intro q hqdiv
  by_contra hq23
  have hq2 : q.val ≠ 2 := fun he => hq23 (Or.inl he)
  have hq3 : q.val ≠ 3 := fun he => hq23 (Or.inr he)
  let : Fact q.val.Prime := ⟨q.property⟩
  let R := (pResidual 3 (fittingSubgroup G)).map (fittingSubgroup G).subtype
  let X := centralizer (R : Set G)
  let S : Sylow q.val X := Classical.choice inferInstance
  let A := (S : Subgroup X).map X.subtype
  have hA : IsPGroup q.val A := S.isPGroup'.map X.subtype
  have hAc : A ≤ centralizer (pCore 3 G : Set G) :=
    prime_subgroup_centralizes_three_core_of_sqtk_cover hH f hf q.property hq2 hq3 A hA
  have hAF : A ≤ fittingSubgroup G :=
    (centralizes_fitting_of_two_parts A (map_subtype_le _) hAc).trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hAR : A ≤ R := prime_subgroup_le_fitting_residual q.property hq3 A hA hAF
  have hScentral : (S : Subgroup X) ≤ center X := by
    intro s hs
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext ((x.property s.val (hAR (mem_map_of_mem X.subtype hs))).symm)
  have hcop := coprime_card_pResidual_of_central_sylow S hScentral
  let N := (pResidual q.val X).map X.subtype
  have hN : ¬ q.val ∣ Nat.card N := by
    have he : Nat.card N = Nat.card (pResidual q.val X) :=
      Nat.card_congr (equivMapOfInjective _ X.subtype X.subtype_injective).symm.toEquiv
    rw [he]
    exact q.property.coprime_iff_not_dvd.mp hcop
  have hG₁ : ¬ q.val ∣ Nat.card G₁ := fun hd =>
    hq23 ((IsPiGroup_iff _ _).mp (local_isTwoThreeGroup h) q hd)
  have hG₂ : ¬ q.val ∣ Nat.card G₂ := fun hd =>
    hq23 ((IsPiGroup_iff _ _).mp (local_isTwoThreeGroup h.symm) q hd)
  have hL : (pResidual 2 G₁).map G₁.subtype ≤ N := by
    apply subgroup_le_prime_residual_of_coprime q.property _ X hc
    apply q.property.coprime_iff_not_dvd.mpr
    intro hd
    exact hG₁ (hd.trans (by
      rw [Nat.card_congr (equivMapOfInjective (pResidual 2 G₁)
        G₁.subtype G₁.subtype_injective).symm.toEquiv]
      exact card_subgroup_dvd_card _))
  have hgen : N ⊔ G₂ = ⊤ := top_unique (h.left_residual_sup_right ▸ sup_le_sup_right hL G₂)
  have hcard : Nat.card (N ⊓ G₂ : Subgroup G) * Nat.card (N ⊔ G₂ : Subgroup G) =
      Nat.card N * Nat.card G₂ :=
    (card_mul_eq_card_inf_mul_card_sup_of_normalizes N G₂ le_normalizer_of_normal).symm
  have hd : q.val ∣ Nat.card N * Nat.card G₂ := by
    rw [← hcard, hgen, card_top]
    exact dvd_mul_of_dvd_right hqdiv _
  exact (q.property.dvd_mul.mp hd).elim hN hG₂

/-- F.6.9: a solvable SQTK quotient with either stated local centralization
hypothesis is a {2,3}-group. The original quotient map is retained. -/
theorem source_lemma_F_6_9
    (hH : IsSQTK K H) (f : H →* G) (hf : Function.Surjective f)
    (hsolv : Group.IsSolvable G) (h : IsGoldschmidtTriple G₁ G₂)
    (hc : (pResidual 2 G₁).map G₁.subtype ≤
        centralizer ((pResidual 3 (fittingSubgroup G)).map
          (fittingSubgroup G).subtype : Set G) ∨
      (pResidual 2 G₂).map G₂.subtype ≤
        centralizer ((pResidual 3 (fittingSubgroup G)).map
          (fittingSubgroup G).subtype : Set G)) :
    IsPiGroup twoThreePrimes G := by
  rcases hc with hc | hc
  · exact isTwoThreeGroup_of_left_residual_centralizes_fitting_residual hH f hf hsolv h hc
  · exact isTwoThreeGroup_of_left_residual_centralizes_fitting_residual hH f hf hsolv h.symm hc

end CFSG.Quasithin.ChapterF.SourceAssembly
