module

public import Theory.SpecificGroups.PSL2.QuinticPrimeQuadraticFusion
public import Theory.SpecificGroups.PSL2.QuinticTwoPerfect
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CenterlessCentralizer
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Whole quintic fusion modulo the full ambient two-core

For B normal in J with J/B a two-group, the image of B in J/O₂(J) is
identified by the literal quotient map with B/O₂(B). Its centerless PSL₂
model makes the ambient centralizer a normal two-subgroup, hence trivial.
The actual two-perfect X has nontrivial image, retains its quintic core
quotient, and becomes an order-five subgroup inside that same PSL₂ model.
Whole-subgroup fusion therefore applies to the actual quotient, with a
conjugator in the actual image of B.

No image model, action kernel, self-centralizer, or quintic-image hypothesis
is supplied separately. This is the full-kernel step in Aschbacher--Smith
6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

private theorem image_quintic_quotient {A D : Type*} [Group A] [Group D]
    [Finite A] [Finite D] (f : A →* D) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 A) (hfive : Nat.card (A ⧸ pCore 2 A) = 5)
    (hne : Nat.card D ≠ 1) : Nat.card (D ⧸ pCore 2 D) = 5 := by
  have hle : (pCore 2 A).map f ≤ pCore 2 D :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 A) (pCore 2 D) f (map_le_iff_le_comap.mp hle)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a, rfl⟩
  have hc : Nat.card (D ⧸ pCore 2 D) ∣ 5 := hfive ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc
  · have ht : pCore 2 D = ⊤ := index_eq_one.mp hc
    have hD : IsPGroup 2 D := pCore_isPGroup.of_surjective
      ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom
      ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
    have hz := hp.hom_eq_one_of_isPGroup hD f
    have hr : (⊤ : Subgroup D) = ⊥ := by
      rw [← f.range_eq_top_of_surjective hf, hz]
      simp
    apply (hne _).elim
    have he := congrArg (fun U : Subgroup D => Nat.card U) hr
    simpa using he
  · exact hc

/-- Whole-subgroup fusion in the literal ambient two-core quotient,
with every structural and quintic-image fact derived from the original inputs. -/
theorem core_quotient_quintic_whole_fusion
    {J : Type*} [Group J] [Finite J]
    (B : Subgroup J) [B.Normal] (hJB : IsPGroup 2 (J ⧸ B))
    {F : Type} [Field F] [Finite F] {p d : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : d = 1 ∨ d = 2) (hF : Nat.card F = p ^ d)
    (hc : 3 < Nat.card F) (e : (B ⧸ pCore 2 B) ≃* PSL(2,F))
    (T : Sylow 2 J) (X : Subgroup J) (hXB : X ≤ B)
    (hXp : IsPPerfect 2 X) (hXfive : Nat.card (X ⧸ pCore 2 X) = 5)
    (hTX : (T : Subgroup J) ≤ normalizer (X : Set J))
    (A : Subgroup (J ⧸ pCore 2 J)) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ ((X.map (QuotientGroup.mk' (pCore 2 J))) ⊔
      ((T : Subgroup J).map (QuotientGroup.mk' (pCore 2 J)))).pCoreIn 2) :
    ∃ g ∈ B.map (QuotientGroup.mk' (pCore 2 J)),
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup J).map (QuotientGroup.mk' (pCore 2 J)) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ ((X.map (QuotientGroup.mk' (pCore 2 J))) ⊔
        ((T : Subgroup J).map (QuotientGroup.mk' (pCore 2 J)))).pCoreIn 2 := by
  let Q := J ⧸ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let N := B.map q
  let Y := X.map q
  let Tbar := T.mapSurjective (f := q) hq
  let : N.Normal := (inferInstance : B.Normal).map q hq
  let eN : N ≃* PSL(2,F) := (coreQuotientEquivImage 2 B).symm.trans e
  have hzN : center N = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr eN ⟨x, hx⟩).property
    change eN x ∈ center PSL(2,F) at he
    rw [psl2_center_eq_bot F, mem_bot] at he
    exact eN.injective (he.trans eN.map_one.symm)
  have hCN : centralizer (N : Set Q) = ⊥ := by
    obtain ⟨m, hm⟩ := hJB.exists_card_eq
    have hidx : N.index ∣ 2 ^ m := (B.index_map_dvd hq).trans (by
      change Nat.card (J ⧸ B) ∣ 2 ^ m
      rw [hm])
    have hCtwo : IsPGroup 2 (centralizer (N : Set Q)) :=
      IsPGroup.of_card_dvd_pow ((centralizer_card_dvd_index_of_center_eq_bot N hzN).trans hidx)
    have hle : centralizer (N : Set Q) ≤ pCore 2 Q := le_sSup ⟨inferInstance, hCtwo⟩
    exact bot_unique (hle.trans_eq (pCore_quotient_pCore_eq_bot 2))
  have hYN : Y ≤ N := map_mono hXB
  have hYp : IsPPerfect 2 Y := hXp.of_surjective (q.subgroupMap X) (q.subgroupMap_surjective X)
  have hYne : Nat.card Y ≠ 1 := by
    intro he
    have hYbot : Y = ⊥ := eq_bot_of_card_eq Y he
    have hXcore : X ≤ pCore 2 J := by
      have hh := (Subgroup.map_eq_bot_iff X).mp hYbot
      rwa [QuotientGroup.ker_mk'] at hh
    have hXtwo : IsPGroup 2 X := pCore_isPGroup.to_le hXcore
    have hi := hXp.hom_eq_one_of_isPGroup hXtwo (MonoidHom.id X)
    have hXbot : X = ⊥ := by
      apply bot_unique
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun hi ⟨x, hx⟩)
    have hXcard : Nat.card X = 1 := by rw [hXbot]; simp
    have hh := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 X))
      (QuotientGroup.mk'_surjective _)
    rw [hXfive, hXcard] at hh
    norm_num at hh
  have hYfive := image_quintic_quotient (q.subgroupMap X) (q.subgroupMap_surjective X)
    hXp hXfive hYne
  let R := (Y.subgroupOf N).map eN.toMonoidHom
  let er : Y ≃* R := (subgroupOfEquivOfLe hYN).symm.trans
    ((Y.subgroupOf N).equivMapOfInjective eN.toMonoidHom eN.injective)
  have hRp : IsPPerfect 2 R := hYp.of_surjective er.toMonoidHom er.surjective
  have hRfive : Nat.card (R ⧸ pCore 2 R) = 5 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).toEquiv]
    exact hYfive
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, d, Fact.out, ho, by rcases hd with h | h <;> omega, hF⟩
  have hYcard : Nat.card Y = 5 := (Nat.card_congr er.toEquiv).trans
    (odd_twoPerfect_quintic_subgroup hodd R hRp hRfive).2
  have hTY : (Tbar : Subgroup Q) ≤ normalizer (Y : Set Q) :=
    (map_mono hTX).trans (X.le_normalizer_map q)
  exact odd_prime_quadratic_quintic_whole_fusion ho hd hF hc N eN hCN
    Tbar Y hYN hYcard hTY A hA hAne hAS

end Theory.PSL2
