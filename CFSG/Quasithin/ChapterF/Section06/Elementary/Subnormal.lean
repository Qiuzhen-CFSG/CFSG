module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Intersections
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PGroup.Subnormal
public import Theory.GroupTheory.PPerfectHom

/-!
# Subnormal intersections in a Goldschmidt triple

For either generator `Gᵢ`, its intersection with a subnormal subgroup `X`
lies in `O₂(Gᵢ)` exactly when the embedded `O²(Gᵢ)` is not contained in `X`.
Together with the Sylow intersection theorem, this gives all three equivalent
conditions of Lemma F.6.7, with the common Sylow subgroup `T = G₁ ∩ G₂`.

The local argument uses the actual quotient isomorphism `Gᵢ/O₂(Gᵢ) ≃ S₃`.
A nontrivial subnormal image in `S₃` has order divisible by three: otherwise
it is a subnormal two-subgroup and lies in the trivial two-core. Consequently
an intersection outside `O₂(Gᵢ)` has index a power of two in `Gᵢ`. Induction
along its subnormal chain places every two-perfect subgroup, in particular
`O²(Gᵢ)`, in that intersection. Conversely, `O²(Gᵢ)` cannot lie in the
two-core, since this would make the quotient `S₃` a two-group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.7, printed p.305 (PDF p.316, 1 March 2004 manuscript).
-/

open Subgroup

/-- A subnormal subgroup of p-power index contains every p-perfect subgroup. -/
private theorem pPerfect_le_subnormal_of_index
    {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    (L N : Subgroup H) (hL : IsPPerfect p L) (hN : N.IsSubnormal) :
    (∃ n, N.index ∣ p ^ n) → L ≤ N := by
  induction hN with
  | top => intro _; exact le_top
  | step N K hNK _ hnormal ih =>
    rintro ⟨n, hn⟩
    have hLK : L ≤ K := ih ⟨n, (index_dvd_of_le hNK).trans hn⟩
    let := hnormal
    have hp : IsPGroup p (K ⧸ N.subgroupOf K) :=
      IsPGroup.of_card_dvd_pow ((relIndex_dvd_index_of_le hNK).trans hn)
    have hf := hL.hom_eq_one_of_isPGroup hp
      ((QuotientGroup.mk' (N.subgroupOf K)).comp (inclusion hLK))
    intro x hx
    exact (QuotientGroup.eq_one_iff (inclusion hLK ⟨x, hx⟩)).mp
      (congrArg (fun f => f ⟨x, hx⟩) hf)

private theorem perm_three_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- Nontrivial subnormal images in the local symmetric quotient retain its three-part. -/
private theorem three_dvd_card_subnormal_perm_three
    (N : Subgroup (Equiv.Perm (Fin 3))) (hN : N.IsSubnormal) (hne : N ≠ ⊥) :
    3 ∣ Nat.card N := by
  by_contra hn
  have hcop : (Nat.card N).Coprime 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hn).symm
  have hdiv : Nat.card N ∣ 6 := by
    simpa only [perm_three_card] using N.card_subgroup_dvd_card
  have hd : Nat.card N ∣ 2 := hcop.dvd_mul_right.mp hdiv
  have hp : IsPGroup 2 N := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)
  have hcore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa using hh.symm
  have hle := isPGroup_le_pCoreAmbient_of_isSubnormalIn
    (⊤ : Subgroup (Equiv.Perm (Fin 3))) N 2 le_top hN.subgroupOf hp
  change N ≤ (pCore 2 (⊤ : Subgroup (Equiv.Perm (Fin 3)))).map
    Subgroup.topEquiv.toMonoidHom at hle
  rw [pCore_map_iso, hcore] at hle
  exact hne (le_bot_iff.mp hle)

/-- Escaping the two-core forces the index to be a power of two. -/
private theorem local_subnormal_index
    {H : Type*} [Group H] [Finite H]
    (e : H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 3))
    (N : Subgroup H) (hN : N.IsSubnormal) (hnot : ¬ N ≤ pCore 2 H) :
    ∃ n, N.index ∣ 2 ^ n := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hne : N.map f ≠ ⊥ := by
    intro hz
    exact hnot (hk ▸ (map_eq_bot_iff N).mp hz)
  have hthree : 3 ∣ Nat.card N :=
    (three_dvd_card_subnormal_perm_three (N.map f) (hN.map hf) hne).trans (N.card_map_dvd f)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hquot : (pCore 2 H).index = 6 := (Nat.card_congr e.toEquiv).trans perm_three_card
  have hcard : Nat.card H = 3 * 2 ^ (n + 1) := by
    rw [← (pCore 2 H).index_mul_card, hquot, hn, pow_succ]
    ring
  obtain ⟨k, hk⟩ := hthree
  refine ⟨n + 1, k, ?_⟩
  have he := N.index_mul_card
  rw [hk, hcard] at he
  have he' : 3 * (N.index * k) = 3 * 2 ^ (n + 1) := by nlinarith [he]
  exact (Nat.mul_left_cancel (by decide : 0 < 3) he').symm

private theorem local_residual_not_le_core
    {H : Type*} [Group H] [Finite H]
    (e : H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 3)) :
    ¬ pResidual 2 H ≤ pCore 2 H := by
  intro hle
  let q := QuotientGroup.map (pResidual 2 H) (pCore 2 H) (MonoidHom.id H)
    (show pResidual 2 H ≤ (pCore 2 H).comap (MonoidHom.id H) from hle)
  have hq : Function.Surjective q := QuotientGroup.map_surjective_of_surjective
    (pResidual 2 H) (pCore 2 H) (MonoidHom.id H) (QuotientGroup.mk'_surjective _) _
  have hp : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
    ((isPGroup_quotient_pResidual 2).of_surjective q hq).of_equiv e
  have hc : (Nat.card (Equiv.Perm (Fin 3))).Coprime 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  rw [perm_three_card] at hc
  norm_num at hc

private theorem local_subnormal_iff
    {H : Type*} [Group H] [Finite H]
    (e : H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 3))
    (N : Subgroup H) (hN : N.IsSubnormal) :
    N ≤ pCore 2 H ↔ ¬ pResidual 2 H ≤ N := by
  constructor
  · intro hle hres
    exact local_residual_not_le_core e (hres.trans hle)
  · intro hnot
    by_contra hn
    exact hnot (pPerfect_le_subnormal_of_index (pResidual 2 H) N
      (isPPerfect_pResidual 2) hN (local_subnormal_index e N hN hn))

namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Conditions (1) and (3) of F.6.7 for the first generator. -/
public theorem IsGoldschmidtTriple.left_subnormal_core_iff_not_residual_le
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) (hX : X.IsSubnormal) :
    (G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype) ↔
      ¬ (pResidual 2 G₁).map G₁.subtype ≤ X := by
  obtain ⟨e⟩ := h.quotient_left
  have hc : (G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype) ↔
      X.subgroupOf G₁ ≤ pCore 2 G₁ := by
    rw [inf_comm G₁ X, ← subgroupOf_map_subtype,
      map_le_map_iff_of_injective G₁.subtype_injective]
  rw [hc, map_le_iff_le_comap]
  exact local_subnormal_iff e (X.subgroupOf G₁) hX.subgroupOf

/-- Conditions (1) and (3) of F.6.7 for the second generator. -/
public theorem IsGoldschmidtTriple.right_subnormal_core_iff_not_residual_le
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) (hX : X.IsSubnormal) :
    (G₂ ⊓ X ≤ (pCore 2 G₂).map G₂.subtype) ↔
      ¬ (pResidual 2 G₂).map G₂.subtype ≤ X :=
  h.symm.left_subnormal_core_iff_not_residual_le X hX

/-- Lemma F.6.7, all three equivalences for either generating subgroup.
The Sylow subgroup is expressed inside `X` through the actual subtype map. -/
public theorem source_lemma_F_6_7
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) (hX : X.IsSubnormal)
    (I : Subgroup G) (hI : I = G₁ ∨ I = G₂) :
    List.TFAE [
      I ⊓ X ≤ (pCore 2 I).map I.subtype,
      I ⊓ X = (pCore 2 I).map I.subtype ⊓ X ∧
        (pCore 2 I).map I.subtype ⊓ X = (G₁ ⊓ G₂) ⊓ X ∧
        ∃ S : Sylow 2 X, (S : Subgroup X) = (G₁ ⊓ G₂).subgroupOf X,
      ¬ (pResidual 2 I).map I.subtype ≤ X] := by
  have hab : (I ⊓ X ≤ (pCore 2 I).map I.subtype) ↔
      (I ⊓ X = (pCore 2 I).map I.subtype ⊓ X ∧
        (pCore 2 I).map I.subtype ⊓ X = (G₁ ⊓ G₂) ⊓ X ∧
        ∃ S : Sylow 2 X, (S : Subgroup X) = (G₁ ⊓ G₂).subgroupOf X) := by
    rcases hI with rfl | rfl
    · exact h.left_subnormal_intersection_iff X hX
    · simpa only [inf_comm I G₁] using h.symm.left_subnormal_intersection_iff X hX
  have hac : (I ⊓ X ≤ (pCore 2 I).map I.subtype) ↔
      ¬ (pResidual 2 I).map I.subtype ≤ X := by
    rcases hI with rfl | rfl
    · exact h.left_subnormal_core_iff_not_residual_le X hX
    · exact h.right_subnormal_core_iff_not_residual_le X hX
  simp only [List.tfae_cons_cons, List.tfae_singleton, and_true]
  exact ⟨hab, hab.symm.trans hac⟩
end CFSG.Quasithin.ChapterF
