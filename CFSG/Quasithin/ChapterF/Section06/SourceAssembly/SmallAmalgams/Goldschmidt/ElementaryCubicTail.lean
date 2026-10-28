module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.Perm

/-!
# The elementary direct-product tail of Goldschmidt's cubic lemma

For `G ≃ S₃ × E`, the actual central factor lies in every Sylow two-subgroup
with index two. Its three images under a cubic Sylow automorphism have trivial
intersection: this intersection is both invariant and normal in the original
ambient group. The product of their indices bounds the Sylow order by eight.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), final paragraph
of Lemma (2.15), pp.385--386.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

private theorem central_index_six_cubic_bound {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (Z : Subgroup G) [Z.Normal] (hZ : IsPGroup 2 Z)
    (hZcentral : Z ≤ center G) (hZindex : Z.index = 6)
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    Nat.card P ≤ 8 ∧ Nat.card Z ≤ 4 := by
  classical
  let C := Z.subgroupOf (P : Subgroup G)
  have hZP : Z ≤ P := hZ.le_sylow_of_normal P
  have hproduct : C.index * P.index = 6 :=
    (relIndex_mul_index hZP).trans hZindex
  have hCindex : C.index = 2 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.index C
    have hd : C.index ∣ 6 := ⟨P.index, hproduct.symm⟩
    have hc : C.index.Coprime 3 := by
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    have hd2 : C.index ∣ 2 := hc.dvd_of_dvd_mul_right (by simpa using hd)
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2 with h1 | h2
    · have hPi : P.index = 6 := by simpa [h1] using hproduct
      exact (P.not_dvd_index (by simp [hPi])).elim
    · exact h2
  let C1 := C.map a.toMonoidHom
  let C2 := C1.map a.toMonoidHom
  let T := C ⊓ C1 ⊓ C2
  have hcycle (x : P) : a (a (a x)) = x := by
    simpa [pow_succ, MulAut.mul_apply] using DFunLike.congr_fun ha x
  have hC3 : C2.map a.toMonoidHom = C := by
    apply le_antisymm
    · rintro x ⟨y, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      change a (a (a w)) ∈ C
      rw [hcycle]
      exact hw
    · intro x hx
      refine ⟨a (a x), ⟨a x, ⟨x, hx, rfl⟩, rfl⟩, hcycle x⟩
  have hTinvariant : T.map a.toMonoidHom = T := by
    rw [map_inf _ _ _ a.injective, map_inf _ _ _ a.injective]
    change (C1 ⊓ C2) ⊓ C2.map a.toMonoidHom = T
    rw [hC3]
    simp [T, inf_assoc, inf_comm]
  have hTcentral : T.map (P : Subgroup G).subtype ≤ center G := by
    rintro x ⟨y, hy, rfl⟩
    exact hZcentral hy.1.1
  have hTnormal : (T.map (P : Subgroup G).subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc := mem_center_iff.mp (hTcentral hx) g
    simpa [hc, mul_assoc] using hx
  have hT : T = ⊥ := hno T hTinvariant hTnormal
  have hC1index : C1.index = 2 := (C.index_map_equiv a).trans hCindex
  have hC2index : C2.index = 2 := (C1.index_map_equiv a).trans hC1index
  have hPcard : Nat.card P ≤ 8 := calc
    Nat.card P = (⊥ : Subgroup P).index := index_bot.symm
    _ = T.index := congrArg Subgroup.index hT.symm
    _ ≤ (C ⊓ C1).index * C2.index := index_inf_le
    _ ≤ (C.index * C1.index) * C2.index :=
      Nat.mul_le_mul_right C2.index index_inf_le
    _ = 8 := by rw [hCindex, hC1index, hC2index]
  have hZcard : Nat.card C = Nat.card Z :=
    Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv
  have hcard := C.card_mul_index
  rw [hCindex, hZcard] at hcard
  exact ⟨hPcard, by omega⟩

/-- The original ambient group and chosen Sylow satisfy the final order bounds
in the elementary direct-product branch of Goldschmidt (2.15). -/
theorem elementary_product_cubic_bound {G E : Type*} [Group G] [Finite G]
    [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (P : Sylow 2 G) (eG : G ≃* (Equiv.Perm (Fin 3) × E))
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    Nat.card P ≤ 8 ∧ Nat.card E ≤ 4 := by
  let f := (MonoidHom.fst (Equiv.Perm (Fin 3)) E).comp eG.toMonoidHom
  let Z := f.ker
  let zToE : Z →* E :=
    (MonoidHom.snd (Equiv.Perm (Fin 3)) E).comp (eG.toMonoidHom.comp Z.subtype)
  have hzfst (z : Z) : (eG z).1 = 1 := z.property
  have hzbij : Function.Bijective zToE := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply eG.injective
      exact Prod.ext ((hzfst x).trans (hzfst y).symm) hxy
    · intro e
      refine ⟨⟨eG.symm (1, e), ?_⟩, ?_⟩
      · change (eG (eG.symm (1, e))).1 = 1
        simp
      · change (eG (eG.symm (1, e))).2 = e
        simp
  have hZp : IsPGroup 2 Z :=
    (IsElementaryAbelian.isPGroup 2 E).of_injective zToE hzbij.1
  have hZcentral : Z ≤ center G := by
    intro z hz
    apply mem_center_iff.mpr
    intro g
    apply eG.injective
    rw [map_mul, map_mul]
    apply Prod.ext
    · have h : (eG z).1 = 1 := hz
      simp [h]
    · change (eG g).2 * (eG z).2 = (eG z).2 * (eG g).2
      exact mul_comm' _ _
  have hfsurj : Function.Surjective f := by
    intro s
    exact ⟨eG.symm (s, 1), by simp [f]⟩
  have hZindex : Z.index = 6 := by
    rw [index_ker, f.range_eq_top_of_surjective hfsurj, card_top]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hZcard : Nat.card Z = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective zToE hzbij)
  obtain ⟨hP, hE⟩ := central_index_six_cubic_bound P Z hZp hZcentral hZindex a ha hno
  exact ⟨hP, hZcard ▸ hE⟩

/-- The central elementary factor has exactly one of the three source orders. -/
theorem elementary_product_cubic_card_cases {G E : Type*} [Group G] [Finite G]
    [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (P : Sylow 2 G) (eG : G ≃* (Equiv.Perm (Fin 3) × E))
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 := by
  have hcard := (elementary_product_cubic_bound P eG a ha hno).2
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (show 2 ^ n ≤ 2 ^ 2 by simpa [← hn] using hcard)
  interval_cases n <;> simp_all

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
