module
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Action
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.ElementaryAbelian.Join

/-!
# Excluding the elementary hyperplane in the low-rank argument

A nonabelian finite group has at most two elementary abelian subgroups of
index two. If a Sylow two-subgroup fixes one, its orbit under the whole
actor group has odd size at most two, hence size one. Applied to W inside
U, this makes W invariant under H; the literal generation U=⟨Vᴴ⟩ and V≤W
then contradict |U:W|=2. Consequently E, which is elementary, is proper
in W. This supplies the nonzero natural-section case needed to place the
fixed lift in W; no positive multiplicity is assumed in 12.8.9(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.8.4, 12.8.9(2–3), and the first paragraph of the proof of 12.8.11(6),
printed p.855 / PDF p.872.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {K : Type*} [Group K]

private theorem eq_top_of_index_two (A C : Subgroup K) (hi : A.index = 2)
    (hAC : A ≤ C) (x : K) (hx : x ∈ C) (hxn : x ∉ A) : C = ⊤ := by
  apply top_unique
  intro y _
  by_cases hy : y ∈ A
  · exact hAC hy
  · have hm : y * x⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr
      (iff_of_false hy (by simpa using hxn))
    simpa only [inv_mul_cancel_right] using C.mul_mem (hAC hm) hx

private theorem sup_eq_top_of_index_two [Finite K] (A B : Subgroup K)
    (ha : A.index = 2) (hb : B.index = 2) (hne : A ≠ B) : A ⊔ B = ⊤ := by
  have hnot : ¬ B ≤ A := by
    intro hle
    apply hne
    apply (eq_of_le_of_card_ge hle ?_).symm
    have hca := A.card_mul_index
    have hcb := B.card_mul_index
    rw [ha] at hca
    rw [hb] at hcb
    omega
  obtain ⟨b, hbB, hbA⟩ := SetLike.not_le_iff_exists.mp hnot
  exact eq_top_of_index_two A (A ⊔ B) ha le_sup_left b (mem_sup_right hbB) hbA

private theorem square_one_commute {x y : K} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hy)
  have ixy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hxy)
  change x * y = y * x
  simpa only [mul_inv_rev, ix, iy] using ixy.symm

/-- In a nonabelian group with two distinct elementary subgroups of index two,
every involution belongs to their union. -/
private theorem square_one_mem_union [Finite K] (hK : ¬ IsMulCommutative K)
    (A B : Subgroup K) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (ha : A.index = 2) (hb : B.index = 2) (hne : A ≠ B)
    (x : K) (hx : x ^ 2 = 1) : x ∈ A ∨ x ∈ B := by
  by_contra! hn
  have hgen := sup_eq_top_of_index_two A B ha hb hne
  have hD : A ⊓ B ≤ center K := by
    intro d hd
    apply mem_center_iff.mpr
    have hc : A ⊔ B ≤ centralizer ({d} : Set K) := by
      apply sup_le
      · intro a hA
        exact mem_centralizer_singleton_iff.mpr ((le_centralizer A hd.1) a hA)
      · intro b hB
        exact mem_centralizer_singleton_iff.mpr ((le_centralizer B hd.2) b hB)
    intro y
    exact (mem_centralizer_singleton_iff.mp (hc (hgen.symm ▸ mem_top y)))
  have hxC : x ∈ centralizer (A : Set K) := by
    intro a haA
    by_cases haB : a ∈ B
    · exact (mem_center_iff.mp (hD ⟨haA, haB⟩) x).symm
    · have hab : a * x ∈ B := (B.mul_mem_iff_of_index_two hb).mpr
        (iff_of_false haB hn.2)
      exact (square_one_commute
        (elemPow_eq_one_of_isElementaryAbelian a haA) hx
        (elemPow_eq_one_of_isElementaryAbelian (a * x) hab)).eq
  have htop : A ⊔ zpowers x = ⊤ :=
    eq_top_of_index_two A _ ha le_sup_left x (mem_sup_right (mem_zpowers x)) hn.1
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian 2 (A ⊔ zpowers x : Subgroup K) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hxC)
  apply hK
  let : IsMulCommutative (⊤ : Subgroup K) := htop ▸ inferInstance
  exact ⟨⟨fun a b => congrArg Subtype.val (mul_comm
    (⟨a, mem_top a⟩ : (⊤ : Subgroup K)) ⟨b, mem_top b⟩)⟩⟩

private theorem elementary_index_two_eq [Finite K] (hK : ¬ IsMulCommutative K)
    (A B C : Subgroup K) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    [IsElementaryAbelian 2 C] (ha : A.index = 2) (hb : B.index = 2)
    (hc : C.index = 2) (hne : A ≠ B) : C = A ∨ C = B := by
  have hsub : (C : Set K) ⊆ (A : Set K) ∪ (B : Set K) := by
    intro x hx
    exact square_one_mem_union hK A B ha hb hne x
      (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hcard (D : Subgroup K) (hd : D.index = 2) : Nat.card D = Nat.card C := by
    have hD := D.card_mul_index
    have hC := C.card_mul_index
    rw [hd] at hD
    rw [hc] at hC
    omega
  rcases SubgroupClass.subset_union.mp hsub with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (hcard A ha).le)
  · exact Or.inr (eq_of_le_of_card_ge h (hcard B hb).le)

private theorem elementary_index_two_invariant [Finite K]
    {J : Type*} [Group J] [Finite J] [MulDistribMulAction J K]
    (S : Sylow 2 J) (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hi : A.index = 2) (hK : ¬ IsMulCommutative K)
    (hS : ∀ s : S, (s : J) • A = A) : ∀ j : J, j • A = A := by
  classical
  by_contra! hn
  obtain ⟨b, hb⟩ := hn
  let B := b • A
  have hindex (j : J) : (j • A).index = 2 := by
    change (A.map (MulDistribMulAction.toMulAut J K j).toMonoidHom).index = 2
    exact (index_map_of_bijective (f := (MulDistribMulAction.toMulAut J K j).toMonoidHom)
      (MulDistribMulAction.toMulAut J K j).bijective A).trans hi
  have hel (j : J) : IsElementaryAbelian 2 (j • A : Subgroup K) :=
    IsElementaryAbelian.map (MulDistribMulAction.toMonoidEnd J K j)
  let : IsElementaryAbelian 2 B := hel b
  have hsub : MulAction.orbit J A ⊆ ({A, B} : Set (Subgroup K)) := by
    rintro C ⟨j, rfl⟩
    let : IsElementaryAbelian 2 (j • A : Subgroup K) := hel j
    exact elementary_index_two_eq hK A B (j • A) hi (hindex b) (hindex j)
      (Ne.symm hb)
  let D := MulAction.stabilizer J A
  have hsmall : D.index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub).trans (by simp [B, Ne.symm hb])
  have hSD : (S : Subgroup J) ≤ D := by
    intro s hs
    exact hS ⟨s, hs⟩
  have hodd : ¬ 2 ∣ D.index := fun hd => S.not_dvd_index
    (hd.trans (index_dvd_of_le hSD))
  have hpos : D.index ≠ 0 := D.index_ne_zero_of_finite
  have he : D.index = 1 := by
    have hne : D.index ≠ 2 := fun he => hodd (he ▸ dvd_rfl)
    omega
  have htop : D = ⊤ := index_eq_one.mp he
  exact hb (show b ∈ D from htop.symm ▸ mem_top b)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- A Sylow-invariant plane centralizer of index two cannot be elementary:
the full orbit-generation U=⟨Vᴴ⟩ rules out the elementary hyperplane case. -/
theorem W_not_elementary (F : InvariantFlag T V n) [IsMulCommutative V]
    (hU : ¬ IsMulCommutative F.U) (hindex : F.W.relIndex F.U = 2) :
    ¬ IsElementaryAbelian 2 F.W := by
  intro hW
  let : IsElementaryAbelian 2 F.W := hW
  let A := F.W.subgroupOf F.U
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (show F.W ≤ F.U from inf_le_left)
  let r : F.H →* MulAut F.U := F.U.normalizerMonoidHom.comp
    (F.H.subtype.codRestrict _ (fun h => le_normalizer_conjugateSpanBy V F.H h.property))
  let : MulDistribMulAction F.H F.U := MulDistribMulAction.compHom F.U r
  let S : Sylow 2 F.H := T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)
  have hTW : (T : Subgroup G) ≤ normalizer (F.W : Set G) :=
    (le_inf ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      ((F.invariant 2).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hS : ∀ t : S, (t : F.H) • A = A := by
    intro t
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      change ((t : F.H) : G) * (a : G) * (((t : F.H) : G))⁻¹ ∈ F.W
      exact (mem_normalizer_iff.mp (hTW t.property) a).mp ha
    · intro a ha
      refine ⟨(t : F.H)⁻¹ • a, ?_, ?_⟩
      · change (((t : F.H) : G))⁻¹ * (a : G) * ((((t : F.H) : G))⁻¹)⁻¹ ∈ F.W
        exact (mem_normalizer_iff.mp ((normalizer (F.W : Set G)).inv_mem (hTW t.property)) a).mp ha
      · exact smul_inv_smul (t : F.H) a
  have hall := elementary_index_two_invariant S A hindex hU hS
  have hHW : F.H ≤ normalizer (F.W : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh w hw
    let a : F.U := ⟨w, hw.1⟩
    have hm : (⟨h, hh⟩ : F.H) • a ∈ (⟨h, hh⟩ : F.H) • A :=
      smul_mem_pointwise_smul a (⟨h, hh⟩ : F.H) A hw
    rw [hall] at hm
    exact hm
  have hUW : F.U ≤ F.W := conjugateSpanBy_le F.seed_le_W hHW
  have he : F.W = F.U := le_antisymm inf_le_left hUW
  rw [he, relIndex_self] at hindex
  omega

/-- The intersection E is elementary by 12.8.11(2), whereas W cannot be;
this excludes the zero natural-module case without an extra rank assumption. -/
theorem W_ne_E (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) [IsElementaryAbelian 2 (F.E g)]
    (hU : ¬ IsMulCommutative F.U) (hindex : F.W.relIndex F.U = 2) :
    F.W ≠ F.E g := by
  intro he
  exact W_not_elementary F hU hindex (he.symm ▸ inferInstance)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
