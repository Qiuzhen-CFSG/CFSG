module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Maps

/-!
# Core, Sylow and index transport from the literal binary star quotient

An S₃ equivalence for LT/O₂(LT) and generation of that quotient by I
identify the restricted star kernel with O₂(I). The resulting quotient
equivalence is induced by the original star map. The kernel lies in T,
so it normalizes U, and the nontrivial two-group U* has order two.
This gives |U:W|=2 and the Sylow witness in the literal join L*U*.
The S₃ recognition and star-generation inputs are explicit here.

Source: Aschbacher–Smith, G.2.3(1–3), printed pp.333–334.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

theorem binary_star_U_card (h : D.BaseHypothesis) (b : D.BinaryNaturalData) (hUT : D.U ≤ D.T)
    (e : D.Star ≃* Equiv.Perm (Fin 3)) : Nat.card (D.star D.U) = 2 := by
  have hc : Nat.card D.Star = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hp : IsPGroup 2 (D.star D.U) :=
    (h.binary_U_isPGroup hUT).comap_subtype.map (QuotientGroup.mk' (pCore 2 D.LT))
  have hd : Nat.card (D.star D.U) ∣ 6 := hc ▸ (D.star D.U).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (D.star D.U)) 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card (D.star D.U) ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · exact (b.image_nontrivial (Subgroup.card_eq_one.mp h1)).elim
  · exact h2

theorem binary_I_star_kernel (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) :
    (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL)).ker = pCore 2 (D.I g) := by
  let q := D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL)
  have hq : Function.Surjective q := by
    apply MonoidHom.range_eq_top.mp
    rw [binaryStarRestriction_range, hi]
  have hk : (e.toMonoidHom.comp q).ker = q.ker := by
    ext x
    exact e.map_eq_one_iff
  have hp : IsPGroup 2 (e.toMonoidHom.comp q).ker := by
    rw [hk]
    exact binaryStarRestriction_ker_isPGroup _ _
  rw [← hk]
  exact ker_eq_twoCore_of_surjective_perm_three _ (e.surjective.comp hq) hp

noncomputable def binaryCoreQuotientEquiv (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* Equiv.Perm (Fin 3) :=
  ((QuotientGroup.quotientMulEquivOfEq (binary_I_star_kernel hUT g hgL e hi).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL))
      (MonoidHom.range_eq_top.mp ((binaryStarRestriction_range _ _).trans hi)))).trans e

/-- The core quotient equivalence is induced by the restricted original star map. -/
theorem binaryCoreQuotientEquiv_apply (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) (x : D.I g) :
    binaryCoreQuotientEquiv hUT g hgL e hi (QuotientGroup.mk' (pCore 2 (D.I g)) x) =
      e (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL) x) := rfl

theorem binary_S_le_LT_core (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) : D.S g ≤ D.LT.pCoreIn 2 := by
  rintro s ⟨x, hx, rfl⟩
  refine ⟨inclusion (binary_I_le_LT hUT hgL) x, ?_, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact (binary_I_star_kernel hUT g hgL e hi).ge hx

theorem binary_S_normalizes_U (h : D.BaseHypothesis) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) : D.S g ≤ normalizer (D.U : Set G) :=
  (binary_S_le_LT_core hUT g hgL e hi).trans
    (h.binary_core_le_T.trans h.binary_T_normalizes_U)

theorem binary_W_index (h : D.BaseHypothesis) (b : D.BinaryNaturalData) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) : (D.W g).relIndex D.U = 2 := by
  have hUI : D.U ≤ D.I g := le_sup_left
  have hU : (D.U.subgroupOf (D.I g)).map (D.I g).subtype = D.U :=
    map_subgroupOf_eq_of_le hUI
  calc
    (D.W g).relIndex D.U = (D.S g).relIndex D.U := inf_relIndex_left _ _
    _ = (pCore 2 (D.I g)).relIndex (D.U.subgroupOf (D.I g)) := by
      rw [← relIndex_map_map_of_injective _ _ (D.I g).subtype_injective, hU]
      rfl
    _ = (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL)).ker.relIndex
        (D.U.subgroupOf (D.I g)) := by rw [binary_I_star_kernel hUT g hgL e hi]
    _ = Nat.card ((D.U.subgroupOf (D.I g)).map
        (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL))) := relIndex_ker _ _
    _ = Nat.card (D.star D.U) := by rw [binaryStarRestriction_map _ _ _ hUI]
    _ = 2 := binary_star_U_card h b hUT e

omit [Finite G] in
theorem binary_star_join_eq_top (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (hi : D.star (D.I g) = ⊤) :
    D.star D.L ⊔ D.star D.U = ⊤ := by
  apply top_unique
  rw [← hi, ← binary_star_sup _ _ le_sup_left (hUT.trans le_sup_right)]
  exact binary_star_mono (binary_I_le_join hgL)

noncomputable def binaryStarJoinEquiv (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) : (D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* Equiv.Perm (Fin 3) :=
  ((MulEquiv.subgroupCongr (binary_star_join_eq_top hUT g hgL hi)).trans topEquiv).trans e

theorem binary_star_U_sylow (h : D.BaseHypothesis) (b : D.BinaryNaturalData) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) (e : D.Star ≃* Equiv.Perm (Fin 3))
    (hi : D.star (D.I g) = ⊤) :
    ∃ P : Sylow 2 (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
      (P : Subgroup (D.star D.L ⊔ D.star D.U : Subgroup D.Star)).map
        (D.star D.L ⊔ D.star D.U).subtype = D.star D.U := by
  let J : Subgroup D.Star := D.star D.L ⊔ D.star D.U
  let A := (D.star D.U).subgroupOf J
  have hp : IsPGroup 2 A := ((h.binary_U_isPGroup hUT).comap_subtype.map
    (QuotientGroup.mk' (pCore 2 D.LT))).comap_subtype
  have ha : Nat.card A = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show D.star D.U ≤ J from le_sup_right)).toEquiv]
    exact binary_star_U_card h b hUT e
  have hj : Nat.card J = 6 := by
    rw [Nat.card_congr (binaryStarJoinEquiv hUT g hgL e hi).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hindex : A.index = 3 := by
    have he := A.card_mul_index
    rw [ha, hj] at he
    omega
  refine ⟨hp.toSylow (by rw [hindex]; decide), ?_⟩
  exact map_subgroupOf_eq_of_le (show D.star D.U ≤ J from le_sup_right)

end CFSG.Quasithin.ChapterG.Section02.Setup
