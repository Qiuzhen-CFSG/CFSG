module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.SylowLift
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.LocalSpan

/-!
# The two original factor Sylow extensions

The marked alternating factor together with the Baumann four-group gives
the full symmetric factor. The actual local conjugate span has image
S₄×V₄ and its component product has image S₅×V₄. Their known orders and
kernel saturation construct the Sylow extension inside the original span.
Swapping coordinates proves the other factor with the same quotient map.

Source: Aschbacher--Smith C.1.24 and E.2.3(3).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB.Offenders
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem alternating_sup_transposition (a : Sym) :
    alternatingGroup (Fin 5) ⊔ (D 5).map (MulAut.conj a).toMonoidHom = ⊤ := by
  apply top_unique
  intro x _
  have ho : a * Equiv.swap (0 : Fin 5) 1 * a⁻¹ ∈ (D 5).map (MulAut.conj a).toMonoidHom :=
    mem_map_of_mem (MulAut.conj a).toMonoidHom (pairSwap_mem 0 (by decide))
  have hn : a * Equiv.swap (0 : Fin 5) 1 * a⁻¹ ∉ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_mul,map_inv,Equiv.Perm.sign_swap (by decide)]
    simp
  by_cases hx : x ∈ alternatingGroup (Fin 5)
  · exact mem_sup_left hx
  · have hh : x * (a * Equiv.swap (0 : Fin 5) 1 * a⁻¹)⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two,inv_mem_iff]
      exact iff_of_false hx hn
    simpa only [inv_mul_cancel_right] using (alternatingGroup (Fin 5) ⊔ (D 5).map (MulAut.conj a).toMonoidHom).mul_mem
      (mem_sup_left hh) (mem_sup_right ho)

theorem first_sylow_extension
    (q : G →* H) (j : Sym × Sym →* H) (hj : Function.Injective j)
    (S K M : Subgroup G) (hS : IsPGroup 2 S) (hkerM : q.ker ≤ M)
    (a b : Sym)
    (hSm : S.map q = (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)).map j)
    (hK : K.map q = ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym)).map j)
    (hM : (M.map q).comap (j.comp (MonoidHom.inl Sym Sym)) =
      pointFour.map (MulAut.conj a).toMonoidHom)
    (hk : IsSylowSubgroupIn (S ⊓ q.ker) ((K ⊔ S) ⊓ q.ker)) :
    ∃ S₁ : Subgroup G, IsSylowSubgroupIn S₁ (K ⊔ S) ∧ S ≤ S₁ ∧
      (S.subgroupOf S₁).index = 2 ∧ S₁ ≤ conjugateSpanBy S (K ⊓ M) := by
  have him := mapped_first_local_span q j S K M hkerM a b hSm hK hM
  have hspan : conjugateSpanBy S (K ⊓ M) ≤ K ⊔ S := by
    apply conjugateSpanBy_le le_sup_right
    exact (inf_le_left.trans le_sup_left).trans (K ⊔ S).le_normalizer
  have hprod (A B : Subgroup Sym) : Nat.card ((A.prod B).map j) = Nat.card A * Nat.card B := by
    rw [card_map_of_injective hj,Nat.card_congr (A.prodEquiv B).toEquiv,Nat.card_prod]
  have hScard : Nat.card (S.map q) = 16 := by
    rw [hSm,hprod,card_map_of_injective (MulAut.conj a).injective,
      card_map_of_injective (MulAut.conj b).injective,D_card]
  have hIcard : Nat.card ((conjugateSpanBy S (K ⊓ M)).map q) = 96 := by
    rw [him,hprod,card_map_of_injective (MulAut.conj a).injective,
      card_map_of_injective (MulAut.conj b).injective,pointFour_card,D_card]
  have hLcard : Nat.card ((K ⊔ S).map q) = 480 := by
    rw [Subgroup.map_sup,hK,hSm,←Subgroup.map_sup,prod_sup_prod,
      alternating_sup_transposition,bot_sup_eq,hprod,
      card_map_of_injective (MulAut.conj b).injective,D_card,Nat.card_congr Subgroup.topEquiv.toEquiv]
    norm_num [Sym,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  exact sylow_extension_of_paired_local_image q S (K ⊔ S) (conjugateSpanBy S (K ⊓ M))
    hS (le_conjugateSpanBy _ _) hspan hScard hIcard hLcard hk

theorem second_sylow_extension
    (q : G →* H) (j : Sym × Sym →* H) (hj : Function.Injective j)
    (S K M : Subgroup G) (hS : IsPGroup 2 S) (hkerM : q.ker ≤ M)
    (a b : Sym)
    (hSm : S.map q = (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)).map j)
    (hK : K.map q = ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))).map j)
    (hM : (M.map q).comap (j.comp (MonoidHom.inr Sym Sym)) =
      pointFour.map (MulAut.conj b).toMonoidHom)
    (hk : IsSylowSubgroupIn (S ⊓ q.ker) ((K ⊔ S) ⊓ q.ker)) :
    ∃ S₂ : Subgroup G, IsSylowSubgroupIn S₂ (K ⊔ S) ∧ S ≤ S₂ ∧
      (S.subgroupOf S₂).index = 2 ∧ S₂ ≤ conjugateSpanBy S (K ⊓ M) := by
  exact first_sylow_extension q (j.comp (MulEquiv.prodComm : Sym × Sym ≃* Sym × Sym).toMonoidHom)
    (hj.comp MulEquiv.prodComm.injective) S K M hS hkerM b a
    (by simpa only [prod_map_swap] using hSm)
    (by simpa only [prod_map_swap] using hK)
    (by
      have hs : (MulEquiv.prodComm : Sym × Sym ≃* Sym × Sym).toMonoidHom.comp
          (MonoidHom.inl Sym Sym) = MonoidHom.inr Sym Sym := by ext x : 1; simp
      simpa only [MonoidHom.comp_assoc,hs] using hM) hk
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
