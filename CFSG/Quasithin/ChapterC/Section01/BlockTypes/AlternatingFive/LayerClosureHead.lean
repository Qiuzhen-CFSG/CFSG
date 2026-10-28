module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureRatio
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Two-core control for a split A₅ layer with quasisimple head

Suppose W is the normal split closure of the natural A₅ module and
centralizes O₂(G). The kernel C_G(W) contains O₂(G), but is proper because
the original block acts as A₅. If G/O₂(G) is quasisimple, the image of this
kernel is central. Every two-subgroup of that image is trivial, since the
head has trivial two-core. In particular the whole original block core
lies in O₂(G), including the possible central involution of C.1.13(c).

Source: the contained-layer reduction in Aschbacher–Smith 10.2.1, p.743,
with the central-cover distinction of C.1.13(c), pp.124–125.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem two_subgroup_le_core_of_proper_normal (N P : Subgroup G) [N.Normal]
    (hN : N ≠ ⊤) (hON : pCore 2 G ≤ N) (hp : IsPGroup 2 P) (hPN : P ≤ N)
    [IsQuasisimple (G ⧸ pCore 2 G)] : P ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let Q := G ⧸ pCore 2 G
  let C := N.map q
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hC : C ≠ ⊤ := by
    intro hc
    apply hN
    have hh := congrArg (comap q) hc
    simpa only [C, q, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hON,
      comap_top] using hh
  have hc : C ≤ center Q := (IsQuasisimple.normal_le_center_or_eq_top C).resolve_right hC
  have hpc : P.map q ≤ center Q := (map_mono hPN).trans hc
  let : (P.map q).Normal := ⟨by
    intro x hx g
    have he : g * x * g⁻¹ = x := by
      rw [mem_center_iff.mp (hpc hx) g, mul_inv_cancel_right]
    rw [he]
    exact hx⟩
  have hpO : P.map q ≤ pCore 2 Q := le_sSup ⟨inferInstance, hp.map q⟩
  have hpbot : P.map q = ⊥ := bot_unique (hpO.trans (pCore_quotient_pCore_eq_bot 2).le)
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hpbot

theorem IsAlternatingBlock.core_le_ambient_core_of_quasisimple_head
    (L W : Subgroup G) [W.Normal] (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (hWC : W ≤ centralizer (pCore 2 G : Set G))
    [IsQuasisimple (G ⧸ pCore 2 G)] : L.pCoreIn 2 ≤ pCore 2 G := by
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  have hk := h.layer_split_quotient_kernel L W hUW hs q (QuotientGroup.ker_mk' _)
  have hLC : L.pCoreIn 2 ≤ C := by
    rintro _ ⟨l,hl,rfl⟩
    have he : q (l : G) = 1 := congrArg Subtype.val
      (MonoidHom.mem_ker.mp (show l ∈ (q.subgroupMap L).ker from by rw [hk]; exact hl))
    exact (QuotientGroup.eq_one_iff (l : G)).mp he
  have hC : C ≠ ⊤ := by
    intro hCt
    obtain ⟨e⟩ := h.layer_split_quotient_image L W hUW hs q (QuotientGroup.ker_mk' _)
    have hbot : L.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
      rw [QuotientGroup.ker_mk',hCt]; exact le_top)
    have hh := Nat.card_congr e.toEquiv
    rw [hbot, card_bot,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  exact two_subgroup_le_core_of_proper_normal C (L.pCoreIn 2) hC (le_centralizer_iff.mp hWC)
    (pCore_isPGroup.map L.subtype) hLC
end CFSG.Quasithin.ChapterC
