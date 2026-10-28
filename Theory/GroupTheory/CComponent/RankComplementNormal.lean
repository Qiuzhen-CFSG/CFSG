module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# Normality of a component with a normal rank complement

A normal subgroup commuting with an ordinary component also commutes with
all its conjugates. A distinct conjugate therefore contributes a second
copy of the component's prime rank alongside the normal subgroup. When
the component center has order prime to p, these ranks add. A strict
ambient rank bound forces normality.

The C-component version passes through the ambient two-core, where the
commutator hypothesis becomes exact centralization, and reflects normality
back through the solvable kernel. It does not assert centralization in the
original group.

Source application: Aschbacher--Smith 14.6.15, printed p.1035, for the
escaping component and the normal second quintic factor in N_G(K₂).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem rank_add_le_sup {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hc : A ≤ centralizer (B : Set G))
    (hz : Nat.Coprime p (Nat.card (center B))) :
    primeRank p A + primeRank p B ≤ primeRank p (A ⊔ B : Subgroup G) := by
  let D := A ⊔ B
  let eA := subgroupOfEquivOfLe (show A ≤ D from le_sup_left)
  let eB := subgroupOfEquivOfLe (show B ≤ D from le_sup_right)
  have hc' : A.subgroupOf D ≤ centralizer (B.subgroupOf D : Set D) := by
    intro a ha b hb
    exact Subtype.ext (hc ha b hb)
  have hz' : Nat.Coprime p (Nat.card (center (B.subgroupOf D))) := by
    rwa [Nat.card_congr (centerCongr eB).toEquiv]
  have h := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (A.subgroupOf D) (B.subgroupOf D) hc' hz'
  rwa [primeRank_congr p eA, primeRank_congr p eB] at h

/-- An independent normal factor leaves too little rank for a second component conjugate. -/
theorem IsComponent.normal_of_coprime_center_rank_complement
    {L : Subgroup G} (hL : IsComponent G L) (B : Subgroup G) [B.Normal]
    (p : ℕ) [Fact p.Prime] (hc : Nat.Coprime p (Nat.card (center L)))
    (hLB : L ≤ centralizer (B : Set G))
    (hr : primeRank p G < 2 * primeRank p L + primeRank p B) : L.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := L.map (MulAut.conj g).toMonoidHom
  have hEL : E ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((hL.map_conj g).commutator_eq_bot_of_ne hL hne)
  have hEB : E ≤ centralizer (B : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hLB).trans
      (map_centralizer_le_centralizer_image (B : Set G) (MulAut.conj g).toMonoidHom)
    have he : B.map (MulAut.conj g).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
    simpa only [←Subgroup.coe_map,he] using hh
  have hce : Nat.Coprime p (Nat.card (center E)) := by
    exact (Nat.card_congr (centerCongr ((MulAut.conj g).subgroupMap L)).toEquiv) ▸ hc
  have he : primeRank p E = primeRank p L :=
    (primeRank_congr p ((MulAut.conj g).subgroupMap L)).symm
  have h1 := rank_add_le_sup B E (le_centralizer_iff.mp hEB) hce
  have h2 := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (B ⊔ E) L (sup_le (le_centralizer_iff.mp hLB) hEL) hc
  omega
end Theory.GroupTheory

open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- A normal factor whose quotient centralizes the component leaves too
little odd rank for a distinct conjugate. Normality is in the original group. -/
theorem IsCComponent.normal_of_coprime_core_center_rank_complement
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (B : Subgroup G) [B.Normal]
    (hc : Nat.Coprime p (Nat.card (center (L ⧸ pCore 2 L))))
    (hLB : ⁅L,B⁆ ≤ L.pCoreIn 2)
    (hr : primeRank p G < 2 * primeRank p L + primeRank p B) : L.Normal := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let E := L.map q
  let e : (L ⧸ pCore 2 L) ≃* E := cComponentTwoCoreQuotientEquiv hL
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv e
  have hE : IsComponent (G ⧸ pCore 2 G) E :=
    ⟨hL.subnormal.map (QuotientGroup.mk'_surjective _),inferInstance⟩
  let : (B.map q).Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hce : Nat.Coprime p (Nat.card (center E)) := by
    rwa [←Nat.card_congr (centerCongr e).toEquiv]
  have hcomm : E ≤ centralizer (B.map q : Set (G ⧸ pCore 2 G)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    apply hLB.trans
    rw [pCoreIn,pCore_subnormal_eq_comap 2 hL.subnormal]
    exact Subgroup.map_comap_le _ _
  have hrq : primeRank p (G ⧸ pCore 2 G) <
      2 * primeRank p E + primeRank p (B.map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel hp q hq,
      ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel hp q hq]
    exact (primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup).trans_lt hr
  let : E.Normal := hE.normal_of_coprime_center_rank_complement (B.map q) p hce hcomm hrq
  exact cComponent_normal_of_quotient_normal hL (pCore 2 G) inferInstance
end Subgroup
