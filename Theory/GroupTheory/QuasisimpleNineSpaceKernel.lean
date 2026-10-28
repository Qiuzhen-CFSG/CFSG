module
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Removing the odd center above an irreducible binary nine-space

Let E be a minimal normal two-subgroup of order 512. If its full
centralizer is three-free, the center of G/O₂(G) is also three-free.
Indeed, a central cubic lifts through O₂(G). The preimage of its cyclic
subgroup is normal, so its fixed subgroup in E is either trivial or all
of E. Orbit counting modulo three excludes the trivial fixed subgroup,
since 512 is not congruent to one. This contradicts the centralizer premise.

For a quasisimple two-core quotient with projective marking PSL₃(4),
the center has odd order dividing three. Hence the entire center vanishes.
The original two-core and its quotient are retained throughout.
Source application: the ordinary-cover reduction in Aschbacher--Smith
4.2.13, printed p.612, used in 8.2.7, printed p.718.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem central_three_quotient_excluded
    (E N : Subgroup G) [E.Normal] [N.Normal]
    (hN : IsPGroup 2 N) (hNC : N ≤ centralizer (E : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ E → X.Normal → X = ⊥ ∨ X = E)
    (hcard : Nat.card E = 512)
    (hthree : ¬ 3 ∣ Nat.card (centralizer (E : Set G))) :
    ¬ 3 ∣ Nat.card (center (G ⧸ N)) := by
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := hN.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hx' : orderOf (x : G ⧸ N) = 3 := (orderOf_coe x).trans hx
  have hxp : IsPGroup 3 (zpowers (x : G ⧸ N)) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hx')
  obtain ⟨A,hA,⟨a⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime q hq hker
    (zpowers (x : G ⧸ N)) hxp
  have hAp : IsPGroup 3 A := hxp.of_equiv a.symm
  have hi := injective_comp_subtype_of_coprime_ker q hker A hAp
  obtain ⟨y,hy,hyx⟩ := hA.symm ▸ mem_zpowers (x : G ⧸ N)
  have hyo : orderOf y = 3 := (orderOf_coe (⟨y,hy⟩ : A)).trans
    ((orderOf_injective (q.comp A.subtype) hi ⟨y,hy⟩).symm.trans (hyx ▸ hx'))
  let Z := (zpowers (x : G ⧸ N)).comap q
  have hz : zpowers (x : G ⧸ N) ≤ center (G ⧸ N) := zpowers_le.mpr x.property
  let : (zpowers (x : G ⧸ N)).Normal := ⟨fun n hn g => by
    have hc := mem_center_iff.mp (hz hn) g
    simpa only [hc,mul_assoc,mul_inv_cancel,mul_one] using hn⟩
  let : Z.Normal := inferInstance
  have hZ : Z = zpowers y ⊔ N := by
    have he : (zpowers y).map q = zpowers (x : G ⧸ N) := by
      rw [MonoidHom.map_zpowers,hyx]
    change (zpowers (x : G ⧸ N)).comap q = _
    rw [←he,comap_map_eq,QuotientGroup.ker_mk']
  have hfix : E ⊓ centralizer (Z : Set G) = E ⊓ centralizer (zpowers y : Set G) := by
    rw [hZ]
    apply le_antisymm (inf_le_inf_left _ (centralizer_le
      (fun z hz => (show zpowers y ≤ zpowers y ⊔ N from le_sup_left) hz)))
    exact le_inf inf_le_left (le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp inf_le_right) (hNC.trans (centralizer_le inf_le_left))))
  have hne : E ⊓ centralizer (Z : Set G) ≠ ⊥ := by
    intro he
    have hyp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1)
      (by simpa only [Nat.card_zpowers,pow_one] using hyo)
    have hm := card_modEq_card_inf_centralizer (zpowers y) E hyp
      (by rw [normalizer_eq_top]; exact le_top)
    rw [←hfix,he,card_bot,hcard] at hm
    norm_num [Nat.ModEq] at hm
  have hfull : E ⊓ centralizer (Z : Set G) = E :=
    (hirr _ inf_le_left inferInstance).resolve_left hne
  have hyC : y ∈ centralizer (E : Set G) := by
    apply le_centralizer_iff.mp (hfull.symm.le.trans inf_le_right)
    change q y ∈ zpowers (x : G ⧸ N)
    rw [hyx]
    exact mem_zpowers _
  apply hthree
  simpa only [Subgroup.orderOf_mk,hyo] using
    _root_.orderOf_dvd_natCard (⟨y,hyC⟩ : centralizer (E : Set G))

/-- A minimal normal nine-space with three-free centralizer removes the
entire odd central kernel of a quasisimple PSL3(4) two-core quotient. -/
theorem psl3_four_twoCore_center_eq_bot_of_nineSpace
    (E : Subgroup G) [E.Normal] (hE : IsPGroup 2 E)
    (hirr : ∀ X : Subgroup G, X ≤ E → X.Normal → X = ⊥ ∨ X = E)
    (hcard : Nat.card E = 512)
    (hthree : ¬ 3 ∣ Nat.card (centralizer (E : Set G)))
    [IsQuasisimple (G ⧸ pCore 2 G)]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃* PSL(3,F)) :
    center (G ⧸ pCore 2 G) = ⊥ := by
  have h3 := central_three_quotient_excluded E (pCore 2 G) pCore_isPGroup
    (pCore_le_centralizer_of_minimal_normal_pSubgroup E hE hirr) hirr hcard hthree
  have hodd : Odd (Nat.card (center (G ⧸ pCore 2 G))) :=
    Nat.not_even_iff_odd.mp (fun hd =>
      PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot (G := G) 2) _ le_rfl (even_iff_two_dvd.mp hd))
  rcases (Nat.dvd_prime Nat.prime_three).mp
      (Matrix.PSL3.BinaryOddCenterCover.center_card_dvd_three_four hF e hodd) with h1 | h3'
  · exact card_eq_one.mp h1
  · exact (h3 (h3' ▸ dvd_rfl)).elim

end Subgroup
