module
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Three-rank from an independent nine-group and a cubic section

Pass to the literal join and quotient by the normal factor's two-core.
The remaining factor has order three, so the odd elementary nine-group
centralizes it. Their trivial intersection gives an elementary subgroup
of order twenty-seven, which lifts through the two-group kernel.

Source application: Aschbacher--Smith, 10.2.9, printed p.753.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An independent elementary nine-group normalizing a cubic core section
forces three-rank at least three in their literal join. -/
theorem three_le_primeRank_of_nine_normalizing_cubic_section (R E : Subgroup G)
    (hn : E ≤ normalizer (R : Set G))
    (hR : Nat.card (R ⧸ pCore 2 R) = 3)
    (he : IsElementaryAbelian 3 E) (hc : Nat.card E = 9) (hd : Disjoint R E) :
    3 ≤ primeRank 3 (R ⊔ E : Subgroup G) := by
  let J := R ⊔ E
  let A := R.subgroupOf J
  let B := E.subgroupOf J
  let eA : A ≃* R := subgroupOfEquivOfLe (show R ≤ J from le_sup_left)
  let eB : B ≃* E := subgroupOfEquivOfLe (show E ≤ J from le_sup_right)
  let _ := he
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.subgroupOf le_sup_right
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le R.le_normalizer hn)
  let Q := (pCore 2 A).map A.subtype
  let : Q.Normal := inferInstance
  let q := QuotientGroup.mk' Q
  have hQ : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := A)).map A.subtype
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hkerA : (q.subgroupMap A).ker = pCore 2 A := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective A.subtype_injective _
  let ea : (A ⧸ pCore 2 A) ≃* A.map q :=
    (QuotientGroup.quotientMulEquivOfEq hkerA.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap A) (q.subgroupMap_surjective A))
  have hac : Nat.card (A.map q) = 3 := by
    rw [←Nat.card_congr ea.toEquiv,
      Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv]
    exact hR
  have hbc : Nat.card (B.map q) = 9 := by
    let eb := MulEquiv.ofBijective (q.subgroupMap B)
      ⟨fun x y h => injective_comp_subtype_of_coprime_ker q hk B
        (IsElementaryAbelian.isPGroup 3 B) (congrArg Subtype.val h), q.subgroupMap_surjective B⟩
    rw [←Nat.card_congr eb.toEquiv,Nat.card_congr eB.toEquiv,hc]
  have hdis : Disjoint (A.map q) (B.map q) := by
    rw [disjoint_comm,disjoint_iff,←map_inf_of_ker_le q B A (by
      rw [QuotientGroup.ker_mk']; exact map_subtype_le _)]
    have hh : B ⊓ A = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact Subtype.ext (hd.le_bot ⟨hx.2,hx.1⟩)
    rw [hh,Subgroup.map_bot]
  let : (A.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hcomm : B.map q ≤ centralizer (A.map q : Set (J ⧸ Q)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact commutator_eq_bot_of_odd_normalizes_card_three (A.map q) (B.map q) hac
      (by rw [hbc]; decide) (by rw [normalizer_eq_top]; exact le_top)
  let : IsCyclic (A.map q) := isCyclic_of_prime_card hac
  let : IsElementaryAbelian 3 (A.map q) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => by rw [←hac]; exact pow_card_eq_one') }
  let : IsElementaryAbelian 3 (B.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 3 (A.map q ⊔ B.map q : Subgroup (J ⧸ Q)) :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  apply IsElementaryAbelian.primeRank_ge_of_coprime_quotient q
    (QuotientGroup.mk'_surjective _) hk (A.map q ⊔ B.map q)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (centralizer_le_normalizer _)) hdis,hac,hbc]
  decide
end Theory.GroupTheory
