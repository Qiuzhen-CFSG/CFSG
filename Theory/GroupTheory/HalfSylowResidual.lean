module
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.CyclicSylowTwoComplement

/-!
# The residual section below a Sylow subgroup of index two

If Q is normal and has index two in a Sylow two-subgroup, the quotient
has cyclic Sylow subgroup of order two. Burnside transfer identifies its
two-residual with its odd core. Pulling this subgroup back proves that
Q O²(G) has index two and Q is its Sylow two-subgroup.

Source application: Aschbacher–Smith, C.5.8–11, printed pp.160–161.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- The true residual section attached to a normal half-Sylow subgroup. -/
theorem normal_half_sylow_residual (S : Sylow 2 G) (Q : Subgroup G) [Q.Normal]
    (hQS : Q ≤ (S : Subgroup G)) (hhalf : Q.relIndex (S : Subgroup G) = 2) :
    (Q ⊔ pResidual 2 G).index = 2 ∧
      ∃ P : Sylow 2 (Q ⊔ pResidual 2 G : Subgroup G),
        (P : Subgroup (Q ⊔ pResidual 2 G : Subgroup G)).map (Q ⊔ pResidual 2 G).subtype = Q := by
  let q := QuotientGroup.mk' Q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective Q)
  have hcard : Nat.card Sbar = 2 := by
    have hi := relIndex_ker (S : Subgroup G) q
    rw [QuotientGroup.ker_mk'] at hi
    exact hi.symm.trans hhalf
  have hcyc : IsCyclic Sbar := isCyclic_of_prime_card hcard
  have heven : 2 ∣ Nat.card (G ⧸ Q) := by
    rw [← hcard]
    exact (Sbar : Subgroup (G ⧸ Q)).card_subgroup_dvd_card
  have hcomp := Sbar.isComplement'_pPrimeCore_of_isCyclic hcyc heven
  have hres := Sbar.twoResidual_eq_oddCore_of_isCyclic hcyc
  let N := Q ⊔ pResidual 2 G
  have hmap : N.map q = pResidual 2 (G ⧸ Q) := by
    change (Q ⊔ pResidual 2 G).map q = _
    rw [Subgroup.map_sup,map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective Q)]
    have hz : Q.map q = ⊥ := (Subgroup.map_eq_bot_iff Q).mpr (by rw [QuotientGroup.ker_mk'])
    rw [hz,bot_sup_eq]
  have hidx : N.index = 2 := by
    rw [← N.index_map_eq (QuotientGroup.mk'_surjective Q) (by rw [QuotientGroup.ker_mk']; exact le_sup_left),
      hmap,hres,hcomp.index_eq_card,hcard]
  have hodd : ¬ 2 ∣ Q.relIndex N := by
    have hi := relIndex_ker N q
    rw [QuotientGroup.ker_mk',hmap,hres] at hi
    rw [hi]
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have hp : IsPGroup 2 (Q.subgroupOf N) := (S.isPGroup'.to_le hQS).comap_subtype
  refine ⟨hidx,hp.toSylow hodd,?_⟩
  exact map_subgroupOf_eq_of_le (show Q ≤ N from le_sup_left)
end Subgroup
