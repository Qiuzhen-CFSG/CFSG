module

public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Nonfusion of a pair of Sylow-normal subgroups

Suppose two distinct subgroups are normalized by a Sylow two-subgroup P,
and the P-normalizer permutes them. Their orbit has size at most two and
odd size, hence size one. Burnside set-fusion then prevents ambient
conjugacy between them.

Source application: Aschbacher--Smith F.5.4(4), printed p.301, for the two
normal elementary sixteen-subgroups A₁ and Q₂ of the original Sylow group.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

/-- A pair permuted by the Sylow normalizer is fixed when the Sylow fixes it. -/
theorem normalizer_fixes_of_pair (P : Sylow 2 G) (A B : Subgroup G)
    (hA : (P : Subgroup G) ≤ normalizer (A : Set G)) (hne : A ≠ B)
    (hpair : ∀ n ∈ normalizer (P : Set G),
      A.map (MulAut.conj n).toMonoidHom = A ∨ A.map (MulAut.conj n).toMonoidHom = B) :
    ∀ n ∈ normalizer (P : Set G), A.map (MulAut.conj n).toMonoidHom = A := by
  classical
  let N := normalizer (P : Set G)
  let ρ : N →* MulAut G := MulAut.conj.comp N.subtype
  let : MulAction N (Subgroup G) := MulAction.compHom (Subgroup G) ρ
  let S : Sylow 2 N := P.subtype le_normalizer
  have hcov : MulAction.orbit N A ⊆ ({A,B} : Set (Subgroup G)) := by
    rintro D ⟨n,rfl⟩
    exact (hpair n n.property).elim (fun h => Or.inl h) (fun h => Or.inr h)
  have hcard : (MulAction.orbit N A).ncard ≤ 2 :=
    (Set.ncard_le_ncard hcov (Set.toFinite _)).trans_eq (Set.ncard_pair hne)
  have hS : (S : Subgroup N) ≤ MulAction.stabilizer N A := by
    intro s hs
    exact mem_normalizer_iff_map_conj_eq.mp (hA hs)
  have hodd : ¬ 2 ∣ (MulAction.stabilizer N A).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hS))
  rw [← MulAction.index_stabilizer] at hcard
  have hpos : 0 < (MulAction.stabilizer N A).index :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have he : (MulAction.stabilizer N A).index = 1 := by omega
  have ht := index_eq_one.mp he
  intro n hn
  exact (show (⟨n,hn⟩ : N) ∈ MulAction.stabilizer N A from ht.symm ▸ mem_top _)

/-- The two distinct Sylow-normal members of a normalizer-invariant pair
cannot fuse in the ambient group. -/
theorem not_conjugate_of_normalizer_pair (P : Sylow 2 G) (A B : Subgroup G)
    (hA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hB : (P : Subgroup G) ≤ normalizer (B : Set G)) (hne : A ≠ B)
    (hpair : ∀ n ∈ normalizer (P : Set G),
      A.map (MulAut.conj n).toMonoidHom = A ∨ A.map (MulAut.conj n).toMonoidHom = B) :
    ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≠ B := by
  intro g hg
  have hweak : ∀ n : G, (P : Subgroup G).map (MulAut.conj n).toMonoidHom ≤ P →
      n ∈ normalizer (P : Set G) := by
    intro n hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hn (by rw [card_map_of_injective (MulAut.conj n).injective])
  obtain ⟨n,hn,hf⟩ := P.weakly_closed_normalizer_controls_set_fusion P le_rfl hweak
    A B hA hB g (congrArg (fun K : Subgroup G => (K : Set G)) hg)
  have he : A.map (MulAut.conj n).toMonoidHom = B := SetLike.coe_injective hf
  exact hne ((P.normalizer_fixes_of_pair A B hA hne hpair n hn).symm.trans he)

end Sylow
