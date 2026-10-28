module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Outer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.CommonPrime
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ExceptionalArithmetic
public import Theory.GroupTheory.DisjointCommutingProduct


/-!
# The pair stabilizer's actual outer quotient

The intersection of D with LJ is KJ. Thus the literal relative quotient
D/KJ embeds into the outer quotient of N_G(L), whose order divides 2m+1.
The normalizer action, together with |K| = q-1, gives the sharper bound
|D| dividing (q-1)|J|(2m+1). No cancellation through the embedding J → L
and no coarse `LocalGeometry.pair_card_dvd` bound is used.

At m = 1 the bound becomes 294 once the solvable model analysis proves
|J| = 14. The last theorem applies this bound to the existing exceptional
prime-power obstruction. The separate common-prime lemma supplies the
factor seven required by that model analysis.

Source: GLS4, Chapter 2, last paragraph of Lemma 14.9, and Chapter 4,
Lemma 3.1; refs/KGroup/GLS4/Chapter2.tex and Chapter4.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.residual_disjoint_centralizer (d : Context Z M z t m) :
    Disjoint (residualGenerated M z t) (centralizer (residualGenerated M z t : Set G)) := by
  let L := residualGenerated M z t
  have hmodel : IsSimpleBenderGroup L :=
    .isSuzuki ⟨m, by have := d.parameter_pos; omega, ⟨d.model⟩⟩
  let := hmodel.isSimple
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hmodel.not_commutative fun x y => by
        have hx : x ∈ center L := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm).elim
  apply disjoint_def.mpr
  intro x hx hxJ
  have hxc : (⟨x, hx⟩ : L) ∈ center L :=
    mem_center_iff.mpr fun y => Subtype.ext (hxJ y y.property)
  rw [hz] at hxc
  exact congrArg Subtype.val (mem_bot.mp hxc)

public theorem Context.pair_inner_direct_product (d : Context Z M z t m) :
    ∃ e : residualCommutator M t × centralizer (residualGenerated M z t : Set G) ≃*
        (residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G) : Subgroup G),
      ∀ k j, (e (k, j) : G) = (k : G) * (j : G) := by
  have hKL : residualCommutator M t ≤ residualGenerated M z t := le_sup_right
  exact exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (d.residual_disjoint_centralizer.mono_left hKL)
    (le_centralizer_iff.mp (centralizer_le (fun _ hx => hKL hx)))

public theorem Context.pair_inner_intersection (d : Context Z M z t m) :
    (residualGenerated M z t ⊔ centralizer (residualGenerated M z t : Set G)) ⊓
      residualPairStabilizer M t =
        residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hK, _⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  rw [hK]
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let D := residualPairStabilizer M t
  change (L ⊔ J) ⊓ D = (D ⊓ L) ⊔ J
  apply le_antisymm
  · intro x hx
    have hxF : x ∈ (L : Set G) * (J : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L J
        (Subgroup.centralizer_le_normalizer _)]
      exact hx.1
    obtain ⟨l, hl, j, hj, rfl⟩ := hxF
    have hlD : l ∈ D := by
      simpa using D.mul_mem hx.2 (D.inv_mem (d.residual_centralizer_le_pair hj))
    exact mul_mem_sup ⟨hlD, hl⟩ hj
  · exact sup_le (le_inf (inf_le_right.trans le_sup_left) inf_le_left)
      (le_inf le_sup_right d.residual_centralizer_le_pair)

public theorem Context.pair_inner_normal (d : Context Z M z t m) :
    ((residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G)).subgroupOf
      (residualPairStabilizer M t)).Normal := by
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let F := L ⊔ J
  have hFN : F ≤ N := sup_le L.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hFnormal : (F.subgroupOf N).Normal := by
    rw [subgroupOf_sup L.le_normalizer (Subgroup.centralizer_le_normalizer _)]
    infer_instance
  rw [← d.pair_inner_intersection]
  apply (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
  exact (le_inf (d.pair_le_residual_normalizer.trans
    ((normal_subgroupOf_iff_le_normalizer hFN).mp hFnormal)) D.le_normalizer).trans
      inf_normalizer_le_normalizer_inf

public theorem Context.pair_inner_index_dvd (d : Context Z M z t m) :
    ((residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G)).subgroupOf
      (residualPairStabilizer M t)).index ∣ 2 * m + 1 := by
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let N := normalizer (L : Set G)
  let F := L ⊔ J
  let : (F.subgroupOf N).Normal := by
    rw [subgroupOf_sup L.le_normalizer (Subgroup.centralizer_le_normalizer _)]
    infer_instance
  rw [← d.pair_inner_intersection]
  change (F ⊓ residualPairStabilizer M t).relIndex (residualPairStabilizer M t) ∣ _
  rw [inf_relIndex_right, ← relIndex_subgroupOf d.pair_le_residual_normalizer]
  exact (relIndex_dvd_index_of_normal _ _).trans d.normalizer_inner_index_dvd

public theorem Context.pair_inner_quotient_card_dvd (d : Context Z M z t m) :
    letI := d.pair_inner_normal
    Nat.card (residualPairStabilizer M t ⧸
      (residualCommutator M t ⊔ centralizer (residualGenerated M z t : Set G)).subgroupOf
        (residualPairStabilizer M t)) ∣ 2 * m + 1 := by
  let := d.pair_inner_normal
  exact d.pair_inner_index_dvd

public theorem Context.pair_card_dvd_centralizer_card (d : Context Z M z t m) :
    Nat.card (residualPairStabilizer M t) ∣
      (2 ^ (2 * m + 1) - 1) *
        Nat.card (centralizer (residualGenerated M z t : Set G)) * (2 * m + 1) := by
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let D := residualPairStabilizer M t
  let K := residualCommutator M t
  let F := K ⊔ J
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hK, _⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  have hcardK : Nat.card K = 2 ^ (2 * m + 1) - 1 := by
    rw [show K = D ⊓ L from hK]
    exact (residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
      d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter_pos d.model).2
  have hKD : K ≤ D := by rw [show K = D ⊓ L from hK]; exact inf_le_left
  have hKL : K ≤ L := by rw [show K = D ⊓ L from hK]; exact inf_le_right
  have hFD : F ≤ D := sup_le hKD d.residual_centralizer_le_pair
  have hJK : J ≤ normalizer (K : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact centralizer_le (fun _ hx => hKL hx)
  have hc : Nat.card F ∣ (2 ^ (2 * m + 1) - 1) * Nat.card J := by
    rw [← hcardK, card_mul_eq_card_inf_mul_card_sup_of_normalizes K J hJK]
    exact dvd_mul_left _ _
  have h := (F.subgroupOf D).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hFD).toEquiv] at h
  rw [← h]
  exact Nat.mul_dvd_mul hc d.pair_inner_index_dvd

public theorem Context.pair_card_dvd_294_of_centralizer_card
    (d : Context Z M z t 1)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 14) :
    Nat.card (residualPairStabilizer M t) ∣ 294 := by
  simpa only [hJ, Nat.mul_one, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMul]
    using d.pair_card_dvd_centralizer_card

public theorem SylowGeometry.seven_dvd_centralizer_card
    (g : LocalGeometry Z M z t 1) (s : SylowGeometry g) :
    7 ∣ Nat.card (centralizer (residualGenerated M z t : Set G)) := by
  obtain ⟨p, hp, hpJ, hpq⟩ := s.common_prime
  norm_num at hpq
  have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hpq
  exact hp7 ▸ hpJ

public theorem Context.no_odd_primePower_congruence_of_centralizer_card
    (d : Context Z M z t 1)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 14)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hdiv : p ^ a ∣ Nat.card M) : ¬ 7 ∣ p ^ a - 1 :=
  d.no_odd_primePower_congruence_at_eight (d.pair_card_dvd_294_of_centralizer_card hJ)
    hp hp2 ha hdiv

end BenderSuzuki.ZD.SuzukiExclusion
