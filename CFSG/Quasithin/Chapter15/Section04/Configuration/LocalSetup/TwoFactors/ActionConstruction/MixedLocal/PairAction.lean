module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.LocalSylow
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.IndexNormal

/-!
# The mixed factor stabilizer and its local Sylow subgroup

The permutation action is tied to conjugation of two distinct ambient subgroups.
Its kernel identifies the relative normalizer and proves index two and relative
normality. A subgroup centralizing exactly one factor has its centralizer inside
that stabilizer. Restriction of the given Sylow subgroup to the normal stabilizer
then constructs the Sylow subgroup of the local centralizer, with its exact
ambient image.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the first three paragraphs of 15.4.18, printed p.1162.
The realized pair action is an explicit input; no local Sylow witness is assumed.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
open Subgroup
variable {G : Type*} [Group G]

/-- The action is on the actual two subgroups, by ambient conjugation. -/
structure FactorPairAction (M : Subgroup G) (L : Bool → Subgroup G) where
  distinct : Function.Injective L
  permutation : M →* Equiv.Perm Bool
  conjugation : ∀ (m : M) (i : Bool),
    (L i).map (MulAut.conj (m : G)).toMonoidHom = L (permutation m i)

private theorem perm_bool_eq_one_iff (q : Equiv.Perm Bool) :
    q false = false ↔ q = 1 := by
  revert q
  decide

/-- The kernel is precisely the relative factor normalizer. -/
theorem FactorPairAction.kernel {M : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) :
    a.permutation.ker = (normalizer (L false : Set G)).subgroupOf M := by
  ext m
  change a.permutation m = 1 ↔ (m : G) ∈ normalizer (L false : Set G)
  rw [mem_normalizer_iff_map_conj_eq]
  change a.permutation m = 1 ↔
    (L false).map (MulAut.conj (m : G)).toMonoidHom = L false
  rw [a.conjugation]
  exact (perm_bool_eq_one_iff _).symm.trans a.distinct.eq_iff.symm

/-- Restriction retains the actual conjugation action on the same pair. -/
def FactorPairAction.restrict {M T : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) (hTM : T ≤ M) : FactorPairAction T L where
  distinct := a.distinct
  permutation := a.permutation.comp (inclusion hTM)
  conjugation t i := a.conjugation (inclusion hTM t) i

/-- An element moving the first factor proves that its stabilizer has index two. -/
theorem FactorPairAction.stabilizer_index {M : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) {t : G} (ht : t ∈ M)
    (hmove : t ∉ normalizer (L false : Set G)) :
    (M ⊓ normalizer (L false : Set G)).relIndex M = 2 := by
  rw [inf_relIndex_left]
  change ((normalizer (L false : Set G)).subgroupOf M).index = 2
  rw [← a.kernel, index_ker]
  have hupper : Nat.card a.permutation.range ≤ 2 := by
    have h := Nat.card_le_card_of_injective a.permutation.range.subtype
      a.permutation.range.subtype_injective
    simpa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_perm] using h
  have hne : a.permutation.range ≠ ⊥ := by
    intro hb
    have hp : a.permutation ⟨t, ht⟩ = 1 :=
      mem_bot.mp (hb ▸ (show a.permutation ⟨t, ht⟩ ∈ a.permutation.range from ⟨⟨t, ht⟩, rfl⟩))
    apply hmove
    have hk : (⟨t, ht⟩ : M) ∈ a.permutation.ker := hp
    rwa [a.kernel] at hk
  exact Nat.le_antisymm hupper (a.permutation.range.one_lt_card_iff_ne_bot.mpr hne)

/-- The stabilizer is normal in the group acting on the pair. -/
theorem FactorPairAction.normalizes_stabilizer {M : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) :
    M ≤ normalizer ((M ⊓ normalizer (L false : Set G) : Subgroup G) : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
  have he : (M ⊓ normalizer (L false : Set G)).subgroupOf M = a.permutation.ker := by
    rw [inf_subgroupOf_left, ← a.kernel]
  rw [he]
  infer_instance

/-- A subgroup centralizing exactly the first factor cannot be fixed by an
actor interchanging the factors. -/
theorem FactorPairAction.centralizer_le_stabilizer
    {M B : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L)
    (hB : B ≤ centralizer (L false : Set G))
    (hnot : ¬ B ≤ centralizer (L true : Set G)) :
    M ⊓ centralizer (B : Set G) ≤ M ⊓ normalizer (L false : Set G) := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  by_contra hn
  have hp : a.permutation ⟨m, hm.1⟩ false = true := by
    cases he : a.permutation ⟨m, hm.1⟩ false with
    | false =>
      have hk : (⟨m, hm.1⟩ : M) ∈ a.permutation.ker :=
        (perm_bool_eq_one_iff _).mp he
      rw [a.kernel] at hk
      exact (hn hk).elim
    | true => rfl
  have hmap : (L false).map (MulAut.conj m).toMonoidHom = L true :=
    (a.conjugation ⟨m, hm.1⟩ false).trans (congrArg L hp)
  apply hnot
  intro b hb
  apply mem_centralizer_iff.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_map.mp (hmap.symm ▸ hy)
  have hfix : (MulAut.conj m) b = b := by
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hm.2 b hb).symm)
  have hc := congrArg (MulAut.conj m) (mem_centralizer_iff.mp (hB hb) x hx)
  change (MulAut.conj m) x * b = b * (MulAut.conj m) x
  simpa only [map_mul, hfix] using hc

/-- Generation by the two factors is already generation by one factor and
the subgroup containing an element interchanging them. -/
theorem pair_join_eq_of_swap {T X : Subgroup G} {L : Bool → Subgroup G}
    (hX : L false ⊔ L true = X) {t : G} (ht : t ∈ T)
    (hswap : (L false).map (MulAut.conj t).toMonoidHom = L true) :
    L false ⊔ T = X ⊔ T := by
  apply le_antisymm
  · exact sup_le_sup (hX ▸ le_sup_left) le_rfl
  · apply sup_le _ le_sup_right
    rw [← hX]
    refine sup_le le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp (hswap.symm ▸ hy)
    exact (L false ⊔ T).mul_mem
      ((L false ⊔ T).mul_mem (mem_sup_right ht) (mem_sup_left hx))
      (mem_sup_right (T.inv_mem ht))

variable [Finite G]

/-- Restrict an ambient Sylow subgroup to the normal factor stabilizer,
then to the centralizer which it contains. The resulting Sylow subgroup has
exactly the prescribed image, without conjugating the given Sylow subgroup. -/
theorem local_sylow_of_pair_action (T : Sylow 2 G)
    {M B : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) (hTM : (T : Subgroup G) ≤ M)
    (hB : B ≤ centralizer (L false : Set G))
    (hnot : ¬ B ≤ centralizer (L true : Set G))
    (hTC : (T : Subgroup G) ⊓ normalizer (L false : Set G) ≤
      centralizer (B : Set G)) :
    ∃ P : Sylow 2 (M ⊓ centralizer (B : Set G) : Subgroup G),
      (P : Subgroup (M ⊓ centralizer (B : Set G) : Subgroup G)).map
        (M ⊓ centralizer (B : Set G) : Subgroup G).subtype =
          (T : Subgroup G) ⊓ normalizer (L false : Set G) := by
  let N := normalizer (L false : Set G)
  let C := M ⊓ centralizer (B : Set G)
  let H := M ⊓ N
  let TM : Sylow 2 M := T.comapOfInjective M.subtype M.subtype_injective (by
    simpa only [range_subtype] using hTM)
  let HM := H.subgroupOf M
  have : HM.Normal := normal_subgroupOf_of_le_normalizer a.normalizes_stabilizer
  obtain ⟨Q, hQ⟩ := TM.exists_subgroupOf_eq_of_normal HM
  have hindex : ¬ 2 ∣ ((T : Subgroup G) ⊓ N).relIndex H := by
    have hqi := Q.not_dvd_index
    rw [hQ] at hqi
    change ¬ 2 ∣ (TM : Subgroup M).relIndex HM at hqi
    have hte : (TM : Subgroup M) = (T : Subgroup G).subgroupOf M := rfl
    rw [hte, relIndex_subgroupOf (show H ≤ M from inf_le_left)] at hqi
    have he : ((T : Subgroup G) ⊓ N).subgroupOf H = (T : Subgroup G).subgroupOf H := by
      ext x
      change ((x : G) ∈ (T : Subgroup G) ∧ (x : G) ∈ N) ↔ (x : G) ∈ (T : Subgroup G)
      exact and_iff_left x.property.2
    change ¬ 2 ∣ (((T : Subgroup G) ⊓ N).subgroupOf H).index
    rwa [he]
  have hCH : C ≤ H := a.centralizer_le_stabilizer hB hnot
  have hTiC : (T : Subgroup G) ⊓ N ≤ C :=
    le_inf (inf_le_left.trans hTM) hTC
  have hidxC : ¬ 2 ∣ ((T : Subgroup G) ⊓ N).relIndex C := by
    intro hd
    apply hindex
    exact hd.trans (dvd_of_mul_right_eq _ (relIndex_mul_relIndex _ C H hTiC hCH))
  let P : Sylow 2 C := ((T.isPGroup'.to_le inf_le_left).comap_subtype).toSylow hidxC
  exact ⟨P, map_subgroupOf_eq_of_le hTiC⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
