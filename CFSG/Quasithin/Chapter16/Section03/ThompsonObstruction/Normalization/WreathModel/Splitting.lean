module
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.WreathModel.SylowIntersection
public import Theory.Alternating.Aut
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Splitting the local Sylow at its central involution

The marked S₈ extension has trivial centralizer of its A₈, so the central
factor ⟨t⟩ is disjoint from Q = (P ∩ K)⟨z⟩. The two factors commute. Their
join has order 256. Conversely, conjugation on K has kernel ⟨t⟩ on P and
image a two-subgroup of Aut(K) ≃ S₈, so P has order at most 256. Thus the
two factors generate P. Normality is used only relative to C_G(t).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, completion of
the proof of Theorem 16.3.7, printed p.1182 / PDF p.1199; the automorphism
identification is supplied by Theory.Alternating.Aut.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The centralizer of K within its marked S₈ extension is trivial. -/
theorem MarkedEnlargement.extension_centralizer_eq_bot (d : MarkedEnlargement z t L) :
    (enlargement t L ⊔ zpowers z) ⊓ centralizer (enlargement t L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hxE, hxC⟩
  let a : ↥(enlargement t L ⊔ zpowers z) := ⟨x, hxE⟩
  have he : d.equiv a ∈ centralizer (alternatingGroup (Fin 8) : Set (Equiv.Perm (Fin 8))) := by
    intro b hb
    rw [← d.enlargement_image] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    change d.equiv k * d.equiv a = d.equiv a * d.equiv k
    rw [← map_mul, ← map_mul]
    exact congrArg d.equiv (Subtype.ext (mem_centralizer_iff.mp hxC k hk))
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide)] at he
  have ha : a = 1 := d.equiv.injective (he.trans (map_one d.equiv).symm)
  exact congrArg Subtype.val ha

/-- The two prospective direct factors intersect trivially. -/
theorem Selected.centralFactor_disjoint_wreathFactor (s : Selected T z t L) :
    Disjoint (zpowers t) ((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z) := by
  have htC : t ∈ centralizer (enlargement t L : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mp (s.marked.component.1 hk)
  apply disjoint_def.mpr
  intro x hxA hxQ
  have hx : x ∈ (enlargement t L ⊔ zpowers z) ⊓
      centralizer (enlargement t L : Set G) :=
    ⟨s.wreath_factor_le_extension hxQ, (zpowers_le.mpr htC) hxA⟩
  rwa [s.marked.extension_centralizer_eq_bot] at hx

/-- The involution factor centralizes Q inside C_G(t). -/
theorem Selected.centralFactor_centralizes_wreathFactor (s : Selected T z t L) :
    zpowers t ≤ centralizer
      (((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z : Subgroup G) : Set G) := by
  apply zpowers_le.mpr
  intro q hq
  exact mem_centralizer_singleton_iff.mp
    (map_subtype_le _ (s.wreath_factor_le_localSylow hq))

/-- The actual automorphism group of the marked enlargement has order 8!. -/
theorem MarkedEnlargement.automorphism_card (d : MarkedEnlargement z t L) :
    Nat.card (MulAut (enlargement t L)) = 40320 := by
  let e := MulAut.congr d.enlargementEquivAlternating
  let a := MulEquiv.ofBijective
    (MulAut.conjNormal : Equiv.Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card]
  norm_num [Fintype.card_perm]

variable [Finite G]

/-- Conjugation on K bounds P by its order-two kernel and an S₈ Sylow image. -/
theorem Selected.localSylow_card_le (s : Selected T z t L) :
    Nat.card (localSylow s.P) ≤ 256 := by
  let H := localSylow s.P
  let K := enlargement t L
  change Nat.card H ≤ 256
  have hHN : H ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer s.marked.component.1).mp
      (s.marked.enlargement_normal s.counterexample.involution))
  let f : H →* MulAut K := K.normalizerMonoidHom.comp (inclusion hHN)
  have hker : f.ker = (zpowers t).subgroupOf H := by
    ext x
    change inclusion hHN x ∈ K.normalizerMonoidHom.ker ↔ (x : G) ∈ zpowers t
    rw [normalizerMonoidHom_ker]
    change (x : G) ∈ centralizer (K : Set G) ↔ (x : G) ∈ zpowers t
    have h := s.marked.localSylow_centralizer_eq s.P s.t_mem_localSylow
    constructor
    · intro hx
      rw [← h]
      exact ⟨x.property, hx⟩
    · intro hx
      rw [← h] at hx
      exact hx.2
  have hkc : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe
      (zpowers_le.mpr s.t_mem_localSylow)).toEquiv, Nat.card_zpowers,
      s.counterexample.involution]
  have hHP : IsPGroup 2 H := s.P.isPGroup'.map _
  have hrP : IsPGroup 2 f.range := by
    rw [MonoidHom.range_eq_map]
    exact (hHP.to_subgroup ⊤).map f
  obtain ⟨AS, hAS⟩ := hrP.exists_le_sylow
  have hAScard : Nat.card AS = 128 := by
    rw [AS.card_eq_multiplicity, s.marked.automorphism_card,
      show 40320 = 2 ^ 7 * 315 by rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  have hrc : Nat.card f.range ≤ 128 := by
    rw [← hAScard]
    exact Nat.card_le_card_of_injective (inclusion hAS) (inclusion_injective _)
  have hcard := f.ker.card_mul_index
  rw [index_ker, hkc] at hcard
  omega

/-- The disjoint commuting factors generate the entire local Sylow. -/
theorem Selected.centralFactor_sup_wreathFactor (s : Selected T z t L) :
    zpowers t ⊔ ((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z) = localSylow s.P := by
  apply eq_of_le_of_card_ge
    (sup_le (zpowers_le.mpr s.t_mem_localSylow) s.wreath_factor_le_localSylow)
  rw [sup_comm, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (s.centralFactor_centralizes_wreathFactor.trans (centralizer_le_normalizer _))
    s.centralFactor_disjoint_wreathFactor.symm,
    s.wreath_factor_card, Nat.card_zpowers, s.counterexample.involution]
  exact s.localSylow_card_le

end CFSG.Quasithin.Chapter16.ThompsonObstruction
