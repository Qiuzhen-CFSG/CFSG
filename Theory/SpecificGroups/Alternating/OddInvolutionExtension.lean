module

public import Theory.SpecificGroups.Alternating.TranspositionExtension

/-!
# Extending an alternating embedding across an odd involution

An involution acting on an embedded Aₙ by an odd permutation extends the
embedding to Sₙ. The map retains the whole alternating subgroup and the
specified involution. Its range is exactly their join. The semidirect-product
proof extends `TranspositionExtension` to odd involutions of arbitrary cycle
type; in particular it includes the triple transpositions of S₈.
For n ≥ 5, n ≠ 6, the existing automorphism theorem supplies such a
permutation from an ambient outer involution. Sign and the order bound
also give the two possible odd involution cycle types in degree eight.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed p.1192, the identification LR ≅ Sₙ.
-/

open Subgroup Equiv Equiv.Perm
open QuaternionGroup (cyclicPowerHom cyclicPowerHom_one)

namespace Theory.SpecificGroups.Alternating.OddInvolutionExtension

private abbrev C2 := Multiplicative (ZMod 2)

private def involutionPower {n : ℕ} (s : Perm (Fin n)) (hs : s ^ 2 = 1) : C2 →* Perm (Fin n) :=
  cyclicPowerHom 2 s hs

private abbrev involutionAction {n : ℕ} (s : Perm (Fin n)) (hs : s ^ 2 = 1) :
    C2 →* MulAut (alternatingGroup (Fin n)) :=
  MulAut.conjNormal.comp (involutionPower s hs)

private def standardMap {n : ℕ} (s : Perm (Fin n)) (hs : s ^ 2 = 1) :
    alternatingGroup (Fin n) ⋊[involutionAction s hs] C2 →* Perm (Fin n) :=
  SemidirectProduct.lift (alternatingGroup (Fin n)).subtype (involutionPower s hs)
    (by intro c; ext k; rfl)

private theorem standardMap_bijective {n : ℕ} (s : Perm (Fin n)) (hs : s ^ 2 = 1) (hodd : sign s = -1) :
    Function.Bijective (standardMap s hs) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    rintro ⟨k, c⟩ hp
    change (k : Perm (Fin n)) * involutionPower s hs c = 1 at hp
    change ZMod 2 at c
    fin_cases c
    · have hk : k = 1 := by
        apply Subtype.ext
        change (k : Perm (Fin n)) * involutionPower s hs 1 = 1 at hp
        simpa only [map_one, mul_one, Subgroup.coe_one] using hp
      subst k
      rfl
    · have hp' : (k : Perm (Fin n)) * s = 1 := by
        change (k : Perm (Fin n)) * involutionPower s hs (Multiplicative.ofAdd 1) = 1 at hp
        simpa only [involutionPower, cyclicPowerHom_one] using hp
      have hsign := congrArg sign hp'
      have hk := mem_alternatingGroup.mp k.property
      simp only [map_mul, hk, hodd, one_mul, map_one] at hsign
      norm_num at hsign
  · intro p
    rcases Int.units_eq_one_or (sign p) with hp | hp
    · refine ⟨SemidirectProduct.inl ⟨p, mem_alternatingGroup.mpr hp⟩, ?_⟩
      simp [standardMap]
    · let k : alternatingGroup (Fin n) := ⟨p * s, by
        rw [mem_alternatingGroup, map_mul, hp, hodd]
        simp⟩
      refine ⟨SemidirectProduct.inl k *
        SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
      simp [standardMap, involutionPower, cyclicPowerHom_one, k, mul_assoc, show s * s = 1 from by simpa only [pow_two] using hs]

/-- A compatible involution extends an alternating embedding to an embedding
of the actual symmetric group, retaining both marked maps. -/
public theorem exists_embedding {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (s : Perm (Fin n)) (hs : s ^ 2 = 1) (hodd : sign s = -1)
    (f : alternatingGroup (Fin n) →* G) (hf : Function.Injective f)
    (t : G) (ht : t ^ 2 = 1)
    (haction : ∀ k, f (MulAut.conjNormal s k) = t * f k * t⁻¹) :
    ∃ F : Perm (Fin n) →* G, Function.Injective F ∧
      (∀ k : alternatingGroup (Fin n), F k = f k) ∧ F s = t := by
  let g : C2 →* G := cyclicPowerHom 2 t ht
  have hcompat (c : C2) :
      f.comp (involutionAction s hs c).toMonoidHom = (MulAut.conj (g c)).toMonoidHom.comp f := by
    ext k
    change f (MulAut.conjNormal (involutionPower s hs c) k) = g c * f k * (g c)⁻¹
    change ZMod 2 at c
    fin_cases c
    · change f (MulAut.conjNormal (involutionPower s hs 1) k) = g 1 * f k * (g 1)⁻¹
      simp
    · change f (MulAut.conjNormal (involutionPower s hs (Multiplicative.ofAdd 1)) k) =
        g (Multiplicative.ofAdd 1) * f k * (g (Multiplicative.ofAdd 1))⁻¹
      simpa only [involutionPower, g, cyclicPowerHom_one] using haction k
  let L := SemidirectProduct.lift f g hcompat
  let e := MulEquiv.ofBijective (standardMap s hs) (standardMap_bijective s hs hodd)
  let F : Perm (Fin n) →* G := L.comp e.symm.toMonoidHom
  have hFk (k : alternatingGroup (Fin n)) : F k = f k := by
    have hk : e.symm k = SemidirectProduct.inl k := by
      apply e.injective
      simp [e, standardMap]
    change L (e.symm k) = f k
    rw [hk]
    exact SemidirectProduct.lift_inl _ _ _ _
  have hFt : F s = t := by
    have ht' : e.symm s = SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
      apply e.injective
      simp [e, standardMap, involutionPower, cyclicPowerHom_one]
    change L (e.symm s) = t
    rw [ht']
    simp [L, g, cyclicPowerHom_one]
  refine ⟨F, ?_, hFk, hFt⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro p hp
  have hFp : F p = 1 := hp
  have hconj : MulAut.conjNormal (H := alternatingGroup (Fin n)) p = 1 := by
    apply MulEquiv.ext
    intro k
    change MulAut.conjNormal p k = k
    apply hf
    calc
      f (MulAut.conjNormal p k) = F (p * (k : Perm (Fin n)) * p⁻¹) :=
        (hFk (MulAut.conjNormal p k)).symm
      _ = f k := by rw [map_mul, map_mul, map_inv, hFp, hFk]; simp
  exact (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn)
    (hconj.trans (map_one _).symm)

/-- The marked extension has precisely the subgroup generated by its
alternating image and the marked involution as its image. -/
public theorem range_eq {G : Type*} [Group G] {n : ℕ}
    (s : Perm (Fin n)) (hs : s ^ 2 = 1) (hodd : sign s = -1) (f : alternatingGroup (Fin n) →* G)
    (F : Perm (Fin n) →* G) (t : G)
    (hFk : ∀ k : alternatingGroup (Fin n), F k = f k) (hFt : F s = t) :
    F.range = f.range ⊔ zpowers t := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rcases Int.units_eq_one_or (sign p) with hp | hp
    · rw [hFk ⟨p, mem_alternatingGroup.mpr hp⟩]
      exact mem_sup_left ⟨_, rfl⟩
    · let k : alternatingGroup (Fin n) := ⟨p * s, by
        rw [mem_alternatingGroup, map_mul, hp, hodd]
        simp⟩
      have hp' : p = (k : Perm (Fin n)) * s := by simp [k, mul_assoc, show s * s = 1 from by simpa only [pow_two] using hs]
      rw [hp', map_mul, hFk, hFt]
      exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right (mem_zpowers t))
  · apply sup_le
    · rintro _ ⟨k, rfl⟩
      exact ⟨k, hFk k⟩
    · exact zpowers_le.mpr ⟨s, hFt⟩

variable {G : Type*} [Group G]

private theorem normalizer_action_not_inner {L : Subgroup G} {r : G}
    (hrN : r ∈ normalizer (L : Set G))
    (hrout : r ∉ centralizer (L : Set G) ⊔ L) :
    ∀ l : L, L.normalizerMonoidHom ⟨r, hrN⟩ ≠ MulAut.conj l := by
  intro l hl
  let lN : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  have hlN : L.normalizerMonoidHom lN = MulAut.conj l := by ext x; rfl
  have hk : (⟨r, hrN⟩ : normalizer (L : Set G)) * lN⁻¹ ∈
      L.normalizerMonoidHom.ker := by
    change L.normalizerMonoidHom (_ * _) = 1
    rw [map_mul, map_inv, hlN, hl, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hmem := (centralizer (L : Set G) ⊔ L).mul_mem
    (mem_sup_left (show r * (l : G)⁻¹ ∈ centralizer (L : Set G) from hk))
    (mem_sup_right l.property)
  exact hrout (by simpa using hmem)

/-- Outside degree six, an ambient outer involution has compatible odd permutation coordinates. -/
public theorem exists_odd_involution_action {L : Subgroup G} {r : G} {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : L ≃* alternatingGroup (Fin n))
    (hrN : r ∈ normalizer (L : Set G)) (hr2 : r ^ 2 = 1)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L) :
    ∃ s : Perm (Fin n), s ^ 2 = 1 ∧ sign s = -1 ∧
      ∀ k : alternatingGroup (Fin n),
        (e.symm (MulAut.conjNormal s k) : G) = r * (e.symm k : G) * r⁻¹ := by
  let a := L.normalizerMonoidHom ⟨r, hrN⟩
  let b := MulAut.congr e a
  obtain ⟨s, hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 b
  have ha2 : a ^ 2 = 1 := by
    change L.normalizerMonoidHom ⟨r, hrN⟩ ^ 2 = 1
    rw [← map_pow, show (⟨r, hrN⟩ : normalizer (L : Set G)) ^ 2 = 1 from Subtype.ext hr2,
      map_one]
  have hs2 : s ^ 2 = 1 := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
    rw [map_pow, map_one, hs]
    change MulAut.congr e a ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  have haction (k : alternatingGroup (Fin n)) :
      (e.symm (MulAut.conjNormal s k) : G) = r * (e.symm k : G) * r⁻¹ := by
    rw [hs]
    change (e.symm (e (a (e.symm k))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨s, hs2, ?_, haction⟩
  rcases Int.units_eq_one_or (sign s) with hs1 | hsm
  · exfalso
    let k : alternatingGroup (Fin n) := ⟨s, mem_alternatingGroup.mpr hs1⟩
    apply normalizer_action_not_inner hrN hrout (e.symm k)
    apply (MulAut.congr e).injective
    change b = _
    rw [← hs]
    apply MulEquiv.ext
    intro x
    change MulAut.conjNormal s x = e ((e.symm k) * (e.symm x) * (e.symm k)⁻¹)
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
    rfl
  · exact hsm

/-- The two possible odd involution cycle types in S₈. -/
public theorem odd_involution_eight_cycleType (s : Perm (Fin 8))
    (hs : s ^ 2 = 1) (hodd : sign s = -1) :
    s.cycleType = {2} ∨ s.cycleType = {2, 2, 2} := by
  have ht := cycleType_of_pow_prime_eq_one hs
  have hbound := s.sum_cycleType_le
  rw [ht] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := sign_of_cycleType' s
  rw [ht] at hsign
  simp only [Multiset.map_replicate, Multiset.prod_replicate] at hsign
  have hcard : s.cycleType.card ≤ 4 := by omega
  interval_cases h : s.cycleType.card <;> simp_all
  exact ((by decide : (-1 : ℤˣ) ^ 4 ≠ -1) hodd).elim

end Theory.SpecificGroups.Alternating.OddInvolutionExtension
