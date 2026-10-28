module
public import Theory.Representation.BinaryPermutation.FivePairFixedSpaces
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The unique invariant plane of a five-point Sylow group

The normalizer of the two disjoint transpositions is a Sylow two-subgroup
of S₅. Every vector outside the plane fixed by their product has four
distinct nonzero images under two of its standard generators. A subgroup
of order four invariant under those generators cannot contain that vector.
Sylow conjugacy transports this uniqueness to every Sylow subgroup.
The pointwise plane fixer is the pair four-group; an odd subgroup normalized
by the Sylow group and fixing the plane is therefore that whole four-group.

The finite certificate inspects the sixteen core vectors and three pairs
of generators, rather than a subgroup lattice. Its actual Chapter13.2
consumer identifies Ω₁Z(J(T)) with the original invariant flag plane V₂.
Source: Aschbacher–Smith13.2.11(3), printed p.881.
-/

public section
open Subgroup
open scoped Pointwise
namespace BinaryPermutation.FiveSylowPlane
open FivePairFixedSpaces
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _

private def orbitFive (a b : Perm) (x : U) : Fin 5 → U :=
  ![1,x,actionHom a x,actionHom b x,actionHom b (actionHom a x)]
private def pairA : Fin 3 → Perm := ![first,first,second]
private def pairB : Fin 3 → Perm := ![second,exchange,exchange]
private theorem orbit_certificate : ∀ x : U,
    coreRepresentation (Fin 5) (first * second) x.toAdd = x.toAdd ∨
      ∃ i : Fin 3, Function.Injective (orbitFive (pairA i) (pairB i) x) := by
  decide +kernel

private theorem standard_plane (W : Subgroup U) (hc : Nat.card W = 4)
    (hi : ∀ p ∈ normalizer (pairClosure : Set Perm), ∀ x ∈ W, actionHom p x ∈ W) :
    W = fixedSubgroup (first * second) := by
  apply eq_of_le_of_card_ge ?_ (le_of_eq (card_fixed_product.trans hc.symm))
  intro x hx
  rcases orbit_certificate x with hh | ⟨i, hi5⟩
  · exact hh
  have hmA : pairA i ∈ normalizer (pairClosure : Set Perm) := by
    fin_cases i
    · exact pairClosure.le_normalizer (subset_closure (by simp [pairA]))
    · exact pairClosure.le_normalizer (subset_closure (by simp [pairA]))
    · exact pairClosure.le_normalizer (subset_closure (by simp [pairA]))
  have hmB : pairB i ∈ normalizer (pairClosure : Set Perm) := by
    fin_cases i
    · exact pairClosure.le_normalizer (subset_closure (by simp [pairB]))
    · exact exchange_mem_pairNormalizer
    · exact exchange_mem_pairNormalizer
  let f : Fin 5 → W := fun j => ⟨orbitFive (pairA i) (pairB i) x j, by
    fin_cases j
    · exact W.one_mem
    · exact hx
    · exact hi _ hmA x hx
    · exact hi _ hmB x hx
    · exact hi _ hmB _ (hi _ hmA x hx)⟩
  have hfin : Function.Injective f := fun j k h => hi5 (congrArg Subtype.val h)
  have hh := Nat.card_le_card_of_injective f hfin
  rw [Nat.card_fin, hc] at hh
  omega

private noncomputable def standardSylow : Sylow 2 Perm := Sylow.ofCard
    (normalizer (pairClosure : Set Perm)) (by
  rw [card_pairNormalizer, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  change 8 = 2 ^ (120 : ℕ).factorization 2
  rw [show 120 = 2 ^ 3 * 15 from rfl,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)])

private theorem action_cancel (g : Perm) (x : U) :
    actionHom g⁻¹ (actionHom g x) = x := by
  change Multiplicative.ofAdd (coreRepresentation (Fin 5) g⁻¹
    (coreRepresentation (Fin 5) g x.toAdd)) = x
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rfl

private def coordinateEquiv (g : Perm) : U ≃* U where
  toFun := actionHom g
  invFun := actionHom g⁻¹
  left_inv := action_cancel g
  right_inv x := by simpa only [inv_inv] using action_cancel g⁻¹ x
  map_mul' := (actionHom g).map_mul

private theorem intertwine (g p : Perm) (x : U) :
    actionHom g (actionHom p x) = actionHom (g * p * g⁻¹) (actionHom g x) := by
  apply Multiplicative.toAdd.injective
  change coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) p x.toAdd) =
    coreRepresentation (Fin 5) (g * p * g⁻¹) (coreRepresentation (Fin 5) g x.toAdd)
  simp only [map_mul, Module.End.mul_apply]
  have hi := congrArg Multiplicative.toAdd (action_cancel g x)
  change coreRepresentation (Fin 5) g⁻¹ (coreRepresentation (Fin 5) g x.toAdd) = x.toAdd at hi
  rw [hi]

theorem invariant_plane_eq (P : Sylow 2 Perm) (W₁ W₂ : Subgroup U)
    (h₁ : Nat.card W₁ = 4) (h₂ : Nat.card W₂ = 4)
    (hi₁ : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ W₁, actionHom p x ∈ W₁)
    (hi₂ : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ W₂, actionHom p x ∈ W₂) : W₁ = W₂ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Perm standardSylow P
  have hmap : (standardSylow : Subgroup Perm).map (MulAut.conj g).toMonoidHom = P := by
    exact congrArg (fun Q : Sylow 2 Perm => (Q : Subgroup Perm)) hg
  have standard (W : Subgroup U) (hw : Nat.card W = 4)
      (hinv : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ W, actionHom p x ∈ W) :
      W.comap (coordinateEquiv g).toMonoidHom = fixedSubgroup (first * second) := by
    have hcard : Nat.card (W.comap (coordinateEquiv g).toMonoidHom) = 4 := by
      have hm : (W.comap (coordinateEquiv g).toMonoidHom).map
          (coordinateEquiv g).toMonoidHom = W :=
        map_comap_eq_self_of_surjective (f := (coordinateEquiv g).toMonoidHom)
          (coordinateEquiv g).surjective W
      have hh := congrArg (fun A : Subgroup U => Nat.card A) hm
      rw [card_map_of_injective (f := (coordinateEquiv g).toMonoidHom) (coordinateEquiv g).injective] at hh
      exact hh.trans hw
    apply standard_plane _ hcard
    intro p hp x hx
    change actionHom g (actionHom p x) ∈ W
    rw [intertwine]
    apply hinv _ ?_ _ hx
    rw [← hmap]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hp
  apply (comap_injective (coordinateEquiv g).surjective)
  exact (standard W₁ h₁ hi₁).trans (standard W₂ h₂ hi₂).symm

theorem exists_plane_marking (P : Sylow 2 Perm) (W : Subgroup U)
    (hw : Nat.card W = 4)
    (hinv : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ W, actionHom p x ∈ W) :
    ∃ g : Perm, (P : Subgroup Perm) =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      W = (fixedSubgroup (first * second)).map (actionHom g) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Perm standardSylow P
  have hmap : (standardSylow : Subgroup Perm).map (MulAut.conj g).toMonoidHom = P :=
    congrArg (fun Q : Sylow 2 Perm => (Q : Subgroup Perm)) hg
  have hm : (W.comap (coordinateEquiv g).toMonoidHom).map
      (coordinateEquiv g).toMonoidHom = W :=
    map_comap_eq_self_of_surjective (f := (coordinateEquiv g).toMonoidHom)
      (coordinateEquiv g).surjective W
  have hcard : Nat.card (W.comap (coordinateEquiv g).toMonoidHom) = 4 := by
    have hh := congrArg (fun A : Subgroup U => Nat.card A) hm
    rw [card_map_of_injective (f := (coordinateEquiv g).toMonoidHom) (coordinateEquiv g).injective] at hh
    exact hh.trans hw
  have he : W.comap (coordinateEquiv g).toMonoidHom = fixedSubgroup (first * second) := by
    apply standard_plane _ hcard
    intro p hp x hx
    change actionHom g (actionHom p x) ∈ W
    rw [intertwine]
    apply hinv _ ?_ _ hx
    rw [← hmap]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hp
  exact ⟨g, hmap.symm, hm.symm.trans (congrArg (map (coordinateEquiv g).toMonoidHom) he)⟩

private theorem standard_fixer (p : Perm) :
    (∀ x : U, x ∈ fixedSubgroup (first * second) → actionHom p x = x) ↔ p ∈ pairClosure := by
  rw [mem_pairClosure]
  have hh : ∀ p : Perm,
      (∀ x : U, coreRepresentation (Fin 5) (first * second) x.toAdd = x.toAdd →
        actionHom p x = x) ↔ p = 1 ∨ p = first ∨ p = second ∨ p = first * second := by
    decide +kernel
  exact hh p

theorem fixes_marked_plane_iff (g p : Perm) :
    (∀ x ∈ (fixedSubgroup (first * second)).map (actionHom g), actionHom p x = x) ↔
      p ∈ pairClosure.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hp
    have hginv : g⁻¹ * p * g ∈ pairClosure := by
      apply (standard_fixer _).mp
      intro x hx
      apply (coordinateEquiv g).injective
      have he := intertwine g (g⁻¹ * p * g) x
      have hconj : g * (g⁻¹ * p * g) * g⁻¹ = p := by simp [mul_assoc]
      rw [hconj] at he
      change actionHom g (actionHom (g⁻¹ * p * g) x) = actionHom g x
      rw [he]
      exact hp _ (mem_map_of_mem (actionHom g) hx)
    refine ⟨g⁻¹ * p * g, hginv, ?_⟩
    change g * (g⁻¹ * p * g) * g⁻¹ = p
    simp [mul_assoc]
  · rintro ⟨a, ha, rfl⟩ x ⟨y, hy, rfl⟩
    change actionHom (g * a * g⁻¹) (actionHom g y) = actionHom g y
    rw [← intertwine, (standard_fixer a).mpr ha y hy]

private theorem standard_odd_normal (A : Subgroup Perm) (hA : A ≤ pairClosure)
    (hn : normalizer (pairClosure : Set Perm) ≤ normalizer (A : Set Perm))
    (ho : ¬ A ≤ alternatingGroup (Fin 5)) : A = pairClosure := by
  obtain ⟨a, ha, hao⟩ := SetLike.not_le_iff_exists.mp ho
  have hboth : first ∈ A ∧ second ∈ A := by
    rcases (mem_pairClosure a).mp (hA ha) with rfl | rfl | rfl | rfl
    · exact (hao (one_mem _)).elim
    · exact ⟨ha, exchange_first ▸ (mem_normalizer_iff.mp (hn exchange_mem_pairNormalizer) first).mp ha⟩
    · exact ⟨exchange_second ▸ (mem_normalizer_iff.mp (hn exchange_mem_pairNormalizer) second).mp ha, ha⟩
    · have hh : first * second ∈ alternatingGroup (Fin 5) := by
        change Equiv.Perm.sign (first * second) = 1
        decide +kernel
      exact (hao hh).elim
  apply le_antisymm hA
  apply (closure_le _).mpr
  rintro p (rfl | hp)
  · exact hboth.1
  · exact (show p = second from hp) ▸ hboth.2

theorem exists_plane_and_normal_odd_marking
    (P : Sylow 2 Perm) (W : Subgroup U) (A : Subgroup Perm)
    (hw : Nat.card W = 4)
    (hinv : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ W, actionHom p x ∈ W)
    (hn : (P : Subgroup Perm) ≤ normalizer (A : Set Perm))
    (hfix : ∀ a ∈ A, ∀ x ∈ W, actionHom a x = x)
    (ho : ¬ A ≤ alternatingGroup (Fin 5)) :
    ∃ g : Perm, (P : Subgroup Perm) =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      W = (fixedSubgroup (first * second)).map (actionHom g) ∧
      A = pairClosure.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hP, hW⟩ := exists_plane_marking P W hw hinv
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hcancel (D : Subgroup Perm) :
      (D.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = D := by
    change (D.conjBy g⁻¹).conjBy g = D
    rw [conjBy_conjBy, mul_inv_cancel, conjBy_one]
  have hB : B ≤ pairClosure := by
    rintro a ⟨a, ha, rfl⟩
    apply (standard_fixer _).mp
    intro x hx
    apply (coordinateEquiv g).injective
    have he := intertwine g (g⁻¹ * a * g) x
    have hconj : g * (g⁻¹ * a * g) * g⁻¹ = a := by simp [mul_assoc]
    rw [hconj] at he
    change actionHom g (actionHom (g⁻¹ * a * g) x) = actionHom g x
    rw [he]
    apply hfix a ha
    rw [hW]
    exact mem_map_of_mem (actionHom g) hx
  have hnB : normalizer (pairClosure : Set Perm) ≤ normalizer (B : Set Perm) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn).trans
      (A.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    rw [hP] at hh
    have he : ((normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = normalizer (pairClosure : Set Perm) := by
      change ((normalizer (pairClosure : Set Perm)).conjBy g).conjBy g⁻¹ = _
      rw [conjBy_conjBy, inv_mul_cancel, conjBy_one]
    rwa [he] at hh
  have hoB : ¬ B ≤ alternatingGroup (Fin 5) := by
    intro he
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) he
    rw [hcancel] at hh
    have heven : (alternatingGroup (Fin 5)).map (MulAut.conj g).toMonoidHom =
        alternatingGroup (Fin 5) := Subgroup.Normal.map_conj_eq (alternatingGroup (Fin 5)) g
    rw [heven] at hh
    exact ho hh
  have he := standard_odd_normal B hB hnB hoB
  refine ⟨g, hP, hW, ?_⟩
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) he
  rw [hcancel] at hh
  exact hh

end BinaryPermutation.FiveSylowPlane
