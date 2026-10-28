module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore.Data
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset

/-!
# The three-part of the first HS local normalizer

The actual normalizer of `elementary 0 = ⟨e0⟩` centralizes the involution `e0`.
Its twenty fixed letters form ten pairs, characterized by their neighborhoods
in the graph already checked in `CentralInvolutionCore.Data`. The induced
simple graph on the ten pairs is the Petersen graph. It has exactly five
independent four-sets, and membership in these sets distinguishes its vertices.

The local normalizer acts on those five sets. An element of the kernel fixes
each pair of fixed letters, so its square fixes all twenty fixed letters.
Neighborhoods among those letters pair all hundred letters, so the fourth
power is the identity. The kernel is therefore a two-group, while the image
has order dividing `5! = 120`. Hence nine cannot divide the local order.

All finite graph, pairing, counting, and separation statements are checked by
the kernel. No local shape, quotient identification, ambient order, Sylow
catalogue, or simplicity assertion is assumed. The private action lemmas keep
this extension independent of changes to the existing two-core module.

Source: GLS volume 3, Table 5.3m, printed p.274, whose central-involution entry
is `(D8 * D8 * 4).S5`; Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528), citing Asc86b. ATLAS attribution and action conventions are those
of the carrier. `CentralNormalizerThreePart/source/generate.py` reproduces the
small additional tables from the retained graph witnesses.
-/

namespace Sporadic.LeechRelated.HS.EvenLocalCandidates
namespace CentralNormalizerThreePart
open Subgroup CentralInvolutionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private theorem carrier_adj (g : Carrier) (i j : Fin 100) :
    adj ((g : Equiv.Perm (Fin 100)) i) ((g : Equiv.Perm (Fin 100)) j) = adj i j := by
  have h : ∀ x ∈ generated, ∀ i j,
      adj (x i) (x j) = adj i j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · rw [← ab0_eq]; exact ab0_adj
      · have hx' : x = generatorB := Set.mem_singleton_iff.mp hx
        subst x
        rw [← ab1_eq]; exact ab1_adj
    | one => intro i j; rfl
    | mul x y _ _ hx hy =>
      intro i j
      exact (hx (y i) (y j)).trans (hy i j)
    | inv x _ hx =>
      intro i j
      simpa using (hx (x⁻¹ i) (x⁻¹ j)).symm
  exact h g g.property i j

private theorem elementary_zero : elementary 0 = closure {e0} := by
  unfold elementary
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    rfl
  · rintro rfl
    exact ⟨(0 : Fin 3), by simp, rfl⟩

private theorem elementary_zero_mem (x : Carrier) :
    x ∈ elementary 0 ↔ x = 1 ∨ x = e0 := by
  rw [elementary_zero]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Or.inr (Set.mem_singleton_iff.mp hy)
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl (one_mul _)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · exact Or.inl e0_mul
    | inv x _ hx =>
      rcases hx with rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (inv_eq_of_mul_eq_one_right e0_mul)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_singleton _)

private theorem local_commutes (g : localGroup 0) : (g : Carrier) * e0 = e0 * g := by
  have he : e0 ∈ elementary 0 := (elementary_zero_mem _).mpr (Or.inr rfl)
  have hc := (mem_normalizer_iff.mp g.property e0).mp he
  rcases (elementary_zero_mem _).mp hc with hc | hc
  · have hh := congrArg (fun x : Carrier => (g : Carrier)⁻¹ * x * g) hc
    have : e0 = 1 := by simpa [mul_assoc] using hh
    exact (e0_nontrivial this).elim
  · exact mul_inv_eq_iff_eq_mul.mp hc

private abbrev act (g : localGroup 0) : Equiv.Perm (Fin 100) := g.val.val

private theorem act_e0 (g : localGroup 0) (i : Fin 100) :
    act g ((e0 : Equiv.Perm (Fin 100)) i) =
      (e0 : Equiv.Perm (Fin 100)) (act g i) :=
  congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) i) (local_commutes g)

private theorem act_fixed (g : localGroup 0) {i : Fin 100}
    (hi : (e0 : Equiv.Perm (Fin 100)) i = i) :
    (e0 : Equiv.Perm (Fin 100)) (act g i) = act g i := by
  rw [← act_e0, hi]

private theorem signature_eq_of (i j : Fin 100)
    (h : ∀ v : Fin 100, (e0 : Equiv.Perm (Fin 100)) v = v → adj i v = adj j v) :
    signature i = signature j := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 100
  · have hi := signature_bits i ⟨k, hk⟩
    have hj := signature_bits j ⟨k, hk⟩
    rw [hi, hj]
    split
    · exact h _ ‹_›
    · rfl
  · have hik : signature i < 2^k := (signature_bound i).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hjk : signature j < 2^k := (signature_bound j).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hik, Nat.testBit_lt_two_pow hjk]

private theorem signature_transport (g : localGroup 0) {i j : Fin 100}
    (h : signature i = signature j) : signature (act g i) = signature (act g j) := by
  apply signature_eq_of
  intro v hv
  have hu := act_fixed g⁻¹ hv
  have hb := congrArg (fun n : ℕ => n.testBit (act g⁻¹ v).val) h
  simp only [signature_bits, if_pos hu] at hb
  calc
    adj (act g i) v = adj i (act g⁻¹ v) := by
      simpa [act] using carrier_adj g.val i (act g⁻¹ v)
    _ = adj j (act g⁻¹ v) := hb
    _ = adj (act g j) v := by
      simpa [act] using (carrier_adj g.val j (act g⁻¹ v)).symm

private theorem act_twin (g : localGroup 0) (i : Fin 100) :
    act g (twin i) = twin (act g i) := by
  have hs := signature_transport g ((signature_class i (twin i)).mpr (Or.inr rfl))
  rcases (signature_class _ _).mp hs with h | h
  · exact (twin_ne i ((act g).injective h)).elim
  · exact h

private theorem twice_of_pair (g : localGroup 0) {i : Fin 100}
    (hi : act g i = i ∨ act g i = twin i) : act g (act g i) = i := by
  rcases hi with hi | hi
  · rw [hi, hi]
  · rw [hi, act_twin, hi, twin_square]


private def rep : Fin 10 → Fin 100 := ![0, 2, 8, 12, 22, 24, 34, 36, 42, 52]
private def pairOf (i : Fin 100) : Fin 10 :=
  ⟨(197010031055615203184203488868686541992801060756677846790217189347526259888505428460229450123804313181623840726319360 >>> (4 * i.val)) % 16 % 10, Nat.mod_lt _ (by decide)⟩
private def edge (i j : Fin 10) : Bool :=
  (239029475073417441828494479884 : ℕ).testBit (10 * i.val + j.val)

private theorem rep_fixed : ∀ i, (e0 : Equiv.Perm (Fin 100)) (rep i) = rep i := by
  apply allFin
  decide +kernel

private theorem pairOf_rep : ∀ i, pairOf (rep i) = i := by
  apply allFin
  decide +kernel

private theorem rep_pairOf : ∀ i : Fin 100, (e0 : Equiv.Perm (Fin 100)) i = i →
    rep (pairOf i) = i ∨ rep (pairOf i) = twin i := by
  apply allFin
  decide +kernel

private theorem pairOf_twin : ∀ i : Fin 100, (e0 : Equiv.Perm (Fin 100)) i = i →
    pairOf (twin i) = pairOf i := by
  apply allFin
  decide +kernel

private theorem pair_adj : ∀ i j : Fin 100,
    (e0 : Equiv.Perm (Fin 100)) i = i →
    (e0 : Equiv.Perm (Fin 100)) j = j →
    adj i j = edge (pairOf i) (pairOf j) := by
  apply allFin
  decide +kernel

private def pairMap (g : localGroup 0) (i : Fin 10) : Fin 10 := pairOf (act g (rep i))

private theorem pairMap_pairOf (g : localGroup 0) (i : Fin 100)
    (hi : (e0 : Equiv.Perm (Fin 100)) i = i) :
    pairMap g (pairOf i) = pairOf (act g i) := by
  unfold pairMap
  rcases rep_pairOf i hi with h | h
  · rw [h]
  · rw [h, act_twin, pairOf_twin _ (act_fixed g hi)]

private theorem pairMap_one (i : Fin 10) : pairMap 1 i = i := pairOf_rep i

private theorem pairMap_mul (g h : localGroup 0) (i : Fin 10) :
    pairMap (g * h) i = pairMap g (pairMap h i) := by
  exact (pairMap_pairOf g (act h (rep i)) (act_fixed h (rep_fixed i))).symm

private def pairPerm (g : localGroup 0) : Equiv.Perm (Fin 10) where
  toFun := pairMap g
  invFun := pairMap g⁻¹
  left_inv i := by rw [← pairMap_mul, inv_mul_cancel, pairMap_one]
  right_inv i := by rw [← pairMap_mul, mul_inv_cancel, pairMap_one]

private def pairHom : localGroup 0 →* Equiv.Perm (Fin 10) where
  toFun := pairPerm
  map_one' := Equiv.ext pairMap_one
  map_mul' g h := Equiv.ext (pairMap_mul g h)

private theorem pairHom_adj (g : localGroup 0) (i j : Fin 10) :
    edge (pairHom g i) (pairHom g j) = edge i j := by
  change edge (pairOf (act g (rep i))) (pairOf (act g (rep j))) = _
  rw [← pair_adj _ _ (act_fixed g (rep_fixed i)) (act_fixed g (rep_fixed j)),
    carrier_adj g.val]
  rw [pair_adj _ _ (rep_fixed i) (rep_fixed j), pairOf_rep, pairOf_rep]

private def IsStar (s : Finset (Fin 10)) : Prop :=
  s.card = 4 ∧ ∀ i ∈ s, ∀ j ∈ s, edge i j = false
private instance (s : Finset (Fin 10)) : Decidable (IsStar s) := inferInstanceAs
  (Decidable (s.card = 4 ∧ ∀ i ∈ s, ∀ j ∈ s, edge i j = false))
private abbrev Star := {s : Finset (Fin 10) // IsStar s}

private theorem card_star : Fintype.card Star = 5 := by decide +kernel

private def starMap (g : localGroup 0) (s : Star) : Star :=
  ⟨s.val.image (pairHom g), by
    constructor
    · rw [Finset.card_image_of_injective _ (pairHom g).injective]
      exact s.property.1
    · intro i hi j hj
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hj
      rw [pairHom_adj]
      exact s.property.2 i hi' j hj'⟩

private theorem starMap_one (s : Star) : starMap 1 s = s := by
  apply Subtype.ext
  change s.val.image (pairHom 1) = s.val
  simp

private theorem starMap_mul (g h : localGroup 0) (s : Star) :
    starMap (g * h) s = starMap g (starMap h s) := by
  apply Subtype.ext
  change s.val.image (pairHom (g * h)) = (s.val.image (pairHom h)).image (pairHom g)
  simp only [Finset.image_image, map_mul, Equiv.Perm.coe_mul]

private def starPerm (g : localGroup 0) : Equiv.Perm Star where
  toFun := starMap g
  invFun := starMap g⁻¹
  left_inv s := by rw [← starMap_mul, inv_mul_cancel, starMap_one]
  right_inv s := by rw [← starMap_mul, mul_inv_cancel, starMap_one]

private def starHom : localGroup 0 →* Equiv.Perm Star where
  toFun := starPerm
  map_one' := Equiv.ext starMap_one
  map_mul' g h := Equiv.ext (starMap_mul g h)

private def stars : Fin 5 → Finset (Fin 10) :=
  ![{0, 1, 7, 8}, {0, 4, 5, 6}, {1, 3, 4, 9}, {2, 3, 6, 7}, {2, 5, 8, 9}]

private theorem stars_valid : ∀ k, IsStar (stars k) := by
  apply allFin
  decide +kernel

private theorem stars_separate : ∀ i j : Fin 10,
    (∀ k : Fin 5, i ∈ stars k ↔ j ∈ stars k) → i = j := by
  apply allFin
  decide +kernel

private theorem ker_fixes_pairs (g : starHom.ker) (i : Fin 10) : pairHom g.val i = i := by
  apply stars_separate
  intro k
  have h := congrArg (fun p : Equiv.Perm Star => (p ⟨stars k, stars_valid k⟩).val)
    (MonoidHom.mem_ker.mp g.property)
  change (stars k).image (pairHom g.val) = stars k at h
  calc
    pairHom g.val i ∈ stars k ↔ pairHom g.val i ∈ (stars k).image (pairHom g.val) := by rw [h]
    _ ↔ i ∈ stars k := Finset.mem_image.trans ⟨by
      rintro ⟨j, hj, he⟩
      exact (pairHom g.val).injective he ▸ hj, by
      intro hi
      exact ⟨i, hi, rfl⟩⟩

private theorem ker_fixed_pair (g : starHom.ker) (i : Fin 100)
    (hi : (e0 : Equiv.Perm (Fin 100)) i = i) :
    act g.val i = i ∨ act g.val i = twin i := by
  have hp : pairOf (act g.val i) = pairOf i := by
    rw [← pairMap_pairOf g.val i hi]
    exact ker_fixes_pairs g (pairOf i)
  have h₁ := rep_pairOf (act g.val i) (act_fixed g.val hi)
  rw [hp] at h₁
  rcases rep_pairOf i hi with h₂ | h₂ <;> rw [h₂] at h₁
  · rcases h₁ with h₁ | h₁
    · exact Or.inl h₁.symm
    · exact Or.inr ((twin_square _).symm.trans (congrArg twin h₁.symm))
  · rcases h₁ with h₁ | h₁
    · exact Or.inr h₁.symm
    · exact Or.inl (by simpa only [twin_square] using congrArg twin h₁.symm)

private theorem pointwise_fixed_pairs (g : localGroup 0)
    (hg : ∀ v : Fin 100, (e0 : Equiv.Perm (Fin 100)) v = v → act g v = v)
    (i : Fin 100) : act g i = i ∨ act g i = twin i := by
  apply (signature_class i (act g i)).mp
  apply signature_eq_of
  intro v hv
  have ha := carrier_adj g.val i v
  rw [hg v hv] at ha
  exact ha.symm

private theorem ker_fourth_power (g : starHom.ker) : g ^ 4 = 1 := by
  have hs : ∀ i : Fin 100, (e0 : Equiv.Perm (Fin 100)) i = i →
      act (g.val ^ 2) i = i := by
    intro i hi
    exact twice_of_pair g.val (ker_fixed_pair g i hi)
  have hp := pointwise_fixed_pairs (g.val ^ 2) hs
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have h := twice_of_pair (g.val ^ 2) (hp i)
  change act (g.val ^ 4) i = i
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two]
  exact h

private theorem ker_isPGroup : IsPGroup 2 starHom.ker := by
  intro g
  exact ⟨2, ker_fourth_power g⟩

end CentralNormalizerThreePart

open Subgroup CentralNormalizerThreePart

/-- Nine does not divide the order of the full normalizer of the first elementary
candidate in the exact degree-100 ATLAS Higman–Sims carrier. -/
public theorem central_localGroup_nine_not_dvd : ¬ 9 ∣ Nat.card (localGroup 0) := by
  obtain ⟨n, hn⟩ := ker_isPGroup.exists_card_eq
  have hcop : Nat.Coprime 9 (Nat.card starHom.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have hperm : Nat.card (Equiv.Perm Star) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, card_star]
    decide
  intro hd
  have hprod := starHom.ker.card_mul_index
  rw [index_ker] at hprod
  rw [← hprod] at hd
  have h := (hcop.dvd_of_dvd_mul_left hd).trans starHom.range.card_subgroup_dvd_card
  rw [hperm] at h
  exact (by decide : ¬ 9 ∣ 120) h

end Sporadic.LeechRelated.HS.EvenLocalCandidates
