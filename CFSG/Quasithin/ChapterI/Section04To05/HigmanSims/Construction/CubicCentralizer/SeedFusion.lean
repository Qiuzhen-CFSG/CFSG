module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.LocalOrder
public import Theory.GroupTheory.CoprimePrimeFusion

/-!
# Original seed-class fusion inside a cubic centralizer

All cubics in the original marked involution centralizer are conjugate there:
the original five-letter quotient has one cubic class, and the kernel has
order64. An ambient conjugator between seed-class involutions commuting with
the same cubic can therefore be corrected to centralize that cubic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem three_cycle_type (s : Equiv.Perm (Fin 5)) (hs : orderOf s = 3) :
    s.cycleType = {3} := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := s) (by rw [hs]; decide)
  have hh := s.sum_cycleType_le
  rw [hn, hs, Multiset.sum_replicate] at hh
  have hn0 : n = 0 := by
    simp only [nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hh
    omega
  simpa [hn0, hs] using hn

/-- The original marked involution centralizer has a single class of
order-three elements, with conjugacy occurring inside that full centralizer. -/
theorem TypeAt.cubic_point_isConj (h : TypeAt z V)
    (s t : involutionCentralizer z) (hs : orderOf s = 3) (ht : orderOf t = 3) :
    IsConj s t := by
  obtain ⟨f, _, hf, hk, _⟩ := h.exists_overlap_five_marking
  have hk64 : Nat.card f.ker = 64 := by
    rw [hk, ←h.centralizer_fitting]
    exact h.centralizer_core_card
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  have hfs : orderOf (f s) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hp s (by rw [hs]; decide)).trans hs
  have hft : orderOf (f t) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hp t (by rw [ht]; decide)).trans ht
  apply f.isConj_of_map_isConj_of_prime_order_of_coprime_ker hf
    (by rw [hk64]; decide : Nat.Coprime 3 (Nat.card f.ker)) hs ht
  exact Equiv.Perm.isConj_of_cycleType_eq
    ((three_cycle_type (f s) hfs).trans (three_cycle_type (f t) hft).symm)

/-- An involution in the original marked conjugacy class that centralizes
the specified cubic is conjugate to the marked involution inside the full
original cubic centralizer. No assertion is made about other classes. -/
theorem TypeAt.cubic_centralizer_seed_fusion (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3)
    (x : G) (hxC : x ∈ centralizer ({t} : Set G)) (hxz : IsConj x z) :
    ∃ g : G, g ∈ centralizer ({t} : Set G) ∧ g * x * g⁻¹ = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxz
  let a := MulAut.conj g
  have hax : a x = z := hg
  have hcomm : Commute (a t) z := by
    rw [←hax]
    exact (show Commute t x from
      (mem_centralizer_singleton_iff.mp hxC).symm).map a.toMonoidHom
  have hat : a t ∈ involutionCentralizer z := mem_centralizer_singleton_iff.mpr hcomm.eq
  let s : involutionCentralizer z := ⟨a t, hat⟩
  let tH : involutionCentralizer z := ⟨t, ht⟩
  have hs3 : orderOf s = 3 :=
    (orderOf_coe s).symm.trans ((a.orderOf_eq t).trans ht3)
  have htH3 : orderOf tH = 3 := (orderOf_coe tH).symm.trans ht3
  obtain ⟨k, hk⟩ := isConj_iff.mp (h.cubic_point_isConj s tH hs3 htH3)
  have hkt : (k : G) * (g * t * g⁻¹) * (k : G)⁻¹ = t :=
    congrArg Subtype.val hk
  have hkz : (k : G) * z = z * (k : G) :=
    mem_centralizer_singleton_iff.mp k.property
  refine ⟨(k : G) * g, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · apply mul_inv_eq_iff_eq_mul.mp
    simpa only [mul_inv_rev, mul_assoc] using hkt
  · calc
      ((k : G) * g) * x * ((k : G) * g)⁻¹ =
          (k : G) * (g * x * g⁻¹) * (k : G)⁻¹ := by group
      _ = (k : G) * z * (k : G)⁻¹ := by rw [hg]
      _ = z := by rw [hkz, mul_inv_cancel_right]

end CFSG.Quasithin.HigmanSims
