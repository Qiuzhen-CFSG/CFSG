module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.CommutingPairFusion
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupAction.CoprimeIndexTwoInvolution

/-!
# The two transfer endpoints of the nonabelian rank-two branch

The original simple-QTKE hypothesis excludes normal subgroups of index two
and makes the ambient group perfect. The first endpoint applies Thompson
transfer to the literal R join U after 14.3.21 and Q=U. The second uses fusion
of commuting pairs to apply generalized transfer in C(z), as in 14.3.22.

These are consumers of the local involution and centralizer geometry.
They do not assert that the original local setup has already supplied that
geometry or the preceding orthogonal recognition.

Source: Aschbacher--Smith, Lemmas 14.3.21--22 and the proof of Theorem 14.3.16,
printed pp.998--999.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}

private theorem no_index_two (hG : IsSimpleQTKE K G)
    (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  let := hG.simple
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h, index_bot]
    intro hc
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hG.nonabelian inferInstance
  · simp [h]

/-- The final transfer contradiction of 14.3.16 on the literal subgroup R join U.
The local conclusions of 14.3.21 and Q=U from 14.3.22 remain explicit. -/
public theorem false_of_ru_fusion (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (R U : Subgroup G) (z : G)
    (hi : ((R ⊔ U).subgroupOf (T : Subgroup G)).index = 2)
    (hex : ∃ t ∈ (T : Subgroup G), orderOf t = 2 ∧ t ∉ R ⊔ U)
    (hout : ∀ t ∈ (T : Subgroup G), orderOf t = 2 → t ∉ R ⊔ U → ¬ IsConj z t)
    (hin : ∀ x ∈ R ⊔ U, orderOf x = 2 → IsConj z x) : False := by
  obtain ⟨t, ht, ho, htRU⟩ := hex
  obtain ⟨x, hx, hxRU⟩ := T.exists_isConj_mem_of_index_two (no_index_two hG)
    ((R ⊔ U).subgroupOf (T : Subgroup G)) hi ⟨t, ht⟩
    (by rw [← Subgroup.orderOf_coe]; exact ho)
  have hxo : orderOf (x : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    rw [← hg]
    exact (MulAut.conj g).orderOf_eq t |>.trans ho
  exact hout t ht ho htRU ((hin x hxRU hxo).trans hx.symm)

/-- The transfer contradiction in 14.3.22 from fusion in the opposite centralizer.
The quotient is the actual abelian quotient of C(z), with no whole-centralizer split. -/
public theorem false_of_centralizer_fusion (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (z w : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hwz : w ∈ centralizer ({z} : Set G))
    (N : Subgroup (centralizer ({z} : Set G))) [N.Normal]
    [IsMulCommutative ((centralizer ({z} : Set G)) ⧸ N)]
    (hw : orderOf w = 2) (hnot : (⟨w, hwz⟩ : centralizer ({z} : Set G)) ∉ N)
    (hf : ∀ a ∈ centralizer ({w} : Set G), IsConj z a →
      ∃ c ∈ centralizer ({w} : Set G), c * z * c⁻¹ = a) : False := by
  let := hG.simple
  have hp : _root_.commutator G = ⊤ :=
    (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hG.nonabelian ((commutator_eq_bot_iff G).mp h))
  have hi : Nat.Coprime 2 (centralizer ({z} : Set G)).index :=
    Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h => T.not_dvd_index (h.trans (index_dvd_of_le hT)))
  exact not_mem_commutator_of_opposite_centralizer_fusion z w hwz N hi hw hnot hf
    (hp ▸ mem_top w)

/-- Apply the cubic fixed-point argument of 14.3.21(1) directly to the final
transfer. Only the local subgroup identities and the two fusion clauses remain. -/
public theorem false_of_ru_fusion_of_cubic_fixed_kernel (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (R U P X : Subgroup G) (z : G)
    (hP : IsPGroup 2 P) (hX : IsPGroup 3 X)
    (hPT : P ≤ (T : Subgroup G)) (hcut : P ⊓ (R ⊔ U) ≤ R)
    (hXP : X ≤ normalizer (P : Set G))
    (hXR : X ≤ normalizer (R : Set G)) [(R.subgroupOf P).Normal]
    (hiP : (R.subgroupOf P).index = 2)
    (hfixed : R ⊓ centralizer (X : Set G) = ⊥)
    (hi : ((R ⊔ U).subgroupOf (T : Subgroup G)).index = 2)
    (hout : ∀ t ∈ (T : Subgroup G), orderOf t = 2 → t ∉ R ⊔ U → ¬ IsConj z t)
    (hin : ∀ x ∈ R ⊔ U, orderOf x = 2 → IsConj z x) : False := by
  obtain ⟨t, ht, ho, htRU, _⟩ := exists_involution_outside_join_of_coprime_fixed_kernel
    T R U P X hP hX hPT hcut hXP hXR hiP hfixed
  exact false_of_ru_fusion hG T R U z hi ⟨t, ht, ho, htRU⟩ hout hin
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource
