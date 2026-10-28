module

public import Theory.GroupTheory.ElementaryCommutingCoprime

/-!
# Odd prime-power reduction for binary centralizer transport

Suppose the two-group `S` contains an elementary subgroup `A` of rank at
least three, and `Q C_S(Q)` contains another such subgroup `B`. A Sylow
two-subgroup of `C_G(Q)` containing `C_S(Q)` preserves the component of
`A`: its commuting product with `Q` is a two-group containing `B`.
Consequently it suffices to control elements of odd prime-power order in
the ambient centralizer. Indeed, a prime divisor of the index of the
component stabilizer in that centralizer contradicts containment of a
Sylow subgroup for that prime.

We also record control of any odd subgroup of the centralizer normalized
by `C_S(Q)`. It is normalized by `Q C_S(Q)`, hence by `B`, so coprime
fixed-point generation applies. These are reductions, not an assertion
that arbitrary odd subgroups have this normalization property.

The component arguments are those of GLS2, Section 22, Lemma 22.2 and
the centralizer reduction in Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). The odd prime-power fusion needed in
the isolated binary case is a separate obligation.
-/

namespace Subgroup

/-- The weak-rank condition controls a Sylow two-subgroup of the entire
centralizer, even when the given two-subgroup is not Sylow in the ambient
group. -/
public theorem exists_sylow_centralizer_le_elementaryCommutingStabilizer
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G))) :
    ∃ T : Sylow 2 (centralizer (Q : Set G)),
      (T : Subgroup (centralizer (Q : Set G))).map
        (centralizer (Q : Set G)).subtype ≤
          elementaryCommutingStabilizer 2 A (by omega) := by
  let C := centralizer (Q : Set G)
  let D := S ⊓ C
  have hD : IsPGroup 2 D := hS.to_le inf_le_left
  have hDC : D ≤ C := inf_le_right
  have hDCp : IsPGroup 2 (D.subgroupOf C) :=
    hD.of_injective (subgroupOfEquivOfLe hDC).toMonoidHom
      (subgroupOfEquivOfLe hDC).injective
  obtain ⟨T, hDT⟩ := hDCp.exists_le_sylow
  let U := (T : Subgroup C).map C.subtype
  have hUC : U ≤ C := map_subtype_le _
  have hDU : D ≤ U := by
    intro d hd
    exact mem_map.mpr ⟨⟨d, hDC hd⟩, hDT hd, rfl⟩
  let R := Q ⊔ U
  have hR : IsPGroup 2 R := (hS.to_le hQS).to_sup_of_normal_left'
    (T.isPGroup'.map C.subtype) (hUC.trans (centralizer_le_normalizer _))
  have hBR : B ≤ R := hBweak.trans (sup_le_sup_left hDU Q)
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  refine ⟨T, ?_⟩
  rw [elementaryCommutingStabilizer_eq_of_connected A B (by omega) (by omega) hAB]
  exact (le_sup_right : U ≤ R).trans
    (twoGroup_le_elementaryCommutingStabilizer R B hR hB hBR)

/-- To prove binary weak-rank centralizer transport, it suffices to prove
it for centralizer elements whose order is a power of an odd prime. -/
public theorem elementaryCommutingConnected_conj_of_odd_prime_power_centralizer
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hodd : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : G),
      c ∈ centralizer (Q : Set G) → (∃ n : ℕ, orderOf c = p ^ n) →
      ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom))
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let C := centralizer (Q : Set G)
  let M := elementaryCommutingStabilizer 2 A (show 2 ^ 2 ≤ Nat.card A by omega)
  let J := M.subgroupOf C
  obtain ⟨T, hTM⟩ := exists_sylow_centralizer_le_elementaryCommutingStabilizer
    S A Q B hS hA hB hAS hQS hBweak
  have hTJ : (T : Subgroup C) ≤ J := fun t ht => hTM (mem_map.mpr ⟨t, ht, rfl⟩)
  have hJ : J = ⊤ := by
    apply index_eq_one.mp
    by_contra hne
    obtain ⟨p, hp, hpJ⟩ := Nat.exists_prime_and_dvd hne
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      exact T.not_dvd_index (hpJ.trans (index_dvd_of_le hTJ))
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := C)
    have hPJ : (P : Subgroup C) ≤ J := by
      intro x hx
      apply hodd p hp hp2 x x.property
      obtain ⟨n, hn⟩ := P.isPGroup'.exists_orderOf_eq_pow (⟨x, hx⟩ : P)
      exact ⟨n, (orderOf_injective (C.subtype.comp (P : Subgroup C).subtype)
        (C.subtype_injective.comp Subtype.coe_injective) (⟨x, hx⟩ : P)).trans hn⟩
    exact P.not_dvd_index (hpJ.trans (index_dvd_of_le hPJ))
  exact (show (⟨c, hc⟩ : C) ∈ J from hJ ▸ mem_top _)

/-- An odd subgroup of the ambient centralizer is controlled whenever
the local centralizer normalizes it. -/
public theorem odd_centralizer_le_elementaryCommutingStabilizer_of_normalized
    {G : Type*} [Group G] [Finite G] (S A Q B N : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hN : Odd (Nat.card N)) (hNC : N ≤ centralizer (Q : Set G))
    (hDN : S ⊓ centralizer (Q : Set G) ≤ normalizer (N : Set G)) :
    N ≤ elementaryCommutingStabilizer 2 A (by omega) := by
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  rw [elementaryCommutingStabilizer_eq_of_connected A B (by omega) (by omega) hAB]
  apply odd_le_elementaryCommutingStabilizer_of_normalized B N hB hN
  exact hBweak.trans (sup_le
    ((le_centralizer_iff.mp hNC).trans (centralizer_le_normalizer _)) hDN)

/-- Centralizer transport holds if an odd subgroup normalized by the local
centralizer supplements that local centralizer in the ambient centralizer.
In particular this handles an odd normal complement to `C_S(Q)`. -/
public theorem elementaryCommutingConnected_conj_of_odd_centralizer_supplement
    {G : Type*} [Group G] [Finite G] (S A Q B N : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hN : Odd (Nat.card N)) (hNC : N ≤ centralizer (Q : Set G))
    (hDN : S ⊓ centralizer (Q : Set G) ≤ normalizer (N : Set G))
    (hsup : centralizer (Q : Set G) ≤ N ⊔ (S ⊓ centralizer (Q : Set G)))
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  have hNM := odd_centralizer_le_elementaryCommutingStabilizer_of_normalized
    S A Q B N hS hA hB hAS hQS hBweak hN hNC hDN
  have hDM : S ⊓ centralizer (Q : Set G) ≤
      elementaryCommutingStabilizer 2 A (by omega) :=
    inf_le_left.trans (twoGroup_le_elementaryCommutingStabilizer S A hS hA hAS)
  exact (hsup.trans (sup_le hNM hDM)) hc

end Subgroup
