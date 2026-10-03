module
public import Theory.GroupTheory.ElementaryCommutingTwoGroup
public import Theory.ElementaryAbelian.Join

/-!
# Binary centralizer transport when the centralizer has rank at least two

Let Q lie in a finite two-subgroup S, and suppose Q C_S(Q) contains an
elementary subgroup B of order at least eight. If Q and C_G(Q) both contain
elementary four-groups, C_G(Q) preserves the commuting component of B.

Choose a Sylow two-subgroup T of C_G(Q) containing C_S(Q), and place a
four-group F in T. For an elementary subgroup E of Q of order at least
four, E F is elementary. If its order is at least eight, connectivity
inside Q T joins B to E F and then to E. Otherwise E = F, and E centralizes
Q T, giving the same conclusion directly. Every element of C_G(Q) fixes E.

This is the non-rank-one centralizer case of the binary fusion step in
GLS2, Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`). It needs neither
simplicity nor solvability; the rank-one centralizer case remains separate.
-/

namespace Subgroup
open scoped Pointwise

private theorem sylow_contains_elementary_four
    {H : Type*} [Group H] [Finite H] (T : Sylow 2 H)
    (F : Subgroup H) [IsElementaryAbelian 2 F] (hF : 4 ≤ Nat.card F) :
    ∃ D : Subgroup T, IsElementaryAbelian 2 D ∧ 4 ≤ Nat.card D := by
  obtain ⟨P, hFP⟩ := (IsElementaryAbelian.isPGroup 2 F).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P T
  let f := (MulAut.conj g).toMonoidHom
  let K := F.map f
  have hKT : K ≤ (T : Subgroup H) := by
    rintro x ⟨a, ha, rfl⟩
    rw [← hg]
    change (MulAut.conj g) • a ∈ (MulAut.conj g) • (P : Set H)
    exact Set.smul_mem_smul_set (hFP ha)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map f
  refine ⟨K.subgroupOf (T : Subgroup H), IsElementaryAbelian.subgroupOf hKT, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hKT).toEquiv,
    card_map_of_injective (MulAut.conj g).injective]
  exact hF

private theorem connected_to_central_factor
    {G : Type*} [Group G] [Finite G]
    (Q T B E F : Subgroup G) (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hB : 8 ≤ Nat.card B) (hE : 4 ≤ Nat.card E) (hF : 4 ≤ Nat.card F)
    (hBT : B ≤ Q ⊔ T) (hEQ : E ≤ Q) (hFT : F ≤ T)
    (hTC : T ≤ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 B E := by
  have hFC : F ≤ centralizer (E : Set G) :=
    hFT.trans (hTC.trans (centralizer_le hEQ))
  let : IsElementaryAbelian 2 (E ⊔ F : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hFC
  have hR : IsPGroup 2 (Q ⊔ T : Subgroup G) :=
    hQ.to_sup_of_normal_left' hT (hTC.trans (centralizer_le_normalizer _))
  by_cases hlarge : 8 ≤ Nat.card (E ⊔ F : Subgroup G)
  · have hBJ := elementaryCommutingConnected_of_le_twoGroup (Q ⊔ T) B (E ⊔ F)
      hR hB hlarge hBT (sup_le (hEQ.trans le_sup_left) (hFT.trans le_sup_right))
    exact hBJ.trans (ElementaryCommutingAdjacent.connected
      ⟨inferInstance, by omega, inferInstance, by omega,
        (E ⊔ F).le_centralizer.trans (centralizer_le (show E ≤ E ⊔ F from le_sup_left))⟩)
  · obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (E ⊔ F : Subgroup G)).exists_card_eq
    have hnle : n ≤ 2 := by
      by_contra! hnlt
      have hh : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hnlt
      omega
    have hsmall : Nat.card (E ⊔ F : Subgroup G) ≤ 4 := by
      rw [hn]
      exact Nat.pow_le_pow_right (by decide) hnle
    have hEJ : E = E ⊔ F := eq_of_le_of_card_ge le_sup_left (hsmall.trans hE)
    have hFJ : F = E ⊔ F := eq_of_le_of_card_ge le_sup_right (hsmall.trans hF)
    have hEF : E = F := hEJ.trans hFJ.symm
    have hEC : E ≤ centralizer (Q : Set G) := hEF ▸ hFT.trans hTC
    have hRC : Q ⊔ T ≤ centralizer (E : Set G) :=
      sup_le (le_centralizer_iff.mp hEC) (hTC.trans (centralizer_le hEQ))
    exact ElementaryCommutingAdjacent.connected
      ⟨inferInstance, by omega, inferInstance, by omega, hBT.trans hRC⟩

/-- A four-group in the full centralizer puts each elementary subgroup of
Q of rank at least two in the principal commuting component of S. -/
public theorem elementaryCommutingConnected_of_centralizer_rank_two
    {G : Type*} [Group G] [Finite G]
    (S A Q E B F : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 F]
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBQ : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hFC : F ≤ centralizer (Q : Set G))
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E)
    (hB : 8 ≤ Nat.card B) (hF : 4 ≤ Nat.card F) :
    ElementaryCommutingConnected 2 A E := by
  let C := centralizer (Q : Set G)
  let D := S ⊓ C
  have hDC : D ≤ C := inf_le_right
  have hD : IsPGroup 2 D := hS.to_le inf_le_left
  obtain ⟨T, hDT⟩ := (hD.of_equiv (subgroupOfEquivOfLe hDC).symm).exists_le_sylow
  let TG : Subgroup G := (T : Subgroup C).map C.subtype
  have hDTG : D ≤ TG := by
    simpa only [map_subgroupOf_eq_of_le hDC] using map_mono (f := C.subtype) hDT
  let : IsElementaryAbelian 2 (F.subgroupOf C) := IsElementaryAbelian.subgroupOf hFC
  have hFcard : 4 ≤ Nat.card (F.subgroupOf C) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv]
  obtain ⟨K, hKe, hK⟩ := sylow_contains_elementary_four T (F.subgroupOf C) hFcard
  let : IsElementaryAbelian 2 K := hKe
  let f : T →* G := C.subtype.comp (T : Subgroup C).subtype
  have hf : Function.Injective f := C.subtype_injective.comp (T : Subgroup C).subtype_injective
  let KG := K.map f
  let : IsElementaryAbelian 2 KG := IsElementaryAbelian.map f
  have hKT : KG ≤ TG := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_map.mpr ⟨k.val, k.property, rfl⟩
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB
    hAS (hBQ.trans (sup_le hQS inf_le_left))
  apply hAB.trans
  exact connected_to_central_factor Q TG B E KG (hS.to_le hQS)
    (T.isPGroup'.map C.subtype) hB hE
    (by simpa only [KG, card_map_of_injective hf] using hK)
    (hBQ.trans (sup_le_sup_left hDTG Q)) hEQ hKT (map_subtype_le _)

/-- Centralizer transport under the weak-core hypotheses, provided the full
centralizer contains an elementary subgroup of order at least four. -/
public theorem elementaryCommutingConnected_conj_of_centralizer_rank_two
    {G : Type*} [Group G] [Finite G]
    (S A Q E B F : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 F]
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBQ : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hFC : F ≤ centralizer (Q : Set G))
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E)
    (hB : 8 ≤ Nat.card B) (hF : 4 ≤ Nat.card F)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  have hAE := elementaryCommutingConnected_of_centralizer_rank_two
    S A Q E B F hS hAS hQS hEQ hBQ hFC hA hE hB hF
  have hfix : E.map (MulAut.conj c).toMonoidHom = E := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      have hce := hc e (hEQ he)
      simpa [MulAut.conj_apply, ← hce] using he
    · intro e he
      refine mem_map.mpr ⟨e, he, ?_⟩
      have hce := hc e (hEQ he)
      simp [MulAut.conj_apply, ← hce]
  exact hAE.trans (hfix ▸ hAE.symm.map (MulAut.conj c))

end Subgroup
