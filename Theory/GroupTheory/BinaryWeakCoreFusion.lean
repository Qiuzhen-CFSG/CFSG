module
public import Theory.GroupTheory.ElementaryCommutingTwoGroup
public import Theory.GroupTheory.ElementaryCommutingStabilizer

/-!
# Frattini reduction for binary weak-core fusion

Let A and B be rank-three elementary subgroups of a finite two-subgroup S.
If B lies in Q C_G(Q), the normalizer of Q stabilizes the commuting component
of A as soon as its centralizer does. Choose a Sylow subgroup R of Q C_G(Q)
containing B. The common rank-three vertex B connects the rank-three
components of S and R, so N_G(R) stabilizes this component. Frattini's
argument in N_G(Q) completes the reduction.

This is the prime-independent normalizer reduction in GLS2, Proposition
22.4(i), `refs/KGroup/GLS2/ChapterF.tex`. The binary centralizer transport
required by the following remark is a separate fusion obligation; ambient
extension of four-groups alone does not assert that transport.
-/

namespace Subgroup

/-- Frattini reduction in the normalizer of Q. The subgroup B specifies
which two-subgroups' normalizers must be controlled. -/
public theorem normalizer_le_of_centralizer_and_twoGroup_normalizers
    {G : Type*} [Group G] [Finite G] (Q B M : Subgroup G)
    (hB : IsPGroup 2 B) (hBD : B ≤ Q ⊔ centralizer (Q : Set G))
    (hQM : Q ≤ M) (hCM : centralizer (Q : Set G) ≤ M)
    (hRM : ∀ R : Subgroup G, IsPGroup 2 R → B ≤ R →
      normalizer (R : Set G) ≤ M) : normalizer (Q : Set G) ≤ M := by
  let N := normalizer (Q : Set G)
  let D := Q ⊔ centralizer (Q : Set G)
  let K := D.subgroupOf N
  have hDN : D ≤ N := sup_le le_normalizer (centralizer_le_normalizer _)
  have hBN : B ≤ N := hBD.trans hDN
  have hBK : B.subgroupOf N ≤ K := fun _ hx => hBD hx
  have hKsup : K = Q.subgroupOf N ⊔ (centralizer (Q : Set G)).subgroupOf N :=
    subgroupOf_sup le_normalizer (centralizer_le_normalizer _)
  let : K.Normal := by
    rw [hKsup]
    infer_instance
  have hBKN : IsPGroup 2 (B.subgroupOf N) :=
    hB.of_injective (subgroupOfEquivOfLe hBN).toMonoidHom
      (subgroupOfEquivOfLe hBN).injective
  have hBKK : IsPGroup 2 ((B.subgroupOf N).subgroupOf K) :=
    hBKN.of_injective (subgroupOfEquivOfLe hBK).toMonoidHom
      (subgroupOfEquivOfLe hBK).injective
  obtain ⟨T, hBT⟩ := hBKK.exists_le_sylow
  let RN : Subgroup N := (T : Subgroup K).map K.subtype
  let R : Subgroup G := RN.map N.subtype
  have hR : IsPGroup 2 R := (T.isPGroup'.map K.subtype).map N.subtype
  have hBR : B ≤ R := by
    intro b hb
    let bN : N := ⟨b, hBN hb⟩
    let bK : K := ⟨bN, hBD hb⟩
    exact mem_map.mpr ⟨bN, mem_map.mpr ⟨bK, hBT hb, rfl⟩, rfl⟩
  have hNR : normalizer (RN : Set N) ≤ M.subgroupOf N := by
    intro n hn
    apply hRM R hR hBR
    exact RN.le_normalizer_map N.subtype (mem_map.mpr ⟨n, hn, rfl⟩)
  have hKM : K ≤ M.subgroupOf N := fun _ hk => (sup_le hQM hCM) hk
  have htop : (⊤ : Subgroup N) ≤ M.subgroupOf N := by
    rw [← T.normalizer_sup_eq_top]
    exact sup_le hNR hKM
  intro n hn
  exact htop (show (⟨n, hn⟩ : N) ∈ (⊤ : Subgroup N) from mem_top _)

/-- Two rank-three vertices in a common two-subgroup have the same component;
thus a second two-subgroup containing one of them has controlled normalizer. -/
public theorem normalizer_le_componentStabilizer_of_common_rank_three
    {G : Type*} [Group G] [Finite G] (S R A B : Subgroup G)
    (hS : IsPGroup 2 S) (hR : IsPGroup 2 R)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hBS : B ≤ S) (hBR : B ≤ R) :
    normalizer (R : Set G) ≤
      elementaryCommutingComponentStabilizer 2 A inferInstance (by omega) := by
  intro g hg
  let e := MulAut.conj g
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hBgR : B.map e.toMonoidHom ≤ R :=
    (map_mono hBR).trans (mem_normalizer_iff_map_conj_eq.mp hg).le
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  have hBBg := elementaryCommutingConnected_of_le_twoGroup R B (B.map e.toMonoidHom)
    hR hB (by simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hB) hBR hBgR
  exact hAB.trans (hBBg.trans (hAB.symm.map e))

/-- The binary normalizer transport reduces to centralizer transport. This
reduction requires neither simplicity nor a rank assumption on Q. -/
public theorem elementaryCommutingConnected_conj_of_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hBS : B ≤ S)
    (hBD : B ≤ Q ⊔ centralizer (Q : Set G))
    (hC : ∀ c ∈ centralizer (Q : Set G),
      ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom))
    (g : G) (hg : g ∈ normalizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj g).toMonoidHom) := by
  let M := elementaryCommutingComponentStabilizer 2 A inferInstance (show 2 ^ 2 ≤ Nat.card A by omega)
  have hRM (R : Subgroup G) (hR : IsPGroup 2 R) (hBR : B ≤ R) :
      normalizer (R : Set G) ≤ M :=
    normalizer_le_componentStabilizer_of_common_rank_three S R A B
      hS hR hA hB hAS hBS hBR
  have hSM : S ≤ M := le_normalizer.trans (hRM S hS hBS)
  exact normalizer_le_of_centralizer_and_twoGroup_normalizers Q B M
    (IsElementaryAbelian.isPGroup 2 B) hBD (hQS.trans hSM) hC hRM hg

/-- The weak-core transport holds whenever Q has a normal four-group.
The four-group may have rank two even when Q has no rank-three subgroup. -/
public theorem elementaryCommutingConnected_conj_of_weak_rank_of_normal_four
    {G : Type*} [Group G] [Finite G] (S A Q B E : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hQE : Q ≤ normalizer (E : Set G))
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (g : G) (hg : g ∈ normalizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj g).toMonoidHom) := by
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hBD : B ≤ Q ⊔ centralizer (Q : Set G) :=
    hBweak.trans (sup_le_sup_left inf_le_right Q)
  have hCE : centralizer (Q : Set G) ≤ normalizer (E : Set G) :=
    (centralizer_le hEQ).trans (centralizer_le_normalizer _)
  have hBE : B ≤ normalizer (E : Set G) := hBD.trans (sup_le hQE hCE)
  have hAE := (elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS).trans
    (elementaryCommutingConnected_of_normalizes_four B E hB hE hBE)
  apply elementaryCommutingConnected_conj_of_centralizer_transport S A Q B hS hA hB
    hAS hQS hBS hBD ?_ g hg
  intro c hc
  exact normalizer_le_elementaryCommutingComponentStabilizer A E inferInstance
    (by omega) hAE (hCE hc)

end Subgroup
