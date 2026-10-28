module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.Embedding
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PrimeChoice
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure

/-!
# The canonical radical in actual local overgroups

For the original nonquasisimple faithful local component L, the proved
radical structure constructs the literal input to intrinsic 1.3.4. The
ambient QTKE hypothesis supplies SQTK for KT, and the actual quaternion
section in the T-automizer excludes the symplectic branch. Thus Ξₚ(L) is
normal in every nonquasisimple local overgroup K. Conversely, its normality
forces that original quotient K/O₂(K) to be nonquasisimple.

The final theorem chooses the prime and a maximal faithful local overgroup.
It leaves precisely the quasisimple linear-three alternative; excluding it
requires the genuine earlier classification 13.1.2(3), coming from 12.2.2.
This module does not assert that classification or full Lemma 13.1.4.
The universal A.3.6, A.3.8 and A.4.10 inputs retain their original owners.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Lemma 13.1.4 and the opening choice for Theorem 13.1.7, pp.867--868.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.Adequate
open CFSG.Quasithin.Chapter1.XiEmbedding
namespace CFSG.Quasithin.Chapter13.Section01.RadicalNormality
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem source_local_sqtk
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) :
    IsSQTK KnownSimple.IsKnownSimple H := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R, hH, isPGroup_pCoreIn 2 H, rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Sylow 2 G} {L₀ K : Subgroup G}
    (hL : L₀ ∈ nonquasisimpleFaithful T) (hK : K ∈ L G T) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))

include hG hA36 hA38 hL hK hLK ho hd

/-- Apply the complete intrinsic embedding theorem to the canonical Ξₚ(L)
and every actual local overgroup, without an embedding or model premise. -/
theorem source_normal_or_linear_three :
    ((XiP p L₀).subgroupOf K).Normal ∨
      IsQuasisimple (XiQuotient K) ∧ LinearThreeModel p (XiQuotient K) ∧
      p ^ 2 ∣ Nat.card (XiQuotient K) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have hQ : ∀ D ∈ L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple
        ((D ⊔ T : Subgroup G) ⧸ pCore 2 (D ⊔ T : Subgroup G)) := by
    intro D hD
    exact uniqueness_local_quotient_sqtk hG hD.2.2
  have hTL := radicalLocal_invariant_of_A38 hA38 hl (hQ L₀ hl) hL.2
  have hTK := local_chain_normalizes hl hK hLK hTL
  have hXi : XiP p L₀ ∈ Xi G T := lemma_1_3_3 hA36 hA38 hQ
    ⟨L₀, hl, hL.2, p, Fact.out, ho, hd, rfl⟩
  obtain ⟨hp3, hodd⟩ := XiP_oddQuotient_of_A36 hA36 hl (hQ L₀ hl) hL.2 ho hd
  let P : Sylow p (XiP p L₀) := default
  have hXK : XiP p L₀ ≤ K := (XiP_le p L₀).trans hLK
  have hinput := localInput_of_mem_Xi hXi hK.2.1 (sup_le_sup_right hXK T) ho hodd P
  exact normal_or_linear_three hK hTK hXK hinput (source_local_sqtk hG hK.2.2) hp3
    (RadicalActions.XiP_automizer_not_isCyclic_of_A36 hA36 hl (hQ L₀ hl) hL.2 ho hd P)

/-- The original radical is normal in each nonquasisimple local overgroup. -/
theorem source_normal_of_not_quasisimple (hn : ¬ IsQuasisimple (XiQuotient K)) :
    ((XiP p L₀).subgroupOf K).Normal := by
  rcases source_normal_or_linear_three hG hA36 hA38 hL hK hLK ho hd with h | h
  · exact h
  · exact (hn h.1).elim

/-- For these actual overgroups, nonnormality is exactly the quasisimple
quotient branch. This uses the same Ξₚ(L) and each K's own two-core. -/
theorem source_normal_iff_not_quasisimple :
    ((XiP p L₀).subgroupOf K).Normal ↔ ¬ IsQuasisimple (XiQuotient K) := by
  exact ⟨source_overgroup_not_quasisimple hG hA36 hL hK hLK ho hd,
    source_normal_of_not_quasisimple hG hA36 hA38 hL hK hLK ho hd⟩


omit hK hLK ho hd in
/-- The original maximal faithful overgroup and its canonical radical are
selected internally. Intrinsic embedding leaves only the explicitly named
linear-three branch, whose source exclusion is 13.1.2(3). -/
theorem exists_maximal_source_alternative (hA410 : A410EarlierResult G) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ K ∈ MainForward.faithfulLocalComponents T ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        ((((XiP p L₀).subgroupOf K).Normal ∧ ¬ IsQuasisimple (XiQuotient K)) ∨
          (IsQuasisimple (XiQuotient K) ∧ LinearThreeModel p (XiQuotient K) ∧
            p ^ 2 ∣ Nat.card (XiQuotient K))) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  obtain ⟨K, hK, hLK⟩ := exists_mem_LStar_ge hl
  have hTL := radicalLocal_invariant_of_A38 hA38 hl
    (uniqueness_local_quotient_sqtk hG hl.2.2) hL.2
  have hTK := local_chain_normalizes hl hK.1 hLK hTL
  have he : (T : Subgroup G) ⊓ normalizer (L₀ : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [inf_eq_left.mpr hTL, inf_eq_left.mpr hTK]
  have hf := (faithful_chain_of_A410_of_normalizer_eq T (hG.evenCharacteristic T)
    hA410 hL.1 hK.1 hLK he).2
  obtain ⟨p, hp, ho, hp3, hd, _, hne⟩ := exists_odd_radical_source hG hA36 hL
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨K, hK, hLK, hf, hTK, p, hp, ho, hp3, hd, hne, ?_⟩
  rcases source_normal_or_linear_three hG hA36 hA38 hL hK.1 hLK ho hd with hn | hq
  · exact Or.inl ⟨hn, source_overgroup_not_quasisimple hG hA36 hL hK.1 hLK ho hd hn⟩
  · exact Or.inr hq

end CFSG.Quasithin.Chapter13.Section01.RadicalNormality
