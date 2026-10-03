module

public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A supplement for the normal closure of a Baumann subgroup

Let B be the elementary Baumann subgroup of a Sylow 2-subgroup S. If normal
subgroups E and N satisfy N ≤ S, E ≤ the normal closure of B, and B ≤ E ∨ N,
then that normal closure is E ∨ B. This is the Frattini transfer behind
L = EB in the proof of Stellmacher (2.3), Journal of Algebra 190 (1997), p.20.

Put D = E ∨ N. The Sylow intersection R = S ∩ D contains B, so Baumann
heredity identifies B with B(R). Its normalizer therefore normalizes B.
Both D and the normalizer of R normalize E ∨ B: E is normal, and N lies
in S, which normalizes B. Frattini for the normal subgroup D now makes
E ∨ B normal in G, proving the equality by the two given containments.
No solvability or characteristic-two hypothesis is required.
-/

namespace Stellmacher

/-- A normal subgroup supplementing the Baumann subgroup modulo a normal
subgroup of S also supplements its full normal closure. -/
public theorem normalClosure_baumann_eq_sup
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (B E N : Subgroup G) [E.Normal] [N.Normal]
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hNS : N ≤ (S : Subgroup G))
    (hEL : E ≤ Subgroup.normalClosure (B : Set G)) (hBEN : B ≤ E ⊔ N) :
    Subgroup.normalClosure (B : Set G) = E ⊔ B := by
  let D := E ⊔ N
  let K := E ⊔ B
  have hBS : B ≤ (S : Subgroup G) := hB ▸ inf_le_left
  have hSNB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := by
    rw [hB]
    exact S.toSubgroup.le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hDNK : D ≤ Subgroup.normalizer (K : Set G) := by
    apply sup_le
    · exact (show E ≤ K from le_sup_left).trans K.le_normalizer
    · have hNE : N ≤ Subgroup.normalizer (E : Set G) := by
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      exact (le_inf hNE (hNS.trans hSNB)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup E B)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let R := (T : Subgroup D).map D.subtype
  have hR : R = (S : Subgroup G) ⊓ D := by
    rw [show R = (T : Subgroup D).map D.subtype from rfl,
      hT, Subgroup.subgroupOf_map_subtype]
  have hRS : R ≤ (S : Subgroup G) := hR ▸ inf_le_left
  have hBR : B ≤ R := by
    rw [hR]
    exact le_inf hBS hBEN
  have hRB : R ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set G) = B := by
    rw [hB] at hBR ⊢
    exact baumann_eq_of_intermediate (S : Subgroup G) R hBR hRS
  have hNRB : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    rw [← hRB]
    exact normalizer_le_normalizer_baumann R
  have hNRK : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have hNRE : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.normalizer_eq_top E]
      exact le_top
    exact (le_inf hNRE hNRB).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup E B)
  have hgen : Subgroup.normalizer (R : Set G) ⊔ D = ⊤ :=
    T.normalizer_sup_eq_top
  have hKn : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hNRK hDNK
  let : K.Normal := hKn
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (show B ≤ K from le_sup_right)
  · exact sup_le hEL Subgroup.le_normalClosure

end Stellmacher
