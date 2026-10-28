module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.CentralizerGeneratorIndexTwo
public import Theory.GroupTheory.RelativeQuotientMaps

/-!
# Centralizer steps in the case-one argument of Lemma 13.8.33

The source subgroups `UH`, `UL` and `HC` retain their definitions from
`SourceDefs`. Write `CQUL = C_Q(UL)`. Centralization of the larger span
places `CQUL` inside `HC`; if `UL` is abelian and contained in `Q`, it
lies in `CQUL`. We prove the relative normality required for the maps
`CQUL/UH → HC/UH` and `CQUL/UH → CQUL/UL` supplied by
`RelativeQuotientMaps`. We do not require `UL` to be normal in `HC`.

The quadratic-pair deduction also keeps the local normalization inputs
explicit. Finally five conjugates of an element with centralizer index
two, together with the centralized subgroup `V`, give `[Q : CQUL] ≤ 32`.
The conjugates are by elements normalizing `Q`, so their indices really
are equal. Their index-two centralizers also construct relative normality
and the elementary abelian structure on the actual quotient `Q/CQUL`.

Abelianness of `UL`, the five conjugate generators and the representation
identifications remain to be proved in the source argument. These lemmas
neither assume a final chief-factor count nor assert Lemma 13.8.33.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.967–968, proof of 13.8.33.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
variable {G : Type*} [Group G]

/-- The actual centralizer in the source two-core `Q`. -/
def CQUL (Q L H V₃ : Subgroup G) : Subgroup G :=
  Q ⊓ centralizer (Source.UL L H V₃ : Set G)

theorem centralizer_le_HC (Q L H V₃ : Subgroup G) (hQH : Q ≤ H) :
    CQUL Q L H V₃ ≤ Source.HC H V₃ := by
  exact le_inf (inf_le_left.trans hQH)
    (inf_le_right.trans (centralizer_le (le_conjugateSpanBy (Source.UH H V₃) L)))

theorem abelian_UL_le_centralizer (Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)] (hULQ : Source.UL L H V₃ ≤ Q) :
    Source.UL L H V₃ ≤ CQUL Q L H V₃ :=
  le_inf hULQ (le_centralizer _)

theorem abelian_UL_le_HC (Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H) :
    Source.UL L H V₃ ≤ Source.HC H V₃ :=
  (abelian_UL_le_centralizer Q L H V₃ hULQ).trans (centralizer_le_HC Q L H V₃ hQH)

/-- Once abelianness and the local normalization are available, the two
subgroups act quadratically on each other. -/
theorem abelian_UL_quadratic_pair (L H V₃ A₁ Uγ Gγ M : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)] [IsMulCommutative Uγ]
    (hA₁ : A₁ ≤ Source.UH H V₃) (hGγ : Gγ = centralizer (A₁ : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G))
    (hUγM : Uγ ≤ M) (hMUL : M ≤ normalizer (Source.UL L H V₃ : Set G)) :
    Source.UL L H V₃ ≤ Gγ ∧
      ⁅Source.UL L H V₃, Uγ⁆ ≤ Source.UL L H V₃ ⊓ Uγ ∧
      ⁅⁅Source.UL L H V₃, Uγ⁆, Uγ⁆ = ⊥ ∧
      ⁅⁅Source.UL L H V₃, Uγ⁆, Source.UL L H V₃⁆ = ⊥ := by
  have hULGγ : Source.UL L H V₃ ≤ Gγ := by
    rw [hGγ]
    exact (le_centralizer _).trans
      (centralizer_le (hA₁.trans (le_conjugateSpanBy (Source.UH H V₃) L)))
  have hcomm : ⁅Source.UL L H V₃, Uγ⁆ ≤ Source.UL L H V₃ ⊓ Uγ :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hUγM.trans hMUL))
      (le_normalizer_iff_commutator_le_right.mp (hULGγ.trans hGγUγ))
  exact ⟨hULGγ, hcomm,
    commutator_eq_bot_iff_le_centralizer.mpr ((hcomm.trans inf_le_right).trans
      (le_centralizer _)),
    commutator_eq_bot_iff_le_centralizer.mpr ((hcomm.trans inf_le_left).trans
      (le_centralizer _))⟩

theorem UH_normal_in_HC (H V₃ : Subgroup G)
    [IsMulCommutative (Source.UH H V₃)] (hUH : Source.UH H V₃ ≤ H) :
    ((Source.UH H V₃).subgroupOf (Source.HC H V₃)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (le_inf hUH (le_centralizer _))).mpr
  exact inf_le_right.trans (centralizer_le_normalizer _)

theorem UL_normal_in_CQUL (Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)] (hULQ : Source.UL L H V₃ ≤ Q) :
    ((Source.UL L H V₃).subgroupOf (CQUL Q L H V₃)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (abelian_UL_le_centralizer Q L H V₃ hULQ)).mpr
  exact inf_le_right.trans (centralizer_le_normalizer _)

theorem UH_normal_in_CQUL (Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)] (hULQ : Source.UL L H V₃ ≤ Q) :
    ((Source.UH H V₃).subgroupOf (CQUL Q L H V₃)).Normal := by
  have hUHUL : Source.UH H V₃ ≤ Source.UL L H V₃ := le_conjugateSpanBy _ _
  apply (normal_subgroupOf_iff_le_normalizer
    (hUHUL.trans (abelian_UL_le_centralizer Q L H V₃ hULQ))).mpr
  exact (inf_le_right.trans (centralizer_le hUHUL)).trans (centralizer_le_normalizer _)

/-- The five-conjugate centralizer bound at the page break on pp.967–968.
Generation and the single-element index are explicit inputs. -/
theorem centralizer_index_le_thirtyTwo (V Q L H V₃ : Subgroup G)
    (u₁ : G) (g : Fin 5 → G)
    (hgen : Source.UL L H V₃ = V ⊔ closure (Set.range fun i => MulAut.conj (g i) u₁))
    (hQV : Q ≤ centralizer (V : Set G))
    (hLQ : L ≤ normalizer (Q : Set G)) (hg : ∀ i, g i ∈ L)
    (hindex : (centralizer ({u₁} : Set G)).relIndex Q = 2) :
    (CQUL Q L H V₃).relIndex Q ≤ 32 := by
  have h := centralizer_relIndex_le_of_conjugate_generators
    V Q (Source.UL L H V₃) u₁ g 2 hgen hQV (fun i => hLQ (hg i)) hindex.le
  simpa only [CQUL, Fintype.card_fin, show 2 ^ 5 = 32 from rfl] using h

/-- The same generators construct the actual elementary quotient used for
the subsequent module recognition. Its normality is proved here. -/
theorem centralizer_quotient_elementary_and_card [Finite G] (V Q L H V₃ : Subgroup G)
    (u₁ : G) (g : Fin 5 → G)
    (hgen : Source.UL L H V₃ = V ⊔ closure (Set.range fun i => MulAut.conj (g i) u₁))
    (hQV : Q ≤ centralizer (V : Set G))
    (hLQ : L ≤ normalizer (Q : Set G)) (hg : ∀ i, g i ∈ L)
    (hindex : (centralizer ({u₁} : Set G)).relIndex Q = 2) :
    ∃ hN : ((CQUL Q L H V₃).subgroupOf Q).Normal,
      letI := hN
      IsElementaryAbelian 2 (Q ⧸ (CQUL Q L H V₃).subgroupOf Q) ∧
        Nat.card (Q ⧸ (CQUL Q L H V₃).subgroupOf Q) ≤ 32 := by
  have hi (i : Fin 5) : (centralizer ({MulAut.conj (g i) u₁} : Set G)).relIndex Q = 2 := by
    rw [centralizer_relIndex_equiv Q (MulAut.conj (g i)) u₁
      (mem_normalizer_iff_map_conj_eq.mp (hLQ (hg i)))]
    exact hindex
  let hN : ((CQUL Q L H V₃).subgroupOf Q).Normal :=
    centralizer_normal_of_generated_index_two V Q (Source.UL L H V₃) _ hgen hQV hi
  let : ((Q ⊓ centralizer (Source.UL L H V₃ : Set G)).subgroupOf Q).Normal := hN
  refine ⟨hN, elementary_centralizer_quotient_of_generated_index_two
    V Q (Source.UL L H V₃) _ hgen hQV hi, ?_⟩
  exact centralizer_index_le_thirtyTwo V Q L H V₃ u₁ g hgen hQV hLQ hg hindex


end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
