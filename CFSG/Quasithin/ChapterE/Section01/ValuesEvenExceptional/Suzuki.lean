module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki.Extension
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Suzuki.ModelGeneration

/-!
# The Suzuki value in E.1.14(1)

The source concerns an SQTK-group `G = F*(G) T`, with simple `F*(G)`
isomorphic to `Sz(2^(2m+1))`, `m > 0`. Its generation parameter is `2m+1`.
The Suzuki calculation needs only these finite-group, simplicity, supplement
and actual-isomorphism hypotheses; no additional SQTK assumption is needed.

The proved odd outer order eliminates the two-extension, giving `F*(G) = G`
and hence an actual isomorphism from `G` to the Suzuki matrix group. The model
calculation then gives E-generation at rank `2m+1`, and an elementary family
whose weak-closure normalizer and E-members at rank `2m` lie in one proper
Borel. Even order and the attained-minimum specification determine the exact
parameter. The generation inputs are also exposed for the parent assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214 (PDF p.225), citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki

open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Even order of the ambient group follows from an actual embedded Suzuki
group; simplicity and the almost-simple reduction are not needed for this step. -/
theorem even_card_of_subgroup_equiv (L : Subgroup G) {m : ℕ} (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) : Even (Nat.card G) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ L.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv]
  exact even_iff_two_dvd.mp (suzukiMatrixGroup_even_card m hm)

variable [Finite G] [IsSimpleGroup (generalizedFitting G)]

/-- The Suzuki branch of E.1.14(1): even ambient order, upper E-generation,
and a concrete proper-subgroup obstruction at the preceding rank. All witnesses
lie in the original ambient group; the outer two-extension is discharged by
the proved automorphism calculation. -/
theorem generation_inputs (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {m : ℕ} (hm : 0 < m) (e : generalizedFitting G ≃* SuzukiMatrixGroup m) :
    Even (Nat.card G) ∧ IsEGenerated (2 * m + 1) G ∧
      ∃ (S : Sylow 2 G) (Ω : Set (Subgroup G)), IsElementaryFamily Ω ∧
        ∃ M : Subgroup G, M ≠ ⊤ ∧
          normalizer (weakClosure (S : Subgroup G) Ω : Set G) ≤ M ∧
          ∀ A ∈ Ω, A ≤ (S : Subgroup G) → ∀ K : Subgroup G,
            IsEMemberAt (2 * m + 1 - 1) (S : Subgroup G) A K → K ≤ M := by
  have hL := generalizedFitting_eq_top T hgen hm e
  let f : G ≃* SuzukiMatrixGroup m :=
    ((MulEquiv.subgroupCongr hL).trans topEquiv).symm.trans e
  exact ⟨even_card_of_subgroup_equiv _ hm e, model_isEGenerated hm f,
    model_predecessor_obstruction hm f⟩

/-- E.1.14(1) for a genuine Suzuki socle of odd field degree greater than one.
The minimum is attained by upper generation and is forced to this degree by
the elementary-family obstruction. -/
theorem generationParameter_eq (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {m : ℕ} (hm : 0 < m) (e : generalizedFitting G ≃* SuzukiMatrixGroup m) :
    generationParameter G = 2 * m + 1 := by
  obtain ⟨heven, hupper, S, Ω, hΩ, M, hM, hnorm, hmembers⟩ :=
    generation_inputs T hgen hm e
  have hpos : 0 < 2 * m + 1 := by omega
  have hspec := generationParameter_spec (Nat.not_odd_iff_even.mpr heven)
    ⟨2 * m + 1, hpos, hupper⟩
  apply Nat.le_antisymm (generationParameter_le hpos hupper)
  by_contra h
  have hle : generationParameter G ≤ 2 * m + 1 - 1 := by omega
  obtain ⟨A, hA, hAS, K, hK, hKM⟩ :=
    ((hspec.2 S).mono hle).exists_member_not_le Ω hΩ M hM hnorm
  exact hKM (hmembers A hA hAS K hK)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
