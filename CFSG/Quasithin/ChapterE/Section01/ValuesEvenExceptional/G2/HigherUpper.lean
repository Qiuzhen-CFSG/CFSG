module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.RadicalQuotient
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.LinearRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.GenerationTransfer

/-!
# Nonbinary G₂ parabolic E-generation

For q = 2^f with f > 1, each literal transported root parabolic joined with
T is E-generated at rank f. Its intrinsic solvable-radical quotient has
simple generalized Fitting subgroup PSL₂(2^f), supplemented by every Sylow
two-subgroup. The actual matrix model proves nonabelianness and the elementary
rank bound, including outer field automorphisms. Simple-socle structure
supplies the radical, residual and local tau clauses of E.1.2(E2), so the
whole quotient is an E-member whenever the elementary subgroup is nontrivial.
Lifting through the solvable radical completes the local calculation.

The final theorem aligns the Sylow intersection by conjugacy and applies
E.1.12 to the two parabolic overgroups. This proves the nonbinary upper bound
without extra splitting, faithfulness or local-generation premises. The argument only
uses normality of L; the source hypotheses L = F*(G), simplicity and SQTK
are therefore more than is needed for this upper bound. The lower bound for
the exact value n(G) remains with the E.1.14 assembly owner.

The earlier transport and solvable-kernel exports are preserved through
`HigherUpper.Transport`, which also avoids a cycle with `RadicalQuotient`.

Source: Aschbacher--Smith, E.1.14(1), printed p.214 (PDF p.225), citing
Aschbacher (1982), Lemma 4.7. We use the revised local tau convention of
E.1.2, printed pp.209--210. The concrete model retains the licensed ATLAS
attribution; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Theory.GroupTheory Atlas.G2
open CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- Each literal transported root parabolic joined with T is E-generated at
rank f. The radical quotient has a simple PSL₂(2^f) socle; its faithful
automorphism action bounds elementary ranks, and its whole-group component
satisfies the intrinsic E2 conditions. Solvable-kernel lifting returns to
the actual overgroup, including arbitrary outer two-extensions. -/
theorem higher_parabolicOvergroup_isEGenerated {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    IsEGenerated f (parabolicOvergroup L T e i) := by
  apply higher_parabolicOvergroup_isEGenerated_of_radical_quotient hf L T e i
  let Q := (parabolicOvergroup L T e i) ⧸ solvableRadical (parabolicOvergroup L T e i)
  obtain ⟨hsimple, ⟨a⟩, hgen⟩ :=
    RadicalQuotient.parabolicOvergroup_structure hf hF L T e he i
  let : IsSimpleGroup (generalizedFitting Q) := hsimple
  have ha := linear_socle_not_isMulCommutative (generalizedFitting Q) a
  have hC := SimpleSocle.centralizer_eq_bot ha
  intro S
  apply linear_isEGeneratedAt_of_top_component (by omega) a hC S
  intro A _ _ hne
  exact eCaseComponent_top ha S (hgen S) (S : Subgroup Q) A hne

/-- The nonbinary ambient upper bound, applying the local calculation to
the two generating parabolic overgroups. Sylow conjugacy supplies the
alignment, so no alignment or local-generation premise remains. In E.1.14
one takes L = F*(G); normality suffices for this upper-bound argument. -/
theorem isEGenerated_of_higher_socle {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* commutator (Model F))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) : IsEGenerated f G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a, ha⟩ := exists_sylow_aligned_equiv L T e
  exact isEGenerated_of_parabolicOvergroups L T a hLT
    (higher_parabolicOvergroup_isEGenerated hf hF L T a ha)

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
