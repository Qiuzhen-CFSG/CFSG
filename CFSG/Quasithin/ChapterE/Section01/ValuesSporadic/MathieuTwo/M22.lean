module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuTwo.SmallQuotients
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete
public import Theory.Mathieu.M22.Properties.FixedHexads

/-!
# Rank-two E-generation for M22 and its outer extension

The concrete pair and hexad-partition stabilizers contain a common Sylow
two-subgroup and generate the ambient faithful extension of M22. Their
intrinsic two-core quotients are S5 and S3, even in the outer case. The
small-quotient generation proofs lift to these actual local subgroups.
E.1.8 then places both local groups in the ambient generation target.

Source: Aschbacher--Smith E.1.14(5), printed p.214, citing Asc82a Lemma 4.9;
the local pair is the one in E.4.3(2), printed pp.241--242.
-/

public section
namespace CFSG.Quasithin.ChapterE.MathieuTwo
open Subgroup Theory.GroupTheory Sporadic.Mathieu

variable {G : Type*} [Group G] [Finite G]

/-- Both local member bounds are proved for the full faithful extension,
including its outer two-extension. -/
theorem m22_rankTwo_family (L : Subgroup G) [L.Normal]
    (hC : centralizer (L : Set G) = ⊥) (e : L ≃* M22) (T : Sylow 2 G) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H := by
  obtain ⟨d⟩ := M22ValueBound.Concrete.nonempty_innerCompatiblePair L hC e T
  refine ⟨{d.first, d.second}, ?_, ?_⟩
  · simpa only [sSup_insert, sSup_singleton] using d.generate
  · intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact ⟨d.sylow_le_first,
        isEGenerated_of_twoCore_quotient_symmetricFive d.firstQuotient⟩
    · obtain rfl := Set.mem_singleton_iff.mp hH
      exact ⟨d.sylow_le_second,
        (isEGenerated_of_twoCore_quotient_symmetricThree d.secondQuotient).mono (by decide)⟩

/-- A faithful normal M22 suffices for ambient rank-two E-generation. -/
theorem m22_extension_isEGenerated (L : Subgroup G) [L.Normal]
    (hC : centralizer (L : Set G) = ⊥) (e : L ≃* M22) (T : Sylow 2 G) :
    IsEGenerated 2 G := by
  obtain ⟨Δ, hΔ, hlocal⟩ := m22_rankTwo_family L hC e T
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 2 T Ω
  rw [← hΔ]
  exact sSup_le fun H hH => ChiefOrbit.overgroup_le_generationTarget T H
    (hlocal H hH).1 hΩ (hlocal H hH).2

/-- The concrete simple M22 bound, used in the M23 point stabilizer. -/
theorem m22_isEGenerated : IsEGenerated 2 M22 := by
  apply m22_extension_isEGenerated ⊤ _ Subgroup.topEquiv (default : Sylow 2 M22)
  simpa only [coe_top, centralizer_univ] using m22_center_eq_bot

/-- The M22 case under the literal generalized-Fitting hypothesis of E.1.14.
No extra local, rank, or generation assumption remains. -/
theorem m22_generalizedFitting_isEGenerated (L : Subgroup G)
    (hL : L = generalizedFitting G) [IsSimpleGroup L]
    (e : L ≃* M22) (T : Sylow 2 G) : IsEGenerated 2 G := by
  subst L
  have ha : ¬ IsMulCommutative (generalizedFitting G) := by
    intro hc
    let := hc
    have hp : (Nat.card (generalizedFitting G)).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [Nat.card_congr e.toEquiv, m22_order] at hp
    norm_num at hp
  exact m22_extension_isEGenerated _ (SimpleSocle.centralizer_eq_bot ha) e T

end CFSG.Quasithin.ChapterE.MathieuTwo
