module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalQuotients
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups

/-!
# Assembly for the Rudvalis upper E-generation bound

For each member H of a generating family of Sylow overgroups, a faithful
simple normal subgroup of H/O₂(H), a two-group quotient and two-rank at most
two imply IsEGenerated 2 H. Restriction of elementary families and inheritance
of the literal E-members then give IsEGenerated 2 G.

The concrete max4 and aligned max6 locals supply the generating cover. Their
intrinsic two-core quotients are PSL₃(2) and S₅. The extension-cover theorem
transports them into the simple normal subgroup L = F*(G), adjoins the actual
ambient Sylow subgroup T, and proves the required quotient structure for
each join. Simplicity comes from the source hypothesis through the genuine
equivalence L ≃* Rudvalis.Model. Thus all permitted extensions G = LT are
included, without a reduction to G = L or an outer-automorphism assumption.

Applying the local-to-global argument of Aschbacher--Smith E.1.12 proves
the Rudvalis clause of E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9:
IsEGenerated 2 G and consequently n(G) ≤ 2. The source application
discharges the concrete cover and quotient inputs completely.

The local criterion is proved using corrected local tau, intrinsic quotients,
and the established normal-two-kernel lifting theorem. Thus general existence
of an E-generation bound is not an additional premise of this route.
-/

public section

namespace CFSG.Quasithin.ChapterE.Rudvalis

open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Convert the structural quotient witnesses into the E-generation bounds
for every member of the supplied Sylow-overgroup family. -/
theorem rankTwo_generatingFamily_of_local_cover (T : Sylow 2 G)
    (Δ : Set (Subgroup G)) (hgen : sSup Δ = ⊤)
    (hlocal : ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H) :
    sSup Δ = ⊤ ∧ ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H := by
  refine ⟨hgen, ?_⟩
  intro H hH
  exact ⟨(hlocal H hH).1, isEGenerated_two_of_local_quotient (hlocal H hH).2⟩

/-- E.1.12 applied to the structural local quotient criterion. The generating
cover is an explicit remaining mathematical input, not a claimed model fact. -/
theorem isEGenerated_two_of_local_cover (T : Sylow 2 G)
    (Δ : Set (Subgroup G)) (hgen : sSup Δ = ⊤)
    (hlocal : ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H) :
    IsEGenerated 2 G := by
  obtain ⟨_, hfamily⟩ := rankTwo_generatingFamily_of_local_cover T Δ hgen hlocal
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 2 T Ω
  rw [← hgen]
  apply sSup_le
  intro H hH
  exact ChiefOrbit.overgroup_le_generationTarget T H (hfamily H hH).1 hΩ
    (hfamily H hH).2

/-- The actual Sylow-overgroup family for the Rudvalis clause of E.1.14(5),
with rank-two E-generation proved for every member. -/
theorem exists_rankTwo_generatingFamily {K : GroupClass}
    (hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H := by
  obtain ⟨Δ, hgen, hlocal⟩ := exists_local_cover hG localQuotientModels T hLT e
  exact ⟨Δ, rankTwo_generatingFamily_of_local_cover T Δ hgen hlocal⟩

/-- E.1.14(5), Rudvalis: the original ambient group is rank-two E-generated.
The intrinsic quotient calculations and extension-compatible cover have no
remaining premises beyond the source hypotheses. -/
theorem isEGenerated_two {K : GroupClass}
    (hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model) : IsEGenerated 2 G := by
  obtain ⟨Δ, hgen, hlocal⟩ := exists_local_cover hG localQuotientModels T hLT e
  exact isEGenerated_two_of_local_cover T Δ hgen hlocal

/-- The source numerical conclusion n(G) ≤ 2 for the Rudvalis case,
including all extensions allowed by L = F*(G) and G = LT. -/
theorem generationParameter_le_two {K : GroupClass}
    (hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model) :
    generationParameter G ≤ 2 :=
  generationParameter_le (by decide) (isEGenerated_two hG T hLT e)

end CFSG.Quasithin.ChapterE.Rudvalis
