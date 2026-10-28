module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair

/-!
# Discharging invariance in the Rudvalis extension cover

Apply the proved invariance of the literal aligned local pair to the existing
normal-extension transport. Only the independent generation equality and local
quotient models remain as explicit premises. The ambient Sylow, generalized
Fitting subgroup and model equivalence are exactly those of the source
application; no restriction to the simple ambient group is made.

Source: Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9;
GLS3 Table 5.3r. Final discharge of generation and quotient models belongs to
the extension-cover assembly.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Rudvalis
variable {G : Type*} [Group G] [Finite G]

/-- The source extension cover with the concrete invariance premise discharged. -/
theorem exists_local_cover_of_model_generation {K : GroupClass}
    (hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (hmodels : LocalQuotientModels) (T : Sylow 2 G)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model)
    (hgen : _root_.Rudvalis.SylowInvariantPair.locals 0 ⊔
      _root_.Rudvalis.SylowInvariantPair.locals 1 = ⊤) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H :=
  exists_local_cover_of_model_geometry hG hmodels T hLT e hgen
    _root_.Rudvalis.SylowInvariantPair.locals_invariant

end CFSG.Quasithin.ChapterE.Rudvalis
