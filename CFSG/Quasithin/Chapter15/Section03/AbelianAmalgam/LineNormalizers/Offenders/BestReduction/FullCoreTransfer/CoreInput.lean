module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.MarkedOrbitCore
public import Theory.Representation.BinaryOffender.CubicMarker
public import Theory.Quasithin.Rank

/-!
# B.5.3 on the actual best-offender subgroup of the faithful image

The marker's Sylow fixedness and orbit span give a trivial two-core. Normality
and restriction supply the corresponding hypotheses for J(D,W), including its
own best generation. The SQTK witness keeps the original covering group and
quotient map, then pulls back the actual subgroup. No claim that D itself is
an SQTK group is needed.

Source: Aschbacher–Smith, B.5.3, printed p.104, and the proof of 15.3.67,
pp.1153–1154 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open ChapterB.SourceInduction
universe u v
variable {D : Type u} [Group D] [Finite D] {W : Type v}
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- All B.5.3 hypotheses for N=J(D,W), established before classifying N. -/
theorem offenderCore_FFHypothesis {K : GroupClass.{u}}
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (S : Sylow 2 D) (P : Submodule (ZMod 2) W)
    (hfix : P ≤ fixedSpace ρ (S : Subgroup D))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : D) (v : W), v ∈ P ∧ ρ g v = w} = ⊤)
    (cover : SQTKQuotient K D) :
    FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype) := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  have hD := twoCore_eq_bot_of_sylow_fixed_span ρ hfaith S P hfix hspan
  have hN : pCore 2 N = ⊥ := by
    have hn : ((pCore 2 N).map N.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hle : (pCore 2 N).map N.subtype ≤ pCore 2 D :=
      le_sSup ⟨hn, pCore_isPGroup.map N.subtype⟩
    have hz : (pCore 2 N).map N.subtype = ⊥ := bot_unique (hD ▸ hle)
    exact ((pCore 2 N).map_eq_bot_iff_of_injective N.subtype_injective).mp hz
  exact ⟨inferInstance, hfaith.comp N.subtype_injective, hN,
    offenderSubgroup_restrict_eq_top ρ, ⟨cover.subgroup N⟩⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- The exact prime-to-three action kernel transfers the original rank bound
to the faithful image and then to its actual offender subgroup. -/
theorem image_offenderCore_threeRank_le_one
    (ρ : Representation (ZMod 2) D W)
    (hker : Nat.Coprime 3 (Nat.card (actionHom ρ).ker))
    (hr : primeRank 3 D ≤ 1) :
    primeRank 3 (offenderSubgroup (imageRepresentation ρ)) ≤ 1 := by
  have him := primeRank_le_of_surjective_of_coprime 3
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective hker
  exact (primeRank_subgroup_le 3 _).trans (him.trans hr)

omit [FiniteDimensional (ZMod 2) W] in
/-- Direct use of the preceding marker-centralizer calculation, with both
its quotient-rank consequence and its cubic obstruction on the same image. -/
theorem image_core_rank_and_marker
    (ρ : Representation (ZMod 2) D W) (P : Submodule (ZMod 2) W)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤)))
    (hr : primeRank 3 D ≤ 1) :
    primeRank 3 (offenderSubgroup (imageRepresentation ρ)) ≤ 1 ∧
      Nat.Coprime 3 (Nat.card (subspaceKernel (imageRepresentation ρ) P ⊤)) :=
  ⟨image_offenderCore_threeRank_le_one ρ
    (action_kernel_coprime_three_of_marker ρ P hP) hr,
    image_markerCentralizer_coprime_three ρ P hP⟩

section Cover
variable {H : Type u} [Group H] {W₀ : Type u}
  [AddCommGroup W₀] [Module (ZMod 2) W₀]

/-- The faithful image of any literal quotient subgroup retains a genuine
SQTK cover via its full inverse image in the original local group. -/
noncomputable def actionImage_sqtkCover {K : GroupClass.{u}}
    (hD : IsSQTK K D) (q : D →* H) (hq : Function.Surjective q)
    (I : Subgroup H) (σ : Representation (ZMod 2) H W₀) :
    SQTKQuotient K (actionImage (σ.comp I.subtype)) := by
  let f := (actionHom (σ.comp I.subtype)).comp (q.subgroupComap I)
  have hf₁ : Function.Surjective (actionHom (σ.comp I.subtype)) :=
    MonoidHom.rangeRestrict_surjective _
  have hf : Function.Surjective f := hf₁.comp
    (q.subgroupComap_surjective_of_surjective I hq)
  exact {
    Cover := I.comap q
    kernel := f.ker
    sqtk := hD.subgroup _
    equiv := QuotientGroup.quotientKerEquivOfSurjective f hf }
end Cover

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
