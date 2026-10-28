module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PointKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerRow
public import Theory.GroupTheory.CubicResidualSelection.ActorRank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredResidual

/-!
# The covered-row exclusion with the larger action kernel: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/LargerRow` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The non-two-group kernel and the earlier 13.3.9 conclusion construct
its nontrivial cubic residual, with the literal ambient embedding. -/
theorem centralizer_kernel_residual_of_source1339_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (Aplus : Subgroup G)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = Aplus ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
    let A := (pResidual 2 K).map K.subtype
    A.map H.subtype = Aplus ∧ Nat.card (A ⧸ pCore 2 A) = 3 := by
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz (fun he => hzL (he ▸ one_mem _))
  let := hU.normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let Z := A.map H.subtype
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hAK : A ≤ K := map_subtype_le _
  have hZM : Z ≤ normalizer (L : Set G) := by
    apply le_trans _ (LocalGeometry.centralizerOmegaOrbit_centralizer_le_normalizer_at h structural D m z.val)
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val ((hAK ha) ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hZn : H ≤ normalizer (Z : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hp : IsPPerfect 2 Z := (isPPerfect_embedded_pResidual 2 K).of_surjective
    (H.subtype.subgroupMap A) (H.subtype.subgroupMap_surjective A)
  have hne : Z ≠ ⊥ := by
    intro he
    have hA : A = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
    have hres : pResidual 2 K = ⊥ :=
      (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hA
    have hpK : IsPGroup 2 K := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hres).trans QuotientGroup.quotientBot)
    exact hlarge (le_antisymm (le_sSup ⟨inferInstance,hpK⟩) hQK)
  obtain ⟨he,hc⟩ := (h1339 Z (map_subtype_le _) hZn hZM hp).resolve_left hne
  refine ⟨he,?_⟩
  let e := A.equivMapOfInjective H.subtype H.subtype_injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
