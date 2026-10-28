module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import Theory.GroupTheory.Commutator.PerfectSolvableKernel

/-!
# Lifting natural point generation to the original actor

A kernel fixing the points normalizes each point residual. If their join
surjects modulo that kernel, the join is consequently normal in the whole
actor. Perfectness removes the remaining solvable quotient. Applied to the
original chosen module, O2(L) fixes V by the actual chosen action, and L is
perfect by its source membership. Thus quotient generation suffices for the
literal PointGeneration predicate; no splitting of L is needed.

The remaining input is the marked SL3/Sp4 point-generation calculation.
Source: Aschbacher--Smith, 11.5.3(1), printed p.779.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
open Subgroup
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Kernel elements fixing the points normalize each point residual. -/
theorem centralizer_normalizes_pointResidual (L : Subgroup G) (u : G) :
    L ⊓ centralizer ({u} : Set G) ≤ normalizer (pointResidual L u : Set G) := by
  let H := L ⊓ centralizer ({u} : Set G)
  exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H
    (solvableResidual H))

noncomputable def pointResidualJoin (L A : Subgroup G) : Subgroup G :=
  ⨆ u : {u : G // u ∈ A ∧ u ≠ 1}, pointResidual L u.val

omit [Finite G] in
theorem pointResidualJoin_le (L A : Subgroup G) : pointResidualJoin L A ≤ L :=
  iSup_le fun _ => (residualIn_le _).trans inf_le_left

omit [Finite G] in
theorem pointResidualJoin_lift (L A : Subgroup G) [Group.IsPerfect L]
    (N : Subgroup L) [N.Normal] [Group.IsSolvable N]
    (hNA : N.map L.subtype ≤ centralizer (A : Set G))
    (himage : ((pointResidualJoin L A).subgroupOf L).map
      (QuotientGroup.mk' N) = ⊤) : L ≤ pointResidualJoin L A := by
  let J := pointResidualJoin L A
  let C := J.subgroupOf L
  let q := QuotientGroup.mk' N
  have hNJ : N.map L.subtype ≤ normalizer (J : Set G) := by
    apply (le_iInf fun u => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    apply le_trans _ (centralizer_normalizes_pointResidual L u.val)
    apply le_inf (map_subtype_le _)
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact (hNA hx u.val u.property.1).symm
  have hNC : N ≤ normalizer (C : Set L) := by
    apply le_normalizer_iff.mpr
    intro n hn c hc
    exact le_normalizer_iff.mp hNJ n.val (mem_map_of_mem L.subtype hn) c.val hc
  have hcover : C ⊔ N = ⊤ := by
    have he := congrArg (Subgroup.comap q) himage
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk', comap_top] using he
  have hnormal : (⊤ : Subgroup L) ≤ normalizer (C : Set L) := by
    rw [← hcover]
    exact sup_le C.le_normalizer hNC
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  have htop : (⊤ : Subgroup L) ≤ C :=
    le_of_map_le_of_perfect_solvable_kernel q ⊤ C le_top hnormal (by
      rw [show C.map q = ⊤ from himage]
      exact le_top)
  intro x hx
  exact htop (show (⟨x, hx⟩ : L) ∈ (⊤ : Subgroup L) from mem_top _)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

include D in
theorem core_centralizes_chosen : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨v', hv'⟩ := D.spaceEquiv.surjective ⟨v, hv⟩
  have hh := LinearMap.congr_fun (show D.chosenAction l = 1 from
    D.chosenAction_core hl) v'.toAdd
  have he := congrArg (fun w : D.space => (w.val.toMul.val : G)) hh
  have hv'' : (v'.toAdd.val.toMul.val : G) = v :=
    (D.spaceEquiv_apply v'.toAdd).symm.trans (congrArg Subtype.val hv')
  change (l : G) * (v'.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
    (v'.toAdd.val.toMul.val : G) at he
  rw [hv''] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Only the finite marked-model calculation remains. -/
def QuotientPointGeneration (L V V₁ : Subgroup G) : Prop :=
  ∀ A : Subgroup G, A ≤ V →
    (∀ l ∈ L, ¬ A ≤ V₁.map (MulAut.conj l : G →* G)) →
    ((pointResidualJoin L A).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) = ⊤

theorem pointGeneration_of_quotient (S : D.NonbinaryNaturalInput) (V₁ : Subgroup G)
    (hgen : QuotientPointGeneration L V V₁) : PointGeneration L V V₁ := by
  let : Group.IsPerfect L := CFSG.Quasithin.Chapter1.mem_L_isPerfect
    S.source.maximal_faithful.1.1
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  intro A hAV havoid
  exact pointResidualJoin_lift L A (pCore 2 L)
    ((core_centralizes_chosen D).trans (centralizer_le hAV)) (hgen A hAV havoid)

/-- The numerical intersection application now asks only for generation in
the literal two-core quotient. The lift to the original L is discharged. -/
theorem intersection_and_rank_of_quotient (E : Geometry D) (F₀ : MarkedFlag E)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hres : pointResidual L E.z = E.L₁) (hK : E.Kz = E.K)
    (hgen : QuotientPointGeneration L V E.V₁)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hKL : E.K = E.L₁) :
    (∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        E.V₁.map (MulAut.conj l : G →* G)) ∧
      (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ ChapterE.globalR V :=
  intersection_and_rank F₀ hfixed hz hz1 htrans hres hK
    (pointGeneration_of_quotient D E.input E.V₁ hgen) hTI hKL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
