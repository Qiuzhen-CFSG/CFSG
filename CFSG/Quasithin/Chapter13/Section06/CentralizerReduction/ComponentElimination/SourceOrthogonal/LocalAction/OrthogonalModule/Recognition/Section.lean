module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Action
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Geometry
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# The literal moved and central spaces in the plus representation

The linear span of the action differences is exactly the additive form of
[W_K,K]. The fixed space is exactly its intersection with C_G(K). Relative
normality of K in KT_v makes both spaces invariant under the entire plus
actor, so their quotient retains that action. The source 13.6.14 identity
then identifies the upper space with U_K, without identifying U_K with K.

These transport and construction results supply the actual carrier for the
B.5.1 recognition step. They do not select a classification alternative.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.14,
printed p.930, and the paragraph after 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Linearization retains the literal conjugation formula on representatives. -/
theorem representation_mk_apply (a : plusActor K L T v) (w : Additive (WK K L T z v)) :
    ((representation K L T z v hL hz (plusMk K L T z v hL hz a) w).toMul : G) =
      (a : G) * (w.toMul : G) * (a : G)⁻¹ := rfl

private def subgroupSpace (H : Subgroup G) : Submodule (ZMod 2) (Additive (WK K L T z v)) :=
  AddSubgroup.toZModSubmodule (n := 2) ((H.comap (WK K L T z v).subtype).toAddSubgroup)

/-- The linear moved space is precisely the ambient group commutator. -/
theorem moved_mem (w : Additive (WK K L T z v)) :
    w ∈ moved (representation K L T z v hL hz) (plusImage K L T z v hL hz K) ↔
      (w.toMul : G) ∈ ⁅WK K L T z v, K⁆ := by
  let ρ := representation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let S := moved ρ C
  have hle : S ≤ subgroupSpace K L T z v ⁅WK K L T z v, K⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨k, hk, rfl⟩, u, _, rfl⟩
    change ((ρ (plusMk K L T z v hL hz k) u).toMul : G) / (u.toMul : G) ∈
      ⁅WK K L T z v, K⁆
    rw [representation_mk_apply, div_eq_mul_inv]
    exact (commutator_comm _ _).le (commutator_mem_commutator hk u.toMul.property)
  constructor
  · exact fun hw => hle hw
  · intro hw
    let H := S.toAddSubgroup.toSubgroup'.map (WK K L T z v).subtype
    have hcomm : ⁅WK K L T z v, K⁆ ≤ H := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro k hk u hu
      let a : plusActor K L T v := ⟨k, K_le_plusActor K L T v hk⟩
      let x : Additive (WK K L T z v) := Additive.ofMul ⟨u, hu⟩
      let d := ρ (plusMk K L T z v hL hz a) x - x
      refine ⟨d.toMul, ?_, ?_⟩
      · change d ∈ S
        exact Submodule.subset_span ⟨plusMk K L T z v hL hz a, ⟨a, hk, rfl⟩,
          x, Submodule.mem_top, rfl⟩
      · change ((ρ (plusMk K L T z v hL hz a) x).toMul : G) / (x.toMul : G) = _
        rw [representation_mk_apply, div_eq_mul_inv]
        rfl
    obtain ⟨u, hu, he⟩ := hcomm hw
    have he' : u = w.toMul := Subtype.ext he
    change Additive.ofMul u ∈ S at hu
    have he'' : Additive.ofMul u = w := congrArg Additive.ofMul he'
    exact he'' ▸ hu

/-- Fixing by the image of K means centralizing the original K. -/
theorem fixed_mem (w : Additive (WK K L T z v)) :
    w ∈ fixedSpace (representation K L T z v hL hz) (plusImage K L T z v hL hz K) ↔
      (w.toMul : G) ∈ centralizer (K : Set G) := by
  constructor
  · intro hf
    apply mem_centralizer_iff.mpr
    intro k hk
    let a : plusActor K L T v := ⟨k, K_le_plusActor K L T v hk⟩
    have he := congrArg (fun x : Additive (WK K L T z v) => (x.toMul : G))
      (hf ⟨plusMk K L T z v hL hz a, ⟨a, hk, rfl⟩⟩)
    change (k * (w.toMul : G)) * k⁻¹ = (w.toMul : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hf ⟨a, k, hk, he⟩
    subst a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (k : G) * (w.toMul : G) * (k : G)⁻¹ = (w.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hf k hk)

/-- Both literal spaces carry the entire plus action. -/
noncomputable def movedSection
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K) := by
  let ρ := representation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  have hnorm : (⊤ : Subgroup (Gplus K L T z v hL hz)) ≤ normalizer (C : Set _) := by
    rw [Subgroup.normalizer_eq_top]
  have hstable := subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by simp)) hnorm
  let U : Subrepresentation ρ :=
    { toSubmodule := moved ρ C
      apply_mem_toSubmodule := fun g u hu =>
        (hstable (mem_top g) u).2 hu }
  exact
    { space := U
      space_eq := rfl
      central :=
        { toSubmodule := fixedSpace U.toRepresentation C
          apply_mem_toSubmodule := fun g u hu =>
            (fixedSpace_stable_of_normal U.toRepresentation C (mem_top g) u).2 hu }
      central_eq := rfl }

/-- The canonical upper space retains its ambient membership test. -/
theorem movedSection_upper_mem
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (w : Additive (WK K L T z v)) :
    w ∈ (movedSection K L T z v hL hz hK hLK).space.toSubmodule ↔
      (w.toMul : G) ∈ ⁅WK K L T z v, K⁆ := moved_mem K L T z v hL hz w

/-- The canonical lower space is the complete K-centralizer in the upper space. -/
theorem movedSection_central_mem
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (w : (movedSection K L T z v hL hz hK hLK).space.toSubmodule) :
    w ∈ (movedSection K L T z v hL hz hK hLK).central.toSubmodule ↔
      (w.val.toMul : G) ∈ centralizer (K : Set G) := by
  rw [← fixed_mem K L T z v hL hz]
  constructor
  · intro h g
    exact congrArg Subtype.val (h g)
  · intro h g
    exact Subtype.ext (h g)

/-- The source's U_K is the upper space, by the genuine 13.6.14 transport. -/
theorem movedSection_upper_source
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (w : Additive (WK K L T z v)) :
    w ∈ (movedSection K L T z v hL hz hK hLK).space.toSubmodule ↔
      (w.toMul : G) ∈ UX L z v (starImage z v K) := by
  rw [(invariant_component_consequences K L T z v hY hK).2]
  exact movedSection_upper_mem K L T z v hL hz hK hLK w

/-- Every B.5.1 section with this action has the same literal upper space. -/
theorem section_upper_mem
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (w : Additive (WK K L T z v)) :
    w ∈ s.space.toSubmodule ↔ (w.toMul : G) ∈ ⁅WK K L T z v, K⁆ := by
  rw [s.space_eq]
  exact moved_mem K L T z v hL hz w

/-- The B.5.1 central subspace keeps all fixed vectors, including extension kernels. -/
theorem section_central_mem
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (w : s.space.toSubmodule) :
    w ∈ s.central.toSubmodule ↔ (w.val.toMul : G) ∈ centralizer (K : Set G) := by
  rw [s.central_eq, ← fixed_mem K L T z v hL hz]
  constructor
  · intro h g
    exact congrArg Subtype.val (h g)
  · intro h g
    exact Subtype.ext (h g)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
