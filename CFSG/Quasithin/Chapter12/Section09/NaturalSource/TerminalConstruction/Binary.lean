module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Cubic
public import Theory.SpecificGroups.BinaryLinear.CubicSylowExtension

/-!
# The binary-linear terminal construction with its literal action premise

For K₁/O₂(K₁) isomorphic to PSL₄(2) or PSL₅(2), innerness of the T-action
makes the minimal parabolics invariant. Their lifted index-three overgroups
generate K₁T, so one escapes M. The existing cubic terminal construction
then supplies every clause of TerminalConfiguration and the final contradiction.
The A₇ case requires no innerness premise and was proved separately.

The remaining source obligation here is innerness on the literal component
quotient, not the existence of a terminal configuration or cubic overgroup.
It remains with `qt-d-1291-natural-source`, together with the component,
local-control and weak-closure stages. This conditional theorem is not 12.9.1.

Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Innerness is imposed on the actual point-normalizer action restricted to T. -/
def SylowActsInner {F : InvariantFlag T V n} (C : ComponentGeometry F L) : Prop :=
  ∀ t : T, pointQuotientAction C ⟨t, F.invariant 1 t.property⟩ ∈
    MulAut.innerSubgroup (C.K1 ⧸ pCore 2 C.K1)

/-- Lift a binary-linear minimal parabolic through the original component quotient. -/
theorem cubic_overgroup_of_binary_inner
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) (control : LocalControl C)
    {d : ℕ} (hd : 2 ≤ d) (model : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2)
    (inner : SylowActsInner C) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ H ≤ C.K1 ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex H = 3 ∧ ¬ H ≤ normalizer (L : Set G) := by
  have hTM := h.sylow_normalizes earlier.structural
  have hn : (T : Subgroup G) ≤ normalizer (C.K1 : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hout : ¬ C.K1 ≤ normalizer (L : Set G) :=
    fun hk => control.overgroup.2.2 (sup_le hk hTM)
  obtain ⟨k, hk, hfin, hcard, ⟨e⟩⟩ := model
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let eK := (e.trans (Atlas.fieldEquivPSL d ek)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  apply BinaryLinear.CubicSylowExtension.exists_cubic_overgroup (by omega)
    T C.K1 (normalizer (L : Set G)) hTM hn eK ?_ hout
  intro t ht
  exact inner ⟨t,ht⟩

/-- The source inner-action obligation, required only in the binary-linear rows. -/
def BinaryInnerActionInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C →
      (ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
        ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) → SylowActsInner C

/-- The binary action premise and the proved A₇ branch supply all cubic selections. -/
theorem cubicOvergroupInput_of_inner (source : BinaryInnerActionInput K) :
    CubicOvergroupInput K := by
  intro X _ _ T L V n h hn earlier F hab C control
  rcases control.models with ha | hfour | hfive
  · obtain ⟨e⟩ := ha
    exact cubic_overgroup_of_alternatingSeven h earlier F C control e
  · exact cubic_overgroup_of_binary_inner h earlier F C control (by decide) hfour
      (source X T L V n h hn earlier F hab C control (Or.inl hfour))
  · exact cubic_overgroup_of_binary_inner h earlier F C control (by decide) hfive
      (source X T L V n h hn earlier F hab C control (Or.inr hfive))

/-- The terminal stage is constructed once the actual binary Sylow action is inner. -/
theorem terminalInput_of_inner (source : BinaryInnerActionInput K) : TerminalInput K :=
  terminalInput_of_cubicOvergroups (cubicOvergroupInput_of_inner source)

/-- In a binary-linear row the constructed configuration gives the actual contradiction. -/
theorem contradiction_of_binary_inner
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (control : LocalControl C) (fusion : FusionControl T L V)
    {d : ℕ} (hd : 2 ≤ d) (model : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2)
    (inner : SylowActsInner C) : False := by
  obtain ⟨H,hTH,hHK,hi,hHM⟩ := cubic_overgroup_of_binary_inner h earlier F C control hd model inner
  obtain ⟨q⟩ := terminalConfiguration_of_cubic h hn earlier F hab control.normalizers fusion
    H hTH (hHK.trans (sup_le C.point_le (F.invariant 1))) hHM hi
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab fusion.hyperplanes
    q.H q.point_le q.g q.conjugate_le q.span_normalizes q.moves_plane
    q.hyperplane_normalizes q.hyperplane_index

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
