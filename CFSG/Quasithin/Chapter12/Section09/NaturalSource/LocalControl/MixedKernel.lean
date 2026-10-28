module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedBinary
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.MiddleKernel

/-!
# Excluding the transvection-flag kernel in the mixed movement obstruction

The literal mixed quotient constructed from a failure of plane movement has
kernel order sixteen. Its kernel normalizer normalizes the actual image of
L₁, already identified with the two-residual. The binary five-space kernel
calculation excludes the transvection flag using precisely these maps and
normalizers. Only the two adjacent-end flags remain.

The final application feeds this reduction to the original LocalControl
consumer. Movement excludes the adjacent flags by their actual kernel action.
The centralizer/model and component premises remain with
qt-d-1291-natural-source; this does not establish LocalControlInput.
Source: Aschbacher--Smith,12.9.5(3)--6, printed pp.860--862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original mixed section, retaining all maps, with only adjacent-end flags. -/
@[expose] def MixedAdjacentPointSection [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) : Prop :=
  ∃ e : ((C.K1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)) ≃* LinearGroup 5,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))
      let B := F.Li L 1 ⊔ (T : Subgroup G)
      let r := q.comp (inclusion (sup_le_sup_right C.contains (T : Subgroup G)))
      let J := r.range
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∃ a : J →* BinaryLinear.parabolic (space (V := V) (F.Vi 1)),
        Function.Surjective a ∧
        (∀ (b : B) (v : Additive V),
          (((a (r.rangeRestrict b)).val v).toMul : G) =
            (b : G) * (v.toMul : G) * (b : G)⁻¹) ∧
        a.ker = (Q.subgroupOf B).map r.rangeRestrict ∧
        IsPGroup 2 a.ker ∧
        ((F.Li L 1).subgroupOf B).map r = (pResidual 2 J).map J.subtype ∧
        normalizer (a.ker.map J.subtype : Set (LinearGroup 5)) ≤
          normalizer (((F.Li L 1).subgroupOf B).map r : Set (LinearGroup 5)) ∧
        Nat.card J = 21504 ∧ Nat.card a.ker = 16 ∧
        (∃ b : FiveBasis, J = flagStabilizer b {0,1} ∨ J = flagStabilizer b {2,3})

omit [Finite G] in
/-- The source kernel-normalizer restriction excludes the transvection flag;
no extra source hypothesis or replacement of the literal action is used. -/
theorem mixedPointSection_adjacent [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (s : MixedPointSection F C) : MixedAdjacentPointSection F C := by
  obtain ⟨e,a,ha,hact,hker,hp,hres,hn,hJ,hk,b,hflag⟩ := s
  refine ⟨e,a,ha,hact,hker,hp,hres,hn,hJ,hk,b,?_⟩
  rcases hflag with he | he | he
  · exact Or.inl he
  · exfalso
    let X := C.K1 ⊔ (T : Subgroup G)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
    let r := q.comp (inclusion (sup_le_sup_right C.contains (T : Subgroup G)))
    let J := r.range
    let Q := a.ker.map J.subtype
    have hQJ : Q ≤ J := map_subtype_le _
    have hJN : J ≤ normalizer (Q : Set (LinearGroup 5)) := by
      apply (normal_subgroupOf_iff_le_normalizer hQJ).mp
      change ((a.ker.map J.subtype).comap J.subtype).Normal
      rw [comap_map_eq_self_of_injective J.subtype_injective]
      infer_instance
    have hc : Nat.card Q = 16 := (card_map_of_injective J.subtype_injective).trans hk
    have hh := BinaryLinear.FivePointSection.MiddleKernel.no_middle_kernel b Q
      (hp.map _) hc (by rwa [←he]) (by rwa [←he]) (by rwa [←he])
    apply hh
    rw [←he,←hres]
    exact hn
  · exact Or.inr he

/-- A movement failure in the mixed row now has an adjacent-end flag, with
its original action and the actual kernel image unchanged. -/
theorem mixed_plane_fixed_adjacent_section
    (h : HigherRankHypothesis K T L V 4) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hfix : ⁅F.Vi 2,C.K1.pCoreIn 2⁆ = ⊥) :
    letI := h.chosen.elementary
    MixedAdjacentPointSection F C := by
  let := h.chosen.elementary
  exact mixedPointSection_adjacent F C (mixed_plane_fixed_section h earlier F C hm hfix)

/-- Actual LocalControl application, reducing every remaining movement failure
to one of the two adjacent-end flags excluded by source12.9.5(3). The
source premises themselves remain obligations of this assembly owner. -/
theorem localControl_or_mixed_adjacent_section
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    LocalControl C ∨ (n = 4 ∧ letI := h.chosen.elementary; MixedAdjacentPointSection F C) := by
  rcases localControl_or_mixed_point_section h hn earlier F C hcentral hmodels hplane with
    hc | ⟨hn,hs⟩
  · exact Or.inl hc
  · let := h.chosen.elementary
    exact Or.inr ⟨hn,mixedPointSection_adjacent F C hs⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
