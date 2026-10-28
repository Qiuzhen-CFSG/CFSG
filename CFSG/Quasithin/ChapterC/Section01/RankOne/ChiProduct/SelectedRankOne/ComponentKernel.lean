module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentLift
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.Alternating.OddCentralCovers
/-!
# The selected component's actual core and Frattini kernel

The original action factors through the intrinsic two-core quotient. Once
that quotient is quasisimple, its covering kernel is central and therefore
Frattini. For the A₅ factor, the nonexceptional multiplier and trivial
two-core remove the center entirely. The resulting isomorphism agrees
with the original action on every representative.

Source: Aschbacher–Smith C.1.26, p.132, using A.3.6 and B.6.8.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- The actual action on a quasisimple core quotient has Frattini kernel. -/
theorem quasisimple_core_action_kernel
    [IsQuasisimple (G ⧸ pCore 2 G)] [IsQuasisimple D]
    (q : G →* D) (hq : Function.Surjective q) (h2 : pCore 2 D = ⊥) :
    q.ker ≤ (frattini (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) := by
  let Q := pCore 2 G
  have hQ : Q ≤ q.ker := by
    apply (Subgroup.map_eq_bot_iff Q).mp
    apply le_bot_iff.mp
    rw [←h2]
    exact le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  let f : G ⧸ Q →* D := QuotientGroup.lift Q q hQ
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _ hq _
  let c : Covering (G ⧸ Q) D := { toMonoidHom := f, surjective := hf }
  intro g hg
  exact center_le_frattini_of_isPerfect (c.ker_le_center (show f (QuotientGroup.mk' Q g) = 1 from hg))

/-- A subnormal factor with quasisimple core quotient retains its own
Frattini bound, independently of the ambient residual's kernel. -/
theorem component_action_kernel
    (q : G →* D) (h2 : pCore 2 D = ⊥)
    (L : Subgroup G)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hA : IsComponent D (L.map q)) :
    L ⊓ q.ker ≤ ChapterB.BaumannArgument.coreFrattini L := by
  let := hA.2
  have h2A : pCore 2 (L.map q) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hA.1,h2,MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (L.map q).subtype_injective
  have hk := quasisimple_core_action_kernel (q.subgroupMap L) (q.subgroupMap_surjective L) h2A
  intro g hg
  refine ⟨⟨g,hg.1⟩,hk ?_,rfl⟩
  exact Subtype.ext hg.2

/-- The nonexceptional A₅ multiplier removes the entire residual center. -/
theorem five_core_quotient_equiv
    [IsQuasisimple (G ⧸ pCore 2 G)]
    (q : G →* alternatingGroup (Fin 5)) (hq : Function.Surjective q) :
    ∃ e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5),
      ∀ g : G, e (QuotientGroup.mk' (pCore 2 G) g) = q g := by
  let A := alternatingGroup (Fin 5)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple A := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have h2 : pCore 2 A = ⊥ := by
    apply le_bot_iff.mp
    exact (IsQuasisimple.pCore_le_center 2).trans (alternatingGroup.center_eq_bot (by simp)).le
  let Q := pCore 2 G
  have hQ : Q ≤ q.ker := by
    apply (Subgroup.map_eq_bot_iff Q).mp
    apply le_bot_iff.mp
    rw [←h2]
    exact le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  let f : G ⧸ Q →* A := QuotientGroup.lift Q q hQ
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _ hq _
  let c : Covering (G ⧸ Q) A := { toMonoidHom := f, surjective := hf }
  let e : (G ⧸ Q) ⧸ center (G ⧸ Q) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq c.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hzodd : Odd (Nat.card (center (G ⧸ Q))) := by
    have h := GLS3.Chapter5.OddCentralCovers.component_center_odd
      (pCore_quotient_pCore_eq_bot 2 (G := G)) (⊤ : Subgroup (G ⧸ Q))
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩
    rwa [Nat.card_congr (centerCongr (topEquiv :
      (⊤ : Subgroup (G ⧸ Q)) ≃* (G ⧸ Q))).toEquiv] at h
  have hc : Nat.card (center (G ⧸ Q)) = 1 := by
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 5 (by decide) e hzodd with h | ⟨h,_⟩
    · exact h
    · omega
  have hker : f.ker = ⊥ := c.ker_eq_center_of_isSimple.trans ((eq_bot_iff_card _).mpr hc)
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff _).mp hker,hf⟩,fun _ => rfl⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
