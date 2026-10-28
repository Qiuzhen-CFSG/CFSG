module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiRemoteCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullCoreUpper

/-!
# An actual five-subgroup in the remote-center join

The two critical remote centers act transitively on the five actual
neighbors at the small-Suzuki vertex. Orbit-stabilizer and Cauchy's
theorem therefore produce an order-five subgroup of that same center
join. No equality with the entire starred parabolic is asserted.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal remote-center join contains an actual subgroup of order
five, inside the original reduced completion. -/
theorem source_small_suzuki_remote_centers_contain_five
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hq : Nat.card k = 2)
    {a x z w c : Vertex (reducedFamily L S)}
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (hca : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    : ∃ A : Subgroup (G₀ L S), A ≤ Z (reducedFamily L S) a ⊔ Z (reducedFamily L S) c ∧
        Nat.card A = 5 := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let E := Z F a ⊔ Z F c
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have haQ : Z F a ≤ Q F m := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ a m
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hxa.symm (Walk.cons hxm .nil))) hb)
    (reduced_kernel_sylow h m)
  have hcQ : Z F c ≤ Q F z := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ c z
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hwc.symm (Walk.cons hwz .nil))) hb)
    (reduced_kernel_sylow h z)
  have hEP : E ≤ star L S i := sup_le
    (haQ.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _)))
    (hcQ.trans ((le_sup_left.trans hR.ge).trans (map_subtype_le _)))
  have hEy : E ≤ stabilizer F y := hEP.trans (star_le_stabilizer i)
  let : Finite E := Finite.of_injective (inclusion hEy) (inclusion_injective _)
  have htrans := small_suzuki_remote_critical_center_transitive h i hb e
    hxa hxm hyz hwz hwc hne hca hcc T R hT hR
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have horbit : MulAction.orbit E m = (graph F).neighborSet y := by
    ext v
    constructor
    · rintro ⟨g,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G₀ L S)).map_adj_iff.mpr hym
      change (graph F).Adj ((g : G₀ L S) • y) ((g : G₀ L S) • m) at hh
      rwa [show (g : G₀ L S) • y = y from hEy g.property] at hh
    · intro hv
      obtain ⟨g,hg,he⟩ := htrans v hv
      exact ⟨(⟨g,hg⟩ : E),he⟩
  have hcard : Nat.card (MulAction.orbit E m) = 5 := by
    rw [horbit]
    have hh := source_linear_suzuki_neighbor_cards h (!i) eLin
      (by cases i <;> exact e) (by simpa only [Nat.mul_zero,Nat.zero_add,pow_one] using hq) y
    change Nat.card ((graph F).neighborSet y) = if i = !i then 3 else 5 at hh
    rw [if_neg (by cases i <;> decide)] at hh
    exact hh
  have hd : 5 ∣ Nat.card E := by
    rw [←hcard,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer E m)]
    exact (MulAction.stabilizer E m).card_quotient_dvd_card
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A,hAc⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 5
    (n := 1) (by simpa only [pow_one] using hd)
  refine ⟨A.map E.subtype,map_subtype_le _,?_⟩
  rw [card_map_of_injective E.subtype_injective]
  simpa only [pow_one] using hAc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
