module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CentralIntersection

/-!
# The literal central quotient layer in DGS p.180

In the central alternative of DGS (12.3)(c), the equality of the graph
intersection with the natural middle center bounds the commutator image of
the opposite local action on `V_y/Z_y`. The central layer is the image of
`Z_m` and has order `q`; the statement retains the literal original actor,
the quotient map, and its conjugation formula.

This is an intermediate in the p.180 central-case argument. It neither proves
that the quotient module is natural nor applies the contradictory DGS (8.5)
conclusion. The earlier Chapter 8 input and the separate middle-core product
remain necessary for the full source theorem.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (8.5), (12.1)(d--g), and (12.3), printed pp.132, 178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source central-case layer bound with the original quotient action.

If the intersection of the two actual radius-one subgroups centralizes the
middle core, the earlier center comparison identifies it with the natural
middle center. The action on the literal quotient `V_y/Z_y` then has a
central subspace of order `|k|` containing the image of the relevant
commutators. The last conjunct records the commutator formula for every
original local actor in the intersection.
-/
theorem source_central_intersection_layer_bound
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcentral : V (reducedFamily L S) x 1 ⊓
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ≤
        centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k) :
    let F := reducedFamily L S
    let y := base F (!i)
    let D := V F y 1
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
    let π := QuotientGroup.mk' ((Z F y).subgroupOf D)
    let C := ((Z F (base F i)).subgroupOf D).map π
    Nat.card C = Nat.card k ∧
      ((⁅V F x 1,D⁆).subgroupOf D).map π ≤ C ∧
      Nat.card (((⁅V F x 1,D⁆).subgroupOf D).map π) ≤ Nat.card k ∧
    ∃ ρ : Representation (ZMod 2)
      (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0)))
      (Additive (D ⧸ (Z F y).subgroupOf D)),
      (∀ a : L (if !i then 1 else 0), ∀ d : D,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk d))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) (!i) a : G₀ L S) * d *
            (originalActor (L := L) (S := S) (!i) a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h (!i)
              (originalActor (L := L) (S := S) (!i) a).property) d).mp d.property⟩) ∧
      ∀ a : L (if !i then 1 else 0),
        (originalActor (L := L) (S := S) (!i) a : G₀ L S) ∈ V F x 1 → ∀ d : D,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk d))).toMul *
          (QuotientGroup.mk d)⁻¹ ∈ C := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let D := V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have he := (source_central_intersection_eq_center h i hb hxadj hne T R hT hR e
    hz hcard hzx hzy hcommx hcommy hcentral hcross hsmall hactor).1
  have hXQ : V F x 1 ≤ Q F m :=
    V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxadj.symm
  have hDQ : D ≤ Q F m :=
    V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hadj.symm
  have hnX : Q F m ≤ normalizer (V F x 1 : Set (G₀ L S)) :=
    ((hQU m).trans ((ballKernel_one_le_edge F hxadj).trans inf_le_right)).trans
      (stabilizer_normalizes_V F x 1)
  have hnD : Q F m ≤ normalizer (D : Set (G₀ L S)) :=
    ((hQU m).trans ((ballKernel_one_le_edge F hadj).trans inf_le_right)).trans
      (stabilizer_normalizes_V F y 1)
  have hc : ⁅V F x 1,D⁆ ≤ Z F m := by
    rw [← he]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp (hDQ.trans hnX))
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (hXQ.trans hnD)
  have hZD : Z F m ≤ D :=
    le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hadj.symm)) le_rfl)
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  let π := QuotientGroup.mk' ((Z F y).subgroupOf D)
  let C := ((Z F m).subgroupOf D).map π
  let : Finite D := Finite.of_injective (inclusion (hDQ.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  have hC : Nat.card C = Nat.card k := by
    change Nat.card (((Z F m).subgroupOf D).map π) = _
    rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hZD]
    have hi := ((Z F y).subgroupOf (Z F m)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hzy).toEquiv] at hi
    change Nat.card (Z F y) * (Z F y).relIndex (Z F m) = Nat.card (Z F m) at hi
    rw [hcardy, hcard] at hi
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := k)) (by simpa [pow_two] using hi)
  have hcmap : ((⁅V F x 1,D⁆).subgroupOf D).map π ≤ C :=
    map_mono (subgroupOf_mono D hc)
  obtain ⟨ρ,hρ⟩ := source_center_layer_action h (reduced_kernel_sylow h) hb (!i) hcommy
  have hcardMap : Nat.card (((⁅V F x 1,D⁆).subgroupOf D).map π) ≤ Nat.card C :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hcmap) (inclusion_injective _)
  refine ⟨hC, hcmap, hcardMap.trans_eq hC, ⟨ρ, hρ, ?_⟩⟩
  intro a ha d
  rw [hρ]
  change π _ * (π d)⁻¹ ∈ C
  rw [← map_inv, ← map_mul]
  apply mem_map_of_mem
  change (originalActor (L := L) (S := S) (!i) a : G₀ L S) * d *
    (originalActor (L := L) (S := S) (!i) a : G₀ L S)⁻¹ * (d : G₀ L S)⁻¹ ∈ Z F m
  exact hc (commutator_mem_commutator ha d.property)

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
