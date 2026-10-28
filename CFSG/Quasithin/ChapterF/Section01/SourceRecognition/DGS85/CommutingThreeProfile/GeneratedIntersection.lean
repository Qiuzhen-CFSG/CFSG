module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow

/-!
# The generated middle intersection on the reduced F1.11 graph

The actual common-Sylow markings and the distinct neighboring vertices now
prove the three-core generation premise of `source_intersection_third_kernel`.
The shared `reduced_kernel_sylow` theorem also discharges 6.2(d) from F1.11.
Thus neither generation nor kernel-Sylow containment is an extra assumption
in this application. The image of the intersection is normal in the original
starred endpoint and lies in the original parabolic core, with the same
subtype inclusion and the original S retained.

The common-Sylow markings, their placement in the starred linear endpoint,
b=3, center centralization and the Chapter 8 commutator bounds remain the
explicit earlier-source inputs. In particular, the starred endpoint is not
silently substituted for the larger L_delta of DGS Chapter 6.

Source: DGS85 (6.1), (6.2)(d), (8.1), (8.7), (12.1) and (12.3)(b),
printed pp.118--119, 132--140 and 178--180. The product/index and central-case
arguments in (12.3)(a,c), and the remaining (12.9) profile, are not asserted.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Reduction
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal middle intersection, with generation and 6.2(d) discharged. -/
theorem source_intersection_of_common_sylows (h : HypothesisF11 L S)
    (hb : b (reducedFamily L S) = 3) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hT : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTS : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hRS : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hcx : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcy : Z (reducedFamily L S) y ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hx : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
        Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hycomm : ⁅V (reducedFamily L S) y 1, Q (reducedFamily L S) y⁆ ≤ Z (reducedFamily L S) y) :
    let F := reducedFamily L S
    let H := V F (base F (!i)) 1 ⊓ V F y 1
    (H.subgroupOf (star L S i)).Normal ∧
      ((H.map (G₀ L S).subtype).subgroupOf
        (starredParabolic L S (if i then 1 else 0))).Normal ∧
      IsElementaryAbelian 2 H ∧ Z F (base F i) ≤ H ∧ H ≠ ⊥ ∧
      H ≤ ballKernel F (base F i) 3 ∧
      H.map (G₀ L S).subtype ≤ (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
  have hadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i)
      (base (reducedFamily L S) (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,
      Subgroup.CosetGeometry.incident_base (reducedFamily L S) i (!i)⟩
  exact source_intersection_third_kernel h (reduced_kernel_sylow h) hb i hadj.symm hy.symm
    T R hT hR hcx hcy hx hycomm
    (star_three_core_generation_of_full_sylows h i hy hne T R hT hR hTS hRS)

/-- The exact p.180 alternative for the literal reduced intersection. The
remaining core-product premise is a Chapter 12 obligation; minimality is
supplied by the earlier natural SL₂ center. The central alternative is retained. -/
theorem source_intersection_center_alternative (h : HypothesisF11 L S) (i : Bool)
    {y : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) y)
    (hne : y ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)))
    (hT : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype =
        Q (reducedFamily L S) y ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hTS : (T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hRS : (R : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))).map
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ star L S i)
    (hcx : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hcy : Z (reducedFamily L S) y ≤
      centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)))
    (hx : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
        Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hycomm : ⁅V (reducedFamily L S) y 1, Q (reducedFamily L S) y⁆ ≤ Z (reducedFamily L S) y)
    (hprod : Q (reducedFamily L S) (base (reducedFamily L S) i) =
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i)) ⊔
      (Q (reducedFamily L S) y ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let H := V F (base F (!i)) 1 ⊓ V F y 1
    ⁅H, Q F (base F i)⁆ = Z F (base F i) ∨ H ≤ centralizer (Q F (base F i) : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ : ∀ v : Vertex F, Z F v ≤ omegaCenterIn (Q F v) :=
    fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hzA : Z F (base F i) ≤ star L S i := by
    exact ((hZ _).trans (map_subtype_le _)).trans
      ((star_core h i).ge.trans (map_subtype_le _))
  have hnZ : star L S i ≤ normalizer (Z F (base F i) : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F _)).mp (Z_normal F _))
  let : ((Z F (base F i)).subgroupOf (star L S i)).Normal :=
    normal_subgroupOf_of_le_normalizer hnZ
  let : IsMinimalNormal ((Z F (base F i)).subgroupOf (star L S i)) :=
    ⟨fun N _ hN => hmin N inferInstance hN⟩
  have hnH := intersection_normalized F
    (fun v => (source_Z_Q_U (reduced_triple h) v).2)
    (show (graph F).Adj (base F (!i)) (base F i) from
      ⟨by change (!i) ≠ i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F (!i) i⟩)
    hy.symm hx hycomm
    (center_le_adjacent_center F hZ T hT hcx)
    (center_le_adjacent_center F hZ R hR hcy)
  have hgen := star_three_core_generation_of_full_sylows h i hy hne T R hT hR hTS hRS
  have hn : star L S i ≤ normalizer (V F (base F (!i)) 1 ⊓ V F y 1 : Set (G₀ L S)) := by
    rw [hgen]
    exact hnH
  exact intersection_commutator_dichotomy F (star L S i) (star_le_stabilizer i) hzA hn
    (intersection_commutator_le_center F hx hycomm
      (center_le_adjacent_center F hZ T hT hcx)
      (center_le_adjacent_center F hZ R hR hcy) hprod)

/-- The noncentral intersection branch gives the full neighboring center-span
commutator. Both the reduced and original equations use literal inclusions.
The local group A may be larger than the starred endpoint. -/
theorem source_span_commutator_of_intersection (h : HypothesisF11 L S)
    {x y m : Vertex (reducedFamily L S)}
    (A : Subgroup (G₀ L S)) (hA : A ≤ stabilizer (reducedFamily L S) y)
    (hadj : (graph (reducedFamily L S)).Adj y m)
    (htrans : ∀ z, (graph (reducedFamily L S)).Adj y z → ∃ g ∈ A, g • m = z)
    (hQy : Q (reducedFamily L S) y ≤ A) (hQm : Q (reducedFamily L S) m ≤ A)
    (hy : ⁅V (reducedFamily L S) y 1, Q (reducedFamily L S) y⁆ = Z (reducedFamily L S) y)
    (hc : ⁅V (reducedFamily L S) x 1 ⊓ V (reducedFamily L S) y 1,
      Q (reducedFamily L S) m⁆ = Z (reducedFamily L S) m) :
    V (reducedFamily L S) y 1 = ⁅V (reducedFamily L S) y 1, A⁆ ∧
      (V (reducedFamily L S) y 1).map (G₀ L S).subtype =
        ⁅(V (reducedFamily L S) y 1).map (G₀ L S).subtype, A.map (G₀ L S).subtype⁆ := by
  let : ∀ j, Finite (reducedFamily L S j) := finite_endpoints (reduced_triple h)
  have he := V_eq_commutator_of_intersection (reducedFamily L S) A hA hadj htrans hQy hQm hy hc
  refine ⟨he, ?_⟩
  have hm := congrArg (Subgroup.map (G₀ L S).subtype) he
  rwa [map_commutator] at hm

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
