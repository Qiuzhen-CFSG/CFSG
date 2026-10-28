module
public import Theory.SpecificGroups.Suzuki.ElementarySylowIntersection
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionIndexSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow

/-!
# The literal Suzuki denominator in DGS 12.3(a)

At the Suzuki endpoint y, the distinct neighboring core products generate
the actual starred endpoint. The elementary subgroup V_x intersect Q_z
lies in both Sylows: V_x lies in Q_m since x is adjacent to m and b > 2.
The Suzuki omega argument puts this intersection in Q_y. Thus the triple
intersection in the linear index calculation is exactly the printed
denominator V_x intersect Q_z. The final clause transports the containment
to the original parabolic two-core by the actual reduction inclusion.

With the previously proved linear index and an explicitly marked complement,
this gives the second printed index with its shared Suzuki/linear parameter.
The quotient coordinates retain the original linear representative formula;
their kernel is the printed denominator, not an unspecified isomorphic group.

Source: DGS, Groups and Graphs (1985), 12.1(b,c), 12.3(a), pp.178--179.
The Chapter 8 common-Sylow inputs and the actual Suzuki isomorphism remain
explicit. This result covers n > 0; it does not settle the dihedral case,
construct the complement's linear image, or assert the full 12.3 or 12.9.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Reduction
open Theory.GroupTheory.AmalgamLocalCores
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The Suzuki marking and the common-Sylow inputs give the printed two-term denominator. -/
theorem source_suzuki_intersection_denominator (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    (hmz : m ≠ base (reducedFamily L S) (!i))
    {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    V F x 1 ⊓ Q F (base F (!i)) ≤ Q F (base F i) ∧
      (V F x 1 ⊓ Q F (base F i)) ⊓ Q F (base F (!i)) =
        V F x 1 ⊓ Q F (base F (!i)) ∧
      (V F x 1 ⊓ Q F (base F (!i))).map (G₀ L S).subtype ≤
        (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
  let F := reducedFamily L S
  let A := star L S i
  let W := V F x 1 ⊓ Q F (base F (!i))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (L := L) (S := S) i))
    (inclusion_injective _)
  have hWT : W ≤ (T : Subgroup A).map A.subtype := by
    rw [hT]
    exact inf_le_right.trans le_sup_left
  have hWR : W ≤ (R : Subgroup A).map A.subtype := by
    rw [hR]
    apply le_trans _ le_sup_left
    exact inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm)
  have hWA : W ≤ A := hWT.trans (map_subtype_le _)
  have hTfix : (T : Subgroup A).map A.subtype ≤ stabilizer F (base F (!i)) := by
    rw [hT]
    apply sup_le (Q_le_stabilizer F _) _
    exact ((source_Z_Q_U (reduced_triple h) (base F i)).2.trans
      (ballKernel_one_le_edge F (show (graph F).Adj (base F i) (base F (!i)) from
        ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F _ _⟩))).trans inf_le_right
  have hRfix : (R : Subgroup A).map A.subtype ≤ stabilizer F m := by
    rw [hR]
    exact sup_le (Q_le_stabilizer F _) (((source_Z_Q_U (reduced_triple h) (base F i)).2.trans
      (ballKernel_one_le_edge F hym)).trans inf_le_right)
  have hgen := star_sylow_pair_generates h i hym hmz T R hTfix hRfix
  have hgen' : (T : Subgroup A) ⊔ R = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, range_subtype]
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ V F x 1 from inf_le_left)
  let : IsElementaryAbelian 2 (W.subgroupOf A) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hWA).toMonoidHom
      (subgroupOfEquivOfLe hWA).injective
  have hcore : W ≤ Q F (base F i) := by
    have hh := BenderSuzuki.MatrixGroups.elementary_le_core_of_generating_suzuki_sylows
      hn ((originalQuotient h i).symm.trans e) T R hgen' (W.subgroupOf A)
      (by simpa only [subgroupOf, comap_map_eq_self_of_injective A.subtype_injective]
        using comap_mono (f := A.subtype) hWT)
      (by simpa only [subgroupOf, comap_map_eq_self_of_injective A.subtype_injective]
        using comap_mono (f := A.subtype) hWR)
    have hm := map_mono (f := A.subtype) hh
    rw [map_subgroupOf_eq_of_le hWA] at hm
    exact hm.trans (star_core h i).le
  refine ⟨hcore, ?_, ?_⟩
  · exact le_antisymm (fun a ha => ⟨ha.1.1, ha.2⟩)
      (fun a ha => ⟨⟨ha.1, hcore ha⟩, ha.2⟩)
  · have hm := map_mono (f := (G₀ L S).subtype) hcore
    have he : (Q F (base F i)).map (G₀ L S).subtype =
        (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
      rw [← star_core h i, ← pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
      change (((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map
        (G₀ L S).subtype).pCoreIn 2 = _
      rw [map_subgroupOf_eq_of_le (star_le_completion _)]
      exact h.starredParabolic_same_core _
    exact hm.trans he.le

/-- The second index of 12.3(a), with the literal denominator and original quotient marking.
The complement image and the earlier common-Sylow and parameter inputs remain explicit. -/
theorem source_suzuki_second_intersection_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    (hmz : m ≠ base (reducedFamily L S) (!i))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2 ^ (2 * n + 1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hW : V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i) ≤
      star L S (!i))
    (hmove : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      Z (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≠ ⊥)
    (P : Sylow 2 SL(2,k)) (K : Subgroup (star L S (!i)))
    (hP : ((V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S)
        (base (reducedFamily L S) i)).subgroupOf (star L S (!i))).map
          (((originalQuotient h (!i)).symm.trans eLin).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 (star L S (!i))))) ≤ P)
    (hKx : K.map (star L S (!i)).subtype ≤ stabilizer (reducedFamily L S) x)
    (hKy : K.map (star L S (!i)).subtype ≤
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hcover : (P : Subgroup SL(2,k)) ⊔ K.map
        (((originalQuotient h (!i)).symm.trans eLin).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 (star L S (!i))))) = normalizer (P : Set SL(2,k))) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F (base F i)
    let D := V F x 1 ⊓ Q F (base F (!i))
    D ≤ W ∧ D.relIndex W = 2 ^ (2 * n + 1) ∧
      (D.map (G₀ L S).subtype).relIndex (W.map (G₀ L S).subtype) = 2 ^ (2 * n + 1) ∧
      ∃ f : W →* Multiplicative k, Function.Surjective f ∧ f.ker = D.subgroupOf W ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P) (f w) : SL(2,k)) =
          eLin ((originalQuotient h (!i)).symm
            (QuotientGroup.mk' (pCore 2 (star L S (!i))) ⟨w, hW w.property⟩)) := by
  let F := reducedFamily L S
  let W := V F x 1 ⊓ Q F (base F i)
  let D := V F x 1 ⊓ Q F (base F (!i))
  obtain ⟨hD, hden, _⟩ := source_suzuki_intersection_denominator
    h i hb hxm hym hmz hn eSuz T R hT hR
  obtain ⟨hindex, _, f, hf, hker, hmark⟩ := source_linear_intersection_index
    h (!i) eLin hW hmove P K hP hKx hKy hcover
  have hi : D.relIndex W = 2 ^ (2 * n + 1) := by
    change (V F x 1 ⊓ Q F (base F (!i))).relIndex W = _
    rw [← hden, inf_relIndex_left, hindex, hq]
  refine ⟨le_inf inf_le_left hD, hi, ?_, f, hf, ?_, hmark⟩
  · rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hi
  · rw [hker]
    ext w
    exact ⟨fun hw => ⟨w.property.1, hw⟩, fun hw => hw.2⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
