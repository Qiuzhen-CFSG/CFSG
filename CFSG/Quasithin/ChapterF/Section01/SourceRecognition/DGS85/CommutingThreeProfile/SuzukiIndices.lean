module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondIndex
public import Theory.SpecificGroups.Suzuki.BorelElementary

/-!
# The two indices in the nonbinary Suzuki case of DGS 12.3(a)

The critical pair gives a nonzero image of V_x in the Suzuki quotient at y.
The earlier common-Sylow marking embeds V_x in the actual starred endpoint.
A full-edge complement fixing x is constructed using the linear action at
the middle vertex, then restricted to the starred endpoint. Its quotient
image supplements the appropriate Sylow in the full normalizer.

The elementary image of V_x lies in the Suzuki Sylow center. Thus the Sylow
centralizes this image, while the complement normalizes it. The existing
Borel-invariance theorem identifies the image with the entire Sylow center,
of order q. The literal quotient kernel gives [V_x : V_x intersect Q_y] = q.
This is the Suzuki specialization of the source's use of 5.9(b).

Combine this with the selected-neighbor calculation to obtain both printed
indices, their original-group transports, and both quotient markings. The
shared parameter, earlier common-Sylow markings, nonzero movement, and the
intersection's starred containment remain explicit. No binary conclusion,
TYPE recognition, middle-core product, or later profile is asserted.

Source: DGS85, Groups and Graphs, (5.3), (5.9)(b), (12.3)(a),
printed pp.106,110,179. Suzuki Borel invariance is proved in
Theory.SpecificGroups.Suzuki.BorelElementary.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem source_middle_edge_complement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    (hyx : base (reducedFamily L S) i ≠ x) :
    let F := reducedFamily L S
    let E := stabilizer F m ⊓ stabilizer F (base F i)
    ∃ K : Subgroup E, (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F x := by
  let F := reducedFamily L S
  let E := stabilizer F m ⊓ stabilizer F (base F i)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, ham⟩ := star_locally_transitive h i hym hadj
  have hay : a • base F i = base F i := star_le_stabilizer i ha
  have hx' : (graph F).Adj (a • x) (base F (!i)) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hxm
    change (graph F).Adj (a • x) (a • m) at hh
    rwa [ham] at hh
  have hxy' : base F i ≠ a • x := by
    intro he
    exact hyx ((MulAction.injective a) (hay.trans he))
  obtain ⟨K₀, hK₀, hodd, hKy, _, _⟩ := source_linear_edge_complement h (!i) eLin hx' hadj hxy'
  let E₀ := stabilizer F (a • x) ⊓ stabilizer F (base F (!i))
  let C := K₀.map E₀.subtype
  let D := C.map (MulAut.conj a⁻¹).toMonoidHom
  have hback (v : Vertex F) (hv : C ≤ stabilizer F (a • v)) : D ≤ stabilizer F v := by
    have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hv
    rw [← stabilizer_translate, inv_smul_smul] at hh
    exact hh
  have hDx : D ≤ stabilizer F x := hback x ((map_subtype_le K₀).trans inf_le_left)
  have hDm : D ≤ stabilizer F m := hback m (by
    rw [ham]
    exact (map_subtype_le K₀).trans inf_le_right)
  have hDy : D ≤ stabilizer F (base F i) := hback (base F i) (by rwa [hay])
  have hDE : D ≤ E := le_inf hDm hDy
  have hcard : Nat.card D = Nat.card K₀ := by
    rw [card_map_of_injective (MulAut.conj a⁻¹).injective,
      card_map_of_injective E₀.subtype_injective]
  have hcomp := source_edge_complement_transfer h hx' hym.symm K₀ hK₀ D hDE
    (hcard.symm ▸ hodd) hcard
  refine ⟨D.subgroupOf E, hcomp, ?_, ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv, hcard]
    exact hodd
  · rw [map_subgroupOf_eq_of_le hDE]
    exact hDx

/-- The first index in 12.3(a), with its image identified as the actual Suzuki Sylow center. -/
theorem source_suzuki_first_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let Vx := V F x 1
    let W := Vx ⊓ Q F (base F i)
    W.relIndex Vx = 2 ^ (2 * n + 1) ∧
      (W.map (G₀ L S).subtype).relIndex (Vx.map (G₀ L S).subtype) = 2 ^ (2 * n + 1) ∧
      ∃ T : Sylow 2 (SuzukiMatrixGroup n),
        (Vx.subgroupOf (star L S i)).map
          (((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 (star L S i)))) = omegaOneAmbient (T : Subgroup _) := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F m ⊓ stabilizer F (base F i)
  let Vx := V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hSyl := reduced_kernel_sylow h
  have hescape : ¬ Vx ≤ Q F (base F i) := by
    intro he
    have hseed : Z F a ≤ Vx :=
      le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hxa)) le_rfl)
    exact hc.2 (hseed.trans (he.trans (source_Z_Q_U (reduced_triple h) (base F i)).2))
  have hyx : base F i ≠ x := by
    intro he
    apply hescape
    change V F x 1 ≤ Q F (base F i)
    rw [← he]
    exact V_le_Q F (reduced_triple h).generate hZ hSyl hb _
  have hVm : Vx ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hxm
  have hVA : Vx ≤ A :=
    (hVm.trans (le_sup_left.trans hR.ge)).trans (map_subtype_le _)
  let : IsElementaryAbelian 2 Vx := V_elementary F (reduced_triple h).generate hZ hSyl hb x
  let : IsElementaryAbelian 2 (Vx.subgroupOf A) := IsElementaryAbelian.subgroupOf hVA
  let q := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let D := (Vx.subgroupOf A).map q
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map q
  obtain ⟨K, hK, hodd, hKx⟩ := source_middle_edge_complement h i eLin hxm hym hyx
  obtain ⟨T, hTN, hsup⟩ := source_quotient_edge_complement_supplement h i hym eSuz K hK hodd
  let C := (K.map E.subtype).subgroupOf A
  have hDN : D ≤ normalizer (T : Set (SuzukiMatrixGroup n)) := by
    apply map_le_iff_le_comap.mpr
    rw [hTN]
    intro v hv
    exact Q_le_stabilizer F m (hVm hv)
  have hDT : D ≤ T := by
    rw [← inf_eq_left.mpr hDN, (IsElementaryAbelian.isPGroup 2 D).inf_normalizer_sylow T]
    exact inf_le_right
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have hq : q.ker = pCore 2 A := by
      ext v
      change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ v ∈ pCore 2 A
      rw [map_eq_one_iff _ eSuz.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff v
    rw [hq, ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  have hne : D ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (Vx.subgroupOf A)).mp he
    rw [hk] at hh
    exact hescape (fun v hv => hh (show (⟨v, hVA hv⟩ : A) ∈ Vx.subgroupOf A from hv))
  have hDZ : D ≤ (center T).map (T : Subgroup (SuzukiMatrixGroup n)).subtype := by
    rw [← suzukiSylow_omega_eq_center hn (MulEquiv.refl _) T, ← omegaOneAmbient_eq_self D]
    exact omegaOneAmbient_mono hDT
  have hnorm : normalizer (T : Set (SuzukiMatrixGroup n)) ≤ normalizer (D : Set _) := by
    rw [← hsup]
    apply sup_le
    · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
      intro d hd t ht
      obtain ⟨d', hd', he⟩ := hDZ hd
      rw [← he]
      exact congrArg Subtype.val ((mem_center_iff.mp hd') ⟨t, ht⟩)
    · have hCV : C ≤ normalizer (Vx.subgroupOf A : Set A) := by
        intro c hc
        exact le_normalizer_comap A.subtype
          (stabilizer_normalizes_V F x 1 (hKx hc))
      exact (map_mono hCV).trans ((Vx.subgroupOf A).le_normalizer_map q)
  have him : D = omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n)) := by
    rw [suzukiSylow_omega_eq_center hn (MulEquiv.refl _) T]
    exact suzuki_elementary_eq_center_of_borel_normalized hn (MulEquiv.refl _) T D hDT hne hnorm
  have hi : (Vx ⊓ Q F (base F i)).relIndex Vx = 2 ^ (2 * n + 1) := by
    rw [inf_relIndex_left, ← relIndex_subgroupOf hVA, ← hk, relIndex_ker]
    change Nat.card D = _
    rw [him]
    exact suzukiSylow_omega_card hn (MulEquiv.refl _) T
  refine ⟨hi, ?_, T, him⟩
  rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hi

/-- Both printed indices in the nonbinary Suzuki case, retaining the original maps
and both local quotient markings. -/
theorem source_suzuki_intersection_indices
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
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
      Z (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F (base F i)
    let D := V F x 1 ⊓ Q F (base F (!i))
    W.relIndex (V F x 1) = 2 ^ (2 * n + 1) ∧ D ≤ W ∧ D.relIndex W = 2 ^ (2 * n + 1) ∧
      (W.map (G₀ L S).subtype).relIndex ((V F x 1).map (G₀ L S).subtype) =
        2 ^ (2 * n + 1) ∧
      (D.map (G₀ L S).subtype).relIndex (W.map (G₀ L S).subtype) = 2 ^ (2 * n + 1) ∧
      (∃ U : Sylow 2 (SuzukiMatrixGroup n),
        ((V F x 1).subgroupOf (star L S i)).map
          (((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 (star L S i)))) = omegaOneAmbient (U : Subgroup _)) ∧
      ∃ P : Sylow 2 SL(2,k), ∃ f : W →* Multiplicative k,
        Function.Surjective f ∧ f.ker = D.subgroupOf W ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P) (f w) : SL(2,k)) =
          eLin ((originalQuotient h (!i)).symm
            (QuotientGroup.mk' (pCore 2 (star L S (!i))) ⟨w, hW w.property⟩)) := by
  obtain ⟨hi, hoi, hSuz⟩ := source_suzuki_first_index h i hb hc hxa hxm hym hn eSuz eLin R hR
  obtain ⟨hD, hj, hoj, hLin⟩ := source_suzuki_second_index
    h i hb hxm hym hmz hn hq eSuz T R hT hR eLin hW hmove
  exact ⟨hi, hD, hj, hoi, hoj, hSuz, hLin⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
