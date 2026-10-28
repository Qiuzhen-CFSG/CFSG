module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Automizer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Product
public import Theory.GroupTheory.ComponentTwoCore.Product
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The genuine paired odd-prime PSL₂ witness

The source supplies the two actual commuting components and their product
coordinates. Normality of the original elementary V in T makes its actions
on both components inner and of order at most two. The residual has trivial
centralizer, so V lies in that product. Faithful component actions identify
the coordinate projections with the bounded automizer images. A nontrivial
projection therefore has order two; the odd-rotation construction produces
the required dihedral pair containing all original V.

No factor-preservation, inner placement, projection bound, or witness is a
premise. The original containment V ≤ O₂(M) is used by the final rotation
construction. Source: Aschbacher–Smith E.2.7, printed p.219.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

theorem source_pair
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (e : K ≃* PSL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (hV : V ≠ ⊥) :
    Nonempty (DihedralWitness T (ChapterB.minimalParabolicMax T hP) V) := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  obtain ⟨t,hne,hDsimple,hD,hR,⟨d,hd⟩,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hC hgen hnot
  let D := K.map (MulAut.conj (t:H)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let : IsQuasisimple D := hD.2
  have hDC : D.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hD.1
  let eD : D ≃* PSL(2,F) := ((MulAut.conj (t:H)).subgroupMap K).symm.trans e
  have hDT : D ⊔ (T : Subgroup H) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:H)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:H)).surjective] at he
    have ht : (T : Subgroup H).map (MulAut.conj (t:H)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup H).le_normalizer t.property)
    rwa [ht] at he
  have hKdata := source_component_placement ho hF hp hH T hP hK hC hrad hgen e V hVT hVN
  have hDdata := source_component_placement ho hF hp hH T hP hD hDC hrad hDT eD V hVT hVN
  have hc : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne hD hne.symm
  have hKD : K ≤ centralizer (D : Set H) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hDK : D ≤ centralizer (K : Set H) := le_centralizer_iff.mp hKD
  have hnormal : (K ⊔ D).Normal := by rw [← hR]; infer_instance
  let := hnormal
  have hRT : (K ⊔ D : Subgroup H) ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le_sup le_sup_left le_rfl)
  have hZ : center (K ⊔ D : Subgroup H) = ⊥ :=
    center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hnormal.isSubnormal
  have hCR : centralizer ((K ⊔ D : Subgroup H) : Set H) = ⊥ := by
    have hcT := centralizer_le_sylow_of_centerless_supplement (K ⊔ D) T hRT hZ
    have hcO : centralizer ((K ⊔ D : Subgroup H) : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hcT⟩
    exact le_bot_iff.mp (hcO.trans ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le))
  have hVR : V ≤ K ⊔ D := (le_inf hKdata.2.1 hDdata.2.1).trans
    (inf_inner_centralizer_supplements_le_sup K D hc hCR)
  let f : K × D →* H := (K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom
  have hf : Function.Injective f := (K ⊔ D : Subgroup H).subtype_injective.comp d.injective
  have hmul : ∀ k a, f (k,a) = (k:H)*(a:H) := hd
  have hfr : f.range = K ⊔ D := by
    change ((K ⊔ D : Subgroup H).subtype.comp d.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr d.surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  let W := V.comap f
  have him : W.map f = V := by rw [map_comap_eq,hfr]; exact inf_eq_right.mpr hVR
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    ((f.comp W.subtype).codRestrict V (fun x => x.property))
    (by
      intro x y he
      apply Subtype.ext
      exact hf (show f (x : K × D) = f (y : K × D) from congrArg (fun v : V => (v:H)) he))
  have hW : W ≠ ⊥ := by intro he; apply hV; rw [← him,he,Subgroup.map_bot]
  have hfirst : Nat.card (W.map (MonoidHom.fst K D)) ≤ 2 := by
    have hh := congrArg (fun A : Subgroup (NormalizerAction.Star K) => Nat.card A)
      (NormalizerAction.componentMap_projection_eq K D V hDK f hmul him)
    rw [card_map_of_injective (NormalizerAction.componentMap_injective_of_center_eq_bot K
      (center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hK.1))] at hh
    exact hh.le.trans hKdata.2.2
  have hsecond : Nat.card (W.map (MonoidHom.snd K D)) ≤ 2 := by
    let z : D × K ≃* K × D := MulEquiv.prodComm
    let f' := f.comp z.toMonoidHom
    have hmul' : ∀ a k, f' (a,k) = (a:H)*(k:H) := by
      intro a k
      change f (k,a) = _
      rw [hmul]
      exact (hKD k.property a a.property).symm
    have him' : (V.comap f').map f' = V := by
      rw [show f' = f.comp z.toMonoidHom from rfl,← comap_comap,← map_map,
        map_comap_eq_self_of_surjective z.surjective,him]
    have hproj : (V.comap f').map (MonoidHom.fst D K) = W.map (MonoidHom.snd K D) := by
      have hz : (V.comap f').map z.toMonoidHom = W := by
        change (W.comap z.toMonoidHom).map z.toMonoidHom = W
        exact map_comap_eq_self_of_surjective z.surjective W
      rw [← hz,map_map]
      rfl
    have hh := congrArg (fun A : Subgroup (NormalizerAction.Star D) => Nat.card A)
      (NormalizerAction.componentMap_projection_eq D K V hKD f' hmul' him')
    rw [card_map_of_injective (NormalizerAction.componentMap_injective_of_center_eq_bot D
      (center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hD.1)),hproj] at hh
    exact hh.le.trans hDdata.2.2
  have hKcore : pCore 2 K = ⊥ := SimpleSocle.pCore_eq_bot
    (solvableRadical_eq_bot_of_isSubnormal hrad hK.1) 2
  have hDcore : pCore 2 D = ⊥ := SimpleSocle.pCore_eq_bot
    (solvableRadical_eq_bot_of_isSubnormal hrad hD.1) 2
  have hw := exists_dihedral_of_projection_cards W hW hfirst hsecond hKcore hDcore T
    (ChapterB.minimalParabolicMax T hP) f hf (by rwa [him]) (by rwa [him])
  rwa [him] at hw

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
