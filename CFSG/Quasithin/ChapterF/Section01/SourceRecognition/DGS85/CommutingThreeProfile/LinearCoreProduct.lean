module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearNeighborOrbits
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NormalCoreProduct
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearIntersectionIndex

/-!
# The middle-core product for linear neighboring quotients

Let x and y be distinct neighbors of the linear middle vertex m, with an
actual critical pair (a,y) passing through x. The critical center escapes
Q_y, so V_x has a nonzero image in the marked quotient at y. Construct a
full-edge odd complement fixing x by the linear local action at m. Its
restriction supplements the Sylow normalizer in the original/starred
quotient at y. When that quotient is SL₂, normalizer invariance makes the
image of V_x the whole Sylow, including over the field of order two.

The literal kernel then gives both [V_x : V_x ∩ Q_y] = |k| and
Q_m = V_x (Q_y ∩ Q_m). Since V_x lies in Q_x ∩ Q_m, this proves the
middle-core product used on DGS p.180 in this branch. The quotient marking
is retained, and LinearCoreApplication applies the product to the actual
original-parabolic commutator dichotomy.

The common-Sylow marking and critical geometry are earlier Chapter 8
inputs. This does not prove the Suzuki product, exclude the linear row,
or establish the later (12.9)/(13.1) alternatives. The private supplement
lemma is intentionally reused from LinearIntersectionIndex within this
same theorem family; no private name enters the public statement.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (5.2), (12.1)(c), (12.3), printed pp.105,178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem core_product_of_quotient_image
    {M : Type*} [Group M] (A Q Y W : Subgroup G) (q : A →* M)
    (hQA : Q ≤ A) (hWQ : W ≤ Q) (hk : q.ker = Y.subgroupOf A)
    (him : (Q.subgroupOf A).map q ≤ (W.subgroupOf A).map q) :
    Q = W ⊔ (Y ⊓ Q) := by
  apply le_antisymm ?_ (sup_le hWQ inf_le_right)
  intro u hu
  obtain ⟨v,hv,hvu⟩ := him (mem_map_of_mem q (show (⟨u,hQA hu⟩ : A) ∈ Q.subgroupOf A from hu))
  have hker : (⟨u,hQA hu⟩ : A) * v⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hvu,mul_inv_cancel]
  have hwY : u * (v : G)⁻¹ ∈ Y := by
    change (⟨u,hQA hu⟩ : A) * v⁻¹ ∈ Y.subgroupOf A
    rwa [← hk]
  have hwQ := Q.mul_mem hu (Q.inv_mem (hWQ hv))
  have hw := (W ⊔ (Y ⊓ Q)).mul_mem
    ((show Y ⊓ Q ≤ W ⊔ (Y ⊓ Q) from le_sup_right) ⟨hwY,hwQ⟩)
    ((show W ≤ W ⊔ (Y ⊓ Q) from le_sup_left) hv)
  change u * (v : G)⁻¹ * (v : G) ∈ W ⊔ (Y ⊓ Q) at hw
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hw

/-- The full linear Sylow image gives the first index and both literal middle-core products. -/
theorem source_linear_first_index_and_product
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eMid : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,l))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    let Vx := V F x 1
    (Vx ⊓ Q F y).relIndex Vx = Nat.card k ∧
      Q F m = Vx ⊔ (Q F y ⊓ Q F m) ∧
      Q F m = (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) ∧
      ∃ T : Sylow 2 SL(2,k),
        (Vx.subgroupOf (star L S i)).map
          (((originalQuotient h i).symm.trans e).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 (star L S i)))) = (T : Subgroup SL(2,k)) := by
  let F := reducedFamily L S
  let A := star L S i
  let m := base F (!i)
  let y := base F i
  let E := stabilizer F m ⊓ stabilizer F y
  let Vx := V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hSyl := reduced_kernel_sylow h
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hescape : ¬ Vx ≤ Q F y := by
    intro he
    have hseed : Z F a ≤ Vx :=
      le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hxa)) le_rfl)
    exact hc.2 (hseed.trans (he.trans (source_Z_Q_U (reduced_triple h) y).2))
  have hxy : x ≠ y := by
    intro he
    apply hescape
    change V F x 1 ≤ Q F y
    rw [he]
    exact V_le_Q F (reduced_triple h).generate hZ hSyl hb _
  have hVm : Vx ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hxm
  have hVx : Vx ≤ Q F x := V_le_Q F (reduced_triple h).generate hZ hSyl hb x
  have hQA : Q F m ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hVA : Vx ≤ A := hVm.trans hQA
  let : IsElementaryAbelian 2 Vx := V_elementary F (reduced_triple h).generate hZ hSyl hb x
  let : IsElementaryAbelian 2 (Vx.subgroupOf A) := IsElementaryAbelian.subgroupOf hVA
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let D := (Vx.subgroupOf A).map q
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map q
  have hcomp : ∃ K : Subgroup E, (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F x := by
    change ∃ K : Subgroup (stabilizer F m ⊓ stabilizer F y : Subgroup (G₀ L S)),
      (pCore 2 (stabilizer F m ⊓ stabilizer F y : Subgroup (G₀ L S))).IsComplement' K ∧
        Odd (Nat.card K) ∧ (K.map (stabilizer F m ⊓ stabilizer F y).subtype) ≤ stabilizer F x
    rw [inf_comm (stabilizer F m) (stabilizer F y)]
    obtain ⟨K,hK,ho,hfix,_,_⟩ := source_linear_edge_complement h (!i) eMid hadj hxm hxy
    exact ⟨K,hK,ho,hfix⟩
  obtain ⟨K,hK,hodd,hKx⟩ := hcomp
  obtain ⟨T,hTN,hsup⟩ := source_quotient_edge_complement_supplement h i hadj e K hK hodd
  let C := (K.map E.subtype).subgroupOf A
  have hDN : D ≤ normalizer (T : Set SL(2,k)) := by
    apply map_le_iff_le_comap.mpr
    rw [hTN]
    intro v hv
    exact Q_le_stabilizer F m (hVm hv)
  have hDT : D ≤ T := by
    rw [← inf_eq_left.mpr hDN, (IsElementaryAbelian.isPGroup 2 D).inf_normalizer_sylow T]
    exact inf_le_right
  have hk : q.ker = (Q F y).subgroupOf A := by
    have hq : q.ker = pCore 2 A := by
      ext v
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ v ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff v
    rw [hq, ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  have hne : D ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (Vx.subgroupOf A)).mp he
    rw [hk] at hh
    exact hescape (fun v hv => hh (show (⟨v,hVA hv⟩ : A) ∈ Vx.subgroupOf A from hv))
  have hn : normalizer (T : Set SL(2,k)) ≤ normalizer (D : Set SL(2,k)) := by
    apply image_normalized_of_sylow_supplement q T (Vx.subgroupOf A) C hDT ?_ hsup
    intro c hc
    exact le_normalizer_comap A.subtype (stabilizer_normalizes_V F x 1 (hKx hc))
  have him : D = (T : Subgroup SL(2,k)) :=
    Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant T D hDT hne hn
  have hQM : (Q F m).subgroupOf A ≤ (R : Subgroup A) := by
    intro u hu
    have hm : (u : G₀ L S) ∈ (R : Subgroup A).map A.subtype :=
      hR.symm ▸ (show (u : G₀ L S) ∈ Q F m ⊔ Q F y from
        (show Q F m ≤ Q F m ⊔ Q F y from le_sup_left) hu)
    obtain ⟨v,hv,he⟩ := hm
    exact (Subtype.ext he : v = u) ▸ hv
  have hpQ : IsPGroup 2 ((Q F m).subgroupOf A) := R.isPGroup'.to_le hQM
  have hQN : ((Q F m).subgroupOf A).map q ≤ normalizer (T : Set SL(2,k)) := by
    apply map_le_iff_le_comap.mpr
    rw [hTN]
    exact fun u hu => Q_le_stabilizer F m hu
  have hQT : ((Q F m).subgroupOf A).map q ≤ T := by
    rw [← inf_eq_left.mpr hQN, (hpQ.map q).inf_normalizer_sylow T]
    exact inf_le_right
  have hprod : Q F m = Vx ⊔ (Q F y ⊓ Q F m) := by
    exact core_product_of_quotient_image A (Q F m) (Q F y) Vx q hQA hVm hk (hQT.trans him.ge)
  refine ⟨?_,hprod,?_,T,him⟩
  · rw [inf_relIndex_left, ← relIndex_subgroupOf hVA, ← hk, relIndex_ker]
    change Nat.card D = _
    rw [him]
    exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.toEquiv
  · exact le_antisymm (hprod.le.trans
      (sup_le ((le_inf hVx hVm).trans le_sup_left) le_sup_right))
      (sup_le inf_le_right inf_le_right)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
