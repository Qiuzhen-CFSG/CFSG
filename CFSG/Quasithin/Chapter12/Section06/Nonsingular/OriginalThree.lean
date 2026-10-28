module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalExtension
public import Theory.SpecificGroups.SymmetricEight.TranspositionThree
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The original three-letter overgroup and characteristic obstruction

The point centralizer in LT has index28. In the actual S8 quotient its
image normalizes the transposition R_v/Q, so its order identifies it with
the full transposition centralizer. Lift the three-letter S3 containing
that transposition. Its preimage X has O2(X)=Q, has R_v as a Sylow two-subgroup,
and generates LT together with C_LT(v).

If a nontrivial characteristic subgroup of R_v were normalized by X, it
would also be normalized by C_LT(v), hence by LT. Source uniqueness would
then put N_G(R_v) in M, contradicting the proved normalizer escape. The
preferred-point application supplies all these data when the original
C_V(L) is nontrivial, retaining V, the point and all quotient projections.
The block, splitting, remaining quasisimple and fixed-space arguments
remain with this owner; neither12.6.2 nor12.6.23 is asserted. Earlier
invariance/TI retain qt-d-1222-source and final discharge qt-d-12634-source.
Source: Aschbacher--Smith12.6.18, printed p.827, combined manuscript of
1 March2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual LT point orbit still has length28. -/
theorem OrthogonalMarking.nonsingular_join_centralizer_index
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v) :
    (LT T L ⊓ Gv (v : G)).relIndex (LT T L) = 28 := by
  rw [inf_relIndex_left,Gv,point_centralizer_index_of_orbit_control L (LT T L)
    le_sup_left (v : G) (fun n => D.normalizer_orbit_control chosen n
      ((sup_le L.le_normalizer chosen.sylow_normalizes_component) n.property)
      ((sup_le chosen.normalizes hTV) n.property) v)]
  simpa only [CLv,inf_relIndex_left,Gv] using D.nonsingular_centralizer_index chosen v hv

/-- The original point centralizer maps onto the full transposition centralizer. -/
theorem SourceHypothesis.nonsingular_original_centralizer_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v)
    (e : Star (LT T L) ≃* Equiv.Perm (Fin 8))
    (t : Equiv.Perm (Fin 8)) (ht : t.IsSwap)
    (hr : (starImage (LT T L) (Rv T L (v : G))).map e.toMonoidHom = zpowers t) :
    (starImage (LT T L) (LT T L ⊓ Gv (v : G))).map e.toMonoidHom =
      centralizer ({t} : Set (Equiv.Perm (Fin 8))) := by
  let J := LT T L
  let C := J ⊓ Gv (v : G)
  let C₀ := C.subgroupOf J
  let R₀ := (Rv T L (v : G)).subgroupOf J
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  have hr' : R₀.map f = zpowers t := by
    simpa only [starImage,map_map] using hr
  have hn : C₀ ≤ normalizer (R₀ : Set J) := by
    rw [←subgroupOf_normalizer_eq hRJ]
    exact fun x hx => (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))) hx
  have hnmap := (map_mono (f := f) hn).trans (R₀.le_normalizer_map f)
  rw [hr'] at hnmap
  have hc : C₀.map f ≤ centralizer ({t} : Set (Equiv.Perm (Fin 8))) :=
    hnmap.trans ((normalizer_le_centralizer_of_card_two _ (by rw [Nat.card_zpowers,ht.orderOf])).trans
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers t))))
  have hk : f.ker ≤ C₀ := by
    intro x hx
    have he : QuotientGroup.mk' (pCore 2 J) x = 1 := e.injective (hx.trans e.map_one.symm)
    have hm : (x : G) ∈ Q T L := mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff x).mp he)
    exact ⟨x.property,(Q_le_Tv H.chosen v hm).2⟩
  have hi : (C₀.map f).index = 28 := by
    rw [index_map,sup_eq_left.mpr hk,MonoidHom.range_eq_top.mpr hf,index_top,mul_one]
    exact D.nonsingular_join_centralizer_index H.chosen hTV v hv
  have hcard : Nat.card (C₀.map f) = 1440 := by
    have hh := (C₀.map f).card_mul_index
    rw [hi] at hh
    have h8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    rw [h8] at hh
    omega
  have htcard : Nat.card (centralizer ({t} : Set (Equiv.Perm (Fin 8)))) = 1440 := by
    rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp ht]
    norm_num [Nat.factorial]
  change ((C.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))).map e.toMonoidHom = _
  rw [map_map]
  exact eq_of_le_of_card_ge hc (by rw [hcard,htcard])


/-- Construct the actual rank-one overgroup used in source12.6.18. -/
theorem SourceHypothesis.nonsingular_original_three_overgroup
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v) (hlt : Q T L < Rv T L (v : G)) :
    ∃ X : Subgroup G, X ≤ LT T L ∧ Rv T L (v : G) ≤ X ∧
      X.pCoreIn 2 = Q T L ∧ Nonempty (Star X ≃* Equiv.Perm (Fin 3)) ∧
      Chapter1.IsSylowIn 2 (Rv T L (v : G)) X ∧
      X ⊔ (LT T L ⊓ Gv (v : G)) = LT T L := by
  obtain ⟨e,_,t,ht,hr⟩ := H.nonsingular_original_symmetric_quotient D v hv hlt
  obtain ⟨B,⟨b⟩,hRB,hgen⟩ :=
    Theory.SpecificGroups.SymmetricEight.TranspositionThree.exists_three_overgroup t ht
  let J := LT T L
  let C := J ⊓ Gv (v : G)
  let R₀ := (Rv T L (v : G)).subgroupOf J
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  let W := B.comap f
  let X := W.map J.subtype
  let a : W ≃* X := W.equivMapOfInjective J.subtype J.subtype_injective
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  have hr' : R₀.map f = zpowers t := by simpa only [starImage,map_map] using hr
  have hc : (C.subgroupOf J).map f = centralizer ({t} : Set (Equiv.Perm (Fin 8))) := by
    simpa only [starImage,map_map] using H.nonsingular_original_centralizer_image D hTV v hv e t ht hr
  have hk : f.ker = pCore 2 J := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 J) x) = 1 ↔ x ∈ pCore 2 J
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hkR : f.ker ≤ R₀ := by
    rw [hk]
    exact fun x hx => hlt.le (mem_map_of_mem J.subtype hx)
  have hW : W.map f = B := map_comap_eq_self_of_surjective hf B
  have hRW : R₀ ≤ W := (le_comap_map f R₀).trans (comap_mono (hr'.trans_le hRB))
  have hRX : Rv T L (v : G) ≤ X := by
    have hh := map_mono (f := J.subtype) hRW
    rwa [map_subgroupOf_eq_of_le hRJ] at hh
  let g := b.toMonoidHom.comp ((MulEquiv.subgroupCongr hW).toMonoidHom.comp (f.subgroupMap W))
  have hg : Function.Surjective g := b.surjective.comp
    ((MulEquiv.subgroupCongr hW).surjective.comp (f.subgroupMap_surjective W))
  have hgker : g.ker = f.ker.subgroupOf W := by
    ext x
    change b (MulEquiv.subgroupCongr hW (f.subgroupMap W x)) = 1 ↔ f (x : J) = 1
    rw [b.map_eq_one_iff,(MulEquiv.subgroupCongr hW).map_eq_one_iff]
    exact Subtype.ext_iff
  have hcore := ker_eq_twoCore_of_surjective_perm_three g hg (by
    rw [hgker,hk]
    exact pCore_isPGroup.comap_subtype)
  have hWcore : W.pCoreIn 2 = pCore 2 J := by
    rw [pCoreIn,←hcore,hgker,map_subgroupOf_eq_of_le (hkR.trans hRW),hk]
  have hXcore : X.pCoreIn 2 = Q T L := by
    have hh := congrArg (map J.subtype) hWcore
    rw [map_pCoreIn_of_injective 2 W J.subtype J.subtype_injective] at hh
    exact hh
  let eW : (W ⧸ pCore 2 W) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  let eX : Star X ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eW
  have hiB : (zpowers t).relIndex B = 3 := by
    have hh := ((zpowers t).subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRB).toEquiv,Nat.card_zpowers,ht.orderOf,
      Nat.card_congr b.toEquiv] at hh
    have hb : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hb] at hh
    change 2 * (zpowers t).relIndex B = 6 at hh
    omega
  have hiW : R₀.relIndex W = 3 := by
    have hh := relIndex_map_map f R₀ W
    rw [hr',hW,sup_eq_left.mpr hkR,sup_eq_left.mpr (hkR.trans hRW)] at hh
    exact hh.symm.trans hiB
  have hiX : (Rv T L (v : G)).relIndex X = 3 := by
    have hh := relIndex_map_map J.subtype R₀ W
    rw [(MonoidHom.ker_eq_bot_iff J.subtype).mpr J.subtype_injective,
      sup_bot_eq,sup_bot_eq,map_subgroupOf_eq_of_le hRJ] at hh
    exact hh.trans hiW
  have hSyl : Chapter1.IsSylowIn 2 (Rv T L (v : G)) X := by
    have hp : IsPGroup 2 ((Rv T L (v : G)).subgroupOf X) :=
      (isPGroup_pCoreIn 2 _).comap_subtype
    have hn : ¬ 2 ∣ ((Rv T L (v : G)).subgroupOf X).index := by
      change ¬ 2 ∣ (Rv T L (v : G)).relIndex X
      rw [hiX]
      decide
    exact ⟨hp.toSylow hn,map_subgroupOf_eq_of_le hRX⟩
  refine ⟨X,map_subtype_le _,hRX,hXcore,⟨eX⟩,hSyl,?_⟩
  have htop : W ⊔ C.subgroupOf J = ⊤ := by
    have hm : (W ⊔ C.subgroupOf J).map f = ⊤ := by rw [Subgroup.map_sup,hW,hc,hgen]
    have hkSup : f.ker ≤ W ⊔ C.subgroupOf J := (hkR.trans hRW).trans le_sup_left
    rw [←comap_map_eq_self hkSup,hm,comap_top]
  have hh := congrArg (map J.subtype) htop
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ J from inf_le_left),
    ←MonoidHom.range_eq_map,range_subtype] at hh


omit [IsElementaryAbelian 2 V] in
/-- Normalizer escape forbids a nontrivial characteristic subgroup of R_v
which is normalized by the three-letter overgroup. -/
theorem SourceHypothesis.nonsingular_three_characteristic_obstruction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (v : V) (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (X : Subgroup G) (hgen : X ⊔ (LT T L ⊓ Gv (v : G)) = LT T L)
    (B : Subgroup (Rv T L (v : G))) [B.Characteristic] (hB : B ≠ ⊥) :
    ¬ X ≤ normalizer (B.map (Rv T L (v : G)).subtype : Set G) := by
  intro hX
  let C := LT T L ⊓ Gv (v : G)
  let A := B.map (Rv T L (v : G)).subtype
  have hRN : normalizer (Rv T L (v : G) : Set G) ≤ normalizer (A : Set G) :=
    normalizer_le_normalizer_characteristic_image _ B
  have hCN : C ≤ normalizer (A : Set G) :=
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))).trans hRN
  have hAN : LT T L ≤ normalizer (A : Set G) := hgen ▸ sup_le hX hCN
  have hAJ : A ≤ LT T L := (map_subtype_le _).trans ((pCoreIn_le 2 C).trans inf_le_left)
  have hA : A ≠ ⊥ := fun hh => hB
    ((map_eq_bot_iff_of_injective B (Rv T L (v : G)).subtype_injective).mp hh)
  exact hn (hRN.trans (H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221 hAJ hA hAN))

/-- The original preferred escaping point supplies the actual S3 overgroup,
its two-core Q and Sylow R_v, and the characteristic-subgroup obstruction
needed by the solvable block argument. No block conclusion is assumed. -/
theorem SourceHypothesis.exists_preferred_nonsingular_three_overgroup_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧
      ¬ normalizer (Rv T L (w : G) : Set G) ≤ M L ∧
      Q T L < Rv T L (w : G) ∧
      (Q T L).relIndex (Rv T L (w : G)) = 2 ∧
      L ⊔ Rv T L (w : G) = LT T L ∧
      ∃ X : Subgroup G, X ≤ LT T L ∧ Rv T L (w : G) ≤ X ∧
        X.pCoreIn 2 = Q T L ∧ Nonempty (Star X ≃* Equiv.Perm (Fin 3)) ∧
        Chapter1.IsSylowIn 2 (Rv T L (w : G)) X ∧
        X ⊔ (LT T L ⊓ Gv (w : G)) = LT T L ∧
        ∀ B : Subgroup (Rv T L (w : G)), B.Characteristic → B ≠ ⊥ →
          ¬ X ≤ normalizer (B.map (Rv T L (w : G)).subtype : Set G) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,hidx,hjoin,_⟩ :=
    H.exists_preferred_nonsingular_original_extension_of_fixed D hTV hTI hz v hv he
  obtain ⟨X,hX,hRX,hcore,hquot,hSyl,hgen⟩ := H.nonsingular_original_three_overgroup D hTV w hw hr
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,hidx,hjoin,X,hX,hRX,hcore,hquot,hSyl,hgen,?_⟩
  intro B hB hne
  let := hB
  exact H.nonsingular_three_characteristic_obstruction w hn X hgen B hne

end CFSG.Quasithin.Chapter12.Section06
