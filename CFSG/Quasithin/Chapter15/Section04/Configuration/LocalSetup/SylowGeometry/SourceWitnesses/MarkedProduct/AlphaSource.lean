module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.AlphaFromAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.ThompsonImage
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.SylowFromAlpha

/-!
# The source alpha decomposition and Sylow witness

The literal four-dimensional action of the source member gives the hypotheses
of B.2.18 inside `X ⊔ T`. Transporting its conclusion back to the ambient group
proves the alpha decomposition, the order-four Thompson fixed subgroup and
containment of the moved module in the Baumann subgroup. The same decomposition
then supplies the source Sylow subgroup of `X ⊔ Baum(T)` and its two-core
containment, as required in Theorem 15.4.12 and Lemma 15.4.19.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
open ChapterB ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}
omit [Finite G] in
private theorem source_join_kernel_isPGroup
    {H : Type*} [Group H] (X S : Subgroup G) (hn : S ≤ normalizer (X : Set G))
    (hS : IsPGroup 2 S) (f : (X ⊔ S : Subgroup G) →* H)
    (hf : (f.comp (inclusion le_sup_left)).ker = pCore 2 X) : IsPGroup 2 f.ker := by
  let U := X ⊔ S
  let N := X.subgroupOf U
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le X.le_normalizer hn)
  have hgen : N ⊔ S.subgroupOf U = ⊤ := by
    apply map_injective U.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (U ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (S.subgroupOf U) hS.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* X :=
      (U.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict X (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 X := by
      intro x
      exact hf.le x.val.property
    let r' : q.ker →* pCore 2 X := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 X => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv


omit [Finite G] in
private theorem source_map_inf_centralizer {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Injective f) (A C : Subgroup G) :
    (A ⊓ centralizer (C : Set G)).map f = A.map f ⊓ centralizer (C.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem f ha.1,mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨c,hc,rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp ha.2 c hc)
  · rintro _ ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,mem_centralizer_iff.mpr ?_⟩,rfl⟩
    intro c hc'
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f c) (mem_map_of_mem f hc')

theorem source_baumann_module (h : Input K T M X 2) :
    IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G) ⊔ movedModule (T : Subgroup G) M X : Subgroup G) ∧
    Nat.card (movedModule (T : Subgroup G) M X ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) = 4 ∧
    movedModule (T : Subgroup G) M X ≤ baumann (T : Subgroup G) ∧
    thompsonAlpha (T : Subgroup G) =
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) ⊔
        (movedModule (T : Subgroup G) M X ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  obtain ⟨d⟩ := exists_sourceAction h
  let H := X ⊔ (T : Subgroup G)
  let W := movedModule (T : Subgroup G) M X
  have hHM : H ≤ M := sup_le h.member_le h.sylow_le
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  have hWH : W ≤ H := hWT.trans le_sup_right
  let W' := W.subgroupOf H
  let R : Sylow 2 H := T.subtype le_sup_right
  let e : W' ≃* W := subgroupOfEquivOfLe hWH
  let : W'.Normal := normal_subgroupOf_of_le_normalizer (hHM.trans h.moved_normalized)
  let : IsElementaryAbelian 2 W := h.moved_elementary
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.subgroupOf hWH
  let a : Action W' :=
    { coordinates := e.trans d.coordinates
      actor := d.actor.comp (inclusion hHM)
      intertwines := by
        intro g w
        apply Subtype.ext
        exact d.intertwines (inclusion hHM g) (e w) }
  have hker : IsPGroup 2 a.actor.ker := by
    apply source_join_kernel_isPGroup X (T : Subgroup G) (YFamily.invariant h.member) T.isPGroup' a.actor
    exact d.member_kernel h
  have hres : (pResidual 2 H).map H.subtype = X := member_residual_join T h.member
  have hmapL : (pResidual 2 H).map (inclusion hHM) = X.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le h.member_le]
    exact hres
  have hL : (pResidual 2 H).map a.actor = rotations := by
    change (pResidual 2 H).map (d.actor.comp (inclusion hHM)) = _
    rw [←map_map,hmapL,d.cubic_image]
  have hTmap : (R : Subgroup H).map H.subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le le_sup_right
  have hJmap : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hTmap]
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
    (sSup_le fun A hA => hA.1).trans h.sylow_le
  have hmapJ : (elementaryAbelianMaxJ (R : Subgroup H)).map (inclusion hHM) =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hJM]
    exact hJmap
  have hJactor : (elementaryAbelianMaxJ (R : Subgroup H)).map a.actor =
      ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M).map d.actor := by
    change (elementaryAbelianMaxJ (R : Subgroup H)).map (d.actor.comp (inclusion hHM)) = _
    rw [←map_map,hmapJ]
  have hbase : (elementaryAbelianMaxJ (R : Subgroup H)).map a.actor ≤ base := by
    rw [hJactor]
    rintro _ ⟨j,hj,rfl⟩
    apply d.baumann_base
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun A hA => hA.1
    refine ⟨hJT hj,?_⟩
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup H)).map a.actor) = 4 := by
    rw [hJactor]
    exact d.thompson_image_card h
  have hWR : W' ≤ (R : Subgroup H) := fun w hw => hWT hw
  have hEW := alpha_sup_elementary W' (R : Subgroup H) hWR (Action.noStrong a (R : Subgroup H))
  have hFix : Nat.card (W' ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup H) : Set H) : Subgroup H) = 4 := by
    rw [Nat.card_congr (Action.fixedEquiv a (elementaryAbelianMaxJ (R : Subgroup H)))]
    exact Concrete.base_four_fixed_card _ hbase hcard
  have ha := alpha_decomposition_from_action R W' a (fun w hw => hWT hw) hker hL hbase hcard
  have hWmap : W'.map H.subtype = W := map_subgroupOf_eq_of_le hWH
  have hAlpha : (thompsonAlpha (R : Subgroup H)).map H.subtype = thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (R : Subgroup H))).map _ = _
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hJmap]
    rfl
  have he := congrArg (Subgroup.map H.subtype) ha
  rw [Subgroup.map_sup,source_map_inf_centralizer H.subtype H.subtype_injective,
    source_map_inf_centralizer H.subtype H.subtype_injective,hAlpha,hres,hWmap,hJmap] at he
  have hEWAmb : IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G) ⊔ W : Subgroup G) := by
    have hh := hEW.map H.subtype
    rw [Subgroup.map_sup,hAlpha,hWmap] at hh
    exact hh
  have hFixAmb : Nat.card (W ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) = 4 := by
    rw [←hWmap,←hJmap,←source_map_inf_centralizer H.subtype H.subtype_injective,
      card_map_of_injective H.subtype_injective]
    exact hFix
  have hWS : W ≤ baumann (T : Subgroup G) := by
    let := hEWAmb
    refine le_inf hWT ?_
    intro w hw z hz
    exact setLike_mul_comm (show z ∈ thompsonAlpha (T : Subgroup G) ⊔ W from (le_sup_left : thompsonAlpha (T : Subgroup G) ≤ _) hz)
      (show w ∈ thompsonAlpha (T : Subgroup G) ⊔ W from (le_sup_right : W ≤ _) hw)
  exact ⟨hEWAmb,hFixAmb,hWS,he⟩

theorem source_alpha_decomposition (h : Input K T M X 2) :
    thompsonAlpha (T : Subgroup G) =
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) ⊔
        (movedModule (T : Subgroup G) M X ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :=
  (source_baumann_module h).2.2.2

theorem source_sylow_and_core (h : Input K T M X 2) :
    X.pCoreIn 2 ≤ baumann (T : Subgroup G) ∧
      (∃ P : Sylow 2 (X ⊔ baumann (T : Subgroup G) : Subgroup G),
        (P : Subgroup (X ⊔ baumann (T : Subgroup G) : Subgroup G)).map
          (X ⊔ baumann (T : Subgroup G) : Subgroup G).subtype = baumann (T : Subgroup G)) ∧
      (X ⊔ baumann (T : Subgroup G)).pCoreIn 2 ≤ baumann (T : Subgroup G) :=
  source_sylow_of_alpha_decomposition h (source_alpha_decomposition h)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
