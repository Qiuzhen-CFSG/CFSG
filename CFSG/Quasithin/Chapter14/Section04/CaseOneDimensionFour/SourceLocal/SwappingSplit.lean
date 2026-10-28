module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Fusion
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.InvariantComplement
public import Theory.GroupTheory.Gaschutz
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalModel

/-!
# The original block splits in the swapping branch

The selected involution in Wᵍ − U interchanges the two quaternion factors.
The genuine block centralizer makes its action on V nontrivial, so the
quaternion calculation constructs an invariant four-group complement to V
in U. Adjoining the selected involution splits T∩L over V. Gaschütz then
splits L, whose index over T∩L is 21.

The source natural-module marking and this complement construct an actual
isomorphism L ≃ E₈ ⋊ SL₃(2). No model isomorphism or splitting assumption is
retained. SwappingGeometry applies this model at the original Sylow and point.
The residual normalizer index, swapping exclusion and final recognition
remain with qt-d-14414-g2-source. The earlier-source hypotheses retain their
existing producers, and universal I.4.5 belongs to qt-i45-g2-recognition.

Source: Aschbacher–Smith, proof of 14.4.4(2),(6), printed p.1007.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype)

include d earlier hq chosen previous hne hZ hcard g hgP hgH q hsX hs hout hswap

/-- The selected swapping involution preserves a literal four-group complement
of V in U. Nontriviality on V follows from the source block centralizer. -/
theorem source_invariant_complement_of_swapping :
    ∃ D : Subgroup G, D ≤ F.U ∧ Disjoint V D ∧ V ⊔ D = F.U ∧
      Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
      (s : G) ∈ normalizer (D : Set G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hTL := (source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1
  have hsTL : (s : G) ∈ (T : Subgroup G) ⊓ L :=
    hTL ▸ mem_sup_right (mem_zpowers (s : G))
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let E := V.subgroupOf F.U
  let α := F.uAction s
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hE : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans
    (by simpa [F.last] using F.card 3 (by decide))
  have hact : α ^ 2 = 1 := by dsimp [α]; rw [← map_pow, hs, map_one]
  have htransport (D : Subgroup F.U) :
      (D.map α.toMonoidHom).map F.U.subtype =
        (D.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hswap' : q.left.map α.toMonoidHom = q.right := by
    apply map_injective F.U.subtype_injective
    rw [htransport, hswap]
  have hEmap : E.map F.U.subtype = V := map_subgroupOf_eq_of_le hVU
  have hEstab : E.map α.toMonoidHom = E := by
    apply map_injective F.U.subtype_injective
    rw [htransport, hEmap]
    exact mem_normalizer_iff_map_conj_eq.mp
      (H.sylow_normalizes_seed previous.structural hsTL.1)
  have hZE : center F.U ≤ E := by
    intro z hz
    apply F.le_seed 1
    rw [← hZ]
    exact mem_map_of_mem F.U.subtype hz
  have hmoved : ∃ v ∈ E, α v ≠ v := by
    by_contra! h
    apply hout
    apply hVU
    apply (source_block_core d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).1.ge
    apply H.centralizer_L.le
    refine ⟨hsTL.2, ?_⟩
    intro v hv
    have he := congrArg (fun u : F.U => (u : G)) (h ⟨v,hVU hv⟩ hv)
    change (s : G) * v * (s : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨D,hD,hDc,hDe,hDa⟩ :=
    q.exists_invariant_complement_of_swap α hact hswap' E hE hZE hEstab hmoved
  let := hDe
  refine ⟨D.map F.U.subtype, ?_, ?_, ?_, ?_, IsElementaryAbelian.map_subtype, ?_⟩
  · rintro _ ⟨x,_,rfl⟩; exact x.property
  · simpa only [hEmap] using disjoint_map F.U.subtype_injective hD.disjoint
  · have he := congrArg (Subgroup.map F.U.subtype) hD.sup_eq_top
    simpa only [Subgroup.map_sup, hEmap, ← MonoidHom.range_eq_map, F.U.range_subtype] using he
  · rw [card_map_of_injective F.U.subtype_injective, hDc]
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (D.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom = _
    rw [← htransport, hDa]

/-- The selected swapping branch splits the original L over V. The proof
first extends the invariant four-group inside T∩L and then applies Gaschütz. -/
theorem source_split_of_swapping :
    ∃ D : Subgroup L, (V.subgroupOf L).IsComplement' D := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let S := (T : Subgroup G) ⊓ L
  obtain ⟨hV,hUL⟩ := source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  have hVL : V ≤ L := hV.le.trans (L.pCoreIn_le 2)
  have hVS : V ≤ S := le_inf chosen.le_sylow hVL
  have hVident : V.subgroupOf L = pCore 2 L := by
    rw [hV]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : (V.subgroupOf L).Normal := by rw [hVident]; infer_instance
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hVc : Nat.card (V.subgroupOf L) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv]
    simpa [F.last] using F.card 3 (by decide)
  have hLc : Nat.card L = 1344 := by
    have e := H.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
    have hc : Nat.card (L ⧸ pCore 2 L) = 168 :=
      (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L), hc, ← hVident, hVc]
  have hSc : Nat.card S = 64 := (source_sylow_index d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  have hindex : (S.subgroupOf L).index = 21 := by
    have hh := (S.subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show S ≤ L from inf_le_right)).toEquiv,
      hSc,hLc] at hh
    omega
  obtain ⟨D,hDU,hd,hspan,hDc,hDe,hDn⟩ := source_invariant_complement_of_swapping
    d earlier hq chosen previous F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  have hTL := (source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1
  have hUS : F.U ≤ S := by change F.U ≤ (T : Subgroup G) ⊓ L; rw [hTL]; exact le_sup_left
  have hDS : D ≤ S := hDU.trans hUS
  have hsS : (s : G) ∈ S := by
    change (s : G) ∈ (T : Subgroup G) ⊓ L
    rw [hTL]
    exact mem_sup_right (mem_zpowers (s : G))
  let a : S := ⟨s,hsS⟩
  let U₀ := F.U.subgroupOf S
  let V₀ := V.subgroupOf S
  let D₀ := D.subgroupOf S
  have hUi : U₀.index = 2 := by
    have hh := U₀.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv, hcard,hSc] at hh
    omega
  let : U₀.Normal := U₀.normal_of_index_eq_two hUi
  let : V₀.Normal := (normal_subgroupOf_iff_le_normalizer hVS).mpr
    (inf_le_right.trans chosen.normalizes)
  have ha : a ^ 2 = 1 := by
    apply Subtype.ext
    change (s : G) ^ 2 = 1
    exact congrArg (fun x : F.H => (x : G)) hs
  have hsplit : V₀.IsComplement' (D₀ ⊔ zpowers a) := by
    apply isComplement_sup_zpowers_of_invariant U₀ V₀ D₀
      (fun _ hx => hDU hx) ?_ ?_ a ha hout ?_ ?_
    · change V.subgroupOf S ⊔ D.subgroupOf S = F.U.subgroupOf S
      rw [← subgroupOf_sup hVS hDS, hspan]
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hd hx hy)
    · apply mem_normalizer_iff.mpr
      intro x
      exact mem_normalizer_iff.mp hDn x
    · apply map_injective S.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUS, MonoidHom.map_zpowers]
      change F.U ⊔ zpowers (s : G) = _
      rw [← hTL, ← MonoidHom.range_eq_map, S.range_subtype]
  let e : S ≃* S.subgroupOf L := (subgroupOfEquivOfLe (show S ≤ L from inf_le_right)).symm
  apply exists_complement_of_coprime_overgroup (V.subgroupOf L) (S.subgroupOf L)
    (fun _ hx => hVS hx) (by rw [hVc,hindex]; decide)
  refine ⟨(D₀ ⊔ zpowers a).map e.toMonoidHom, ?_⟩
  have he : ((V.subgroupOf L).subgroupOf (S.subgroupOf L)) = V₀.map e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      exact hy
  rw [he]
  apply isComplement'_of_card_mul_and_disjoint
  · rw [card_map_of_injective e.injective, card_map_of_injective e.injective,
      hsplit.card_mul_card, Nat.card_congr e.toEquiv]
  · exact disjoint_map e.injective hsplit.disjoint

/-- Splitting and the original source marking construct the full natural model.
Normality here is only the intrinsic relative subgroup instance. -/
theorem source_split_natural_data_of_swapping [(V.subgroupOf L).Normal] :
    Nonempty (Matrix.PSL3Two.SplitParabolic.SplitNaturalData (V.subgroupOf L)) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hV := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  have hVL : V ≤ L := hV.le.trans (L.pCoreIn_le 2)
  have hVident : V.subgroupOf L = pCore 2 L := by
    rw [hV]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  obtain ⟨D,hD⟩ := source_split_of_swapping d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout hswap
  let A := H.naturalMarking
  let e := BinaryLinear.OuterCyclic.slEquivLinear 3
  let quotient := ((QuotientGroup.quotientMulEquivOfEq hVident).trans A.quotientEquiv).trans e.symm
  let coordinates : (V.subgroupOf L) ≃* Matrix.PSL3Two.SplitParabolic.E3 :=
    (subgroupOfEquivOfLe hVL).trans A.coordinates.toAddEquiv.toMultiplicativeRight
  refine ⟨{ quotient := quotient
            moduleEquiv := coordinates
            complement := D
            splitting := hD
            equivariant := ?_ }⟩
  intro l v
  apply Multiplicative.toAdd.injective
  have h := A.equivariant l (Additive.ofMul (subgroupOfEquivOfLe hVL v))
  have he := congrArg (fun f : BinaryLinear.OuterCyclic.LinearGroup 3 =>
    f (A.coordinates (Additive.ofMul (subgroupOfEquivOfLe hVL v))))
    (e.apply_symm_apply (A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)))
  dsimp only [quotient, MulEquiv.trans_apply, MulEquiv.toMonoidHom_eq_coe,
    QuotientGroup.mk'_apply] at *
  simp only [QuotientGroup.quotientMulEquivOfEq_mk]
  exact h.trans he.symm

/-- The swapping branch gives an actual isomorphism of the original L. -/
theorem source_split_model_of_swapping :
    Nonempty (L ≃* Matrix.PSL3Two.SplitParabolic.Block) := by
  have hV := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  let : (V.subgroupOf L).Normal := by
    rw [hV]
    change (Subgroup.comap L.subtype ((pCore 2 L).map L.subtype)).Normal
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  obtain ⟨data⟩ := source_split_natural_data_of_swapping d earlier hq chosen previous F
    hne hZ hcard g hgP hgH q s hsX hs hout hswap
  exact ⟨data.blockEquiv⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
