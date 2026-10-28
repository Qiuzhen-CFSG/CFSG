module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpCommutator
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.First.Actor

/-!
# The actual enlarged binary normalizer in exterior pushing up

The original marked LT actor has a binary kernel and is already surjective
on L, so LT = L O₂(LT). Sylow conjugacy inside the literal section centralizer
aligns an overgroup R-plus of the original counterexample core R. The source
relative Sylow theorem gives R-plus ∩ H = R. If R-plus were R, the actual
covering residual would put the conjugate of LT in the outside overgroup,
contradicting maximal-overgroup uniqueness. Thus R < R-plus, and the binary
normalizer condition constructs R₁ = N_{R-plus}(R) > R.

After involution-centralizer reselection, C_G(r) ≤ H gives C_{R₁}(r) = R
and hence a nonzero commutator at the same chosen involution. The original
intersection residual normalizes this literal R₁. The full exterior module,
central covers, cubic and every relative placement from PushingUpCommutator
are retained in the consumer. The remaining p.612 step must establish
centralization of V and select an involution with its R₁-commutators in V;
nonzero commutation alone does not discharge those source premises.
The distinct p.623 odd-local comparison remains required.

Source: Aschbacher--Smith, 4.2.13, printed p.612, using 4.1.4(4) and the
original exterior marking. OddNormalizer supplies the literal Hall application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
/-- The original LT actor proves the source factorization by L and O₂(LT). -/
theorem SylowExteriorMarking.join_eq_component_sup_core (s : SylowExteriorMarking D) :
    L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U := L ⊔ (T : Subgroup G)
  have hker : s.actor.ker ≤ pCore 2 U :=
    le_sSup ⟨inferInstance,s.actor_kernel_isPGroup⟩
  refine le_antisymm ?_ (sup_le le_sup_left (pCoreIn_le 2 _))
  intro x hx
  obtain ⟨q,hq⟩ := s.marking.quotientEquiv.surjective (s.actor ⟨x,hx⟩)
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  let l' : U := inclusion le_sup_left l
  have he : s.actor l' = s.actor ⟨x,hx⟩ := (s.actor_component l).trans hq
  have hk : l'⁻¹ * ⟨x,hx⟩ ∈ s.actor.ker := by
    change s.actor (l'⁻¹ * ⟨x,hx⟩) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hc : (l : G)⁻¹ * x ∈ U.pCoreIn 2 := mem_map_of_mem U.subtype (hker hk)
  have hh := mul_mem_sup l.property hc
  simpa only [mul_inv_cancel_left] using hh

omit [Finite G] in
private theorem unique_map {I M : Subgroup G} (h : UniqueMaximalOvergroup I M)
    (e : G ≃* G) :
    UniqueMaximalOvergroup (I.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  refine ⟨Theory.Quasithin.isMaximalTwoLocal_map e h.1,map_mono h.2.1,?_⟩
  intro N hN hIN
  have hh : I ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hIN
  have he := h.2.2 _ (Theory.Quasithin.isMaximalTwoLocal_map e.symm hN) hh
  simpa [map_map] using congrArg (fun A : Subgroup G => A.map e.toMonoidHom) he

private theorem relative_normalizer_strict {R P : Subgroup G}
    (hP : IsPGroup 2 P) (hRP : R < P) : R < P ⊓ normalizer (R : Set G) := by
  let B := R.subgroupOf P
  have hb : B < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hm := congrArg (map P.subtype) he
    rw [map_subgroupOf_eq_of_le hRP.le,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hRP.ne hm
  let : Group.IsNilpotent P := hP.isNilpotent
  have hn := Group.normalizerCondition_of_isNilpotent B hb
  refine lt_of_le_not_ge (le_inf hRP.le R.le_normalizer) ?_
  intro he
  apply not_le_of_gt hn
  intro x hx
  apply he
  refine ⟨x.property,?_⟩
  have hh := R.subgroupOf P |>.le_normalizer_map P.subtype
  rw [map_subgroupOf_eq_of_le hRP.le] at hh
  exact hh (mem_map_of_mem P.subtype hx)

/-- The literal source normalizer is larger than the original counterexample
core. Its full intersection with the outside overgroup is exactly that core.
The section-centralizer conjugator and the original Sylow remain explicit. -/
theorem exterior_pushingUp_source_normalizer (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
      let R := J.pCoreIn 2
      let R₁ := P ⊓ normalizer (R : Set G)
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      P = ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom ∧
      P = sectionCentralizerIn (((c : G) • T : Sylow 2 G) : Subgroup G) L ∧
      L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G) = L ⊔ P ∧
      R < P ∧ P ⊓ H = R ∧ R < R₁ ∧ IsPGroup 2 R₁ ∧
      F ≤ normalizer (R₁ : Set G) := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let R := J.pCoreIn 2
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Mminus := coveringOvergroup M L (oddActorResidual L A)
  have hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) M :=
    exterior_component_sylow_unique s h
  have hyp := source_hypothesis411 h.toHypothesis1221 hM
  have hm : Mminus ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact mul_mem (hw.1.1.1.1 hj)
      ((show C ≤ Mminus from le_sup_right) (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hRC : R ≤ C := lemma_4_1_4_1 hyp hm hw.1
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 (R.subgroupOf C)).exists_le_sylow
  let P := (S : Subgroup C).map C.subtype
  have hRP : R ≤ P := by
    intro r hr
    exact ⟨⟨r,hRC hr⟩,hRS hr,rfl⟩
  have hPC : P ≤ C := map_subtype_le _
  have hP : IsPGroup 2 P := S.isPGroup'.map C.subtype
  have hRH : R ≤ H := (pCoreIn_le 2 J).trans hw.2.2.2.1
  obtain ⟨S₀,hS₀⟩ := core_sylow_sectionCentralizer_outside hyp hm hw.1
    (Chapter1.mem_H_of_isTwoLocal hw.2.2.1.1) hw.2.2.2.1
    (fun he => hw.2.2.2.2.1.ne (inf_eq_left.mpr he))
  have hPH : P ⊓ H = R := by
    have hs := Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2 R
      (sectionCentralizerIn (H ⊓ M) L) from ⟨S₀,hS₀⟩)
    exact hs.2.2 _ (hP.to_le inf_le_left) (le_inf hRP hRH) (by
      intro x hx
      exact ⟨⟨hx.2,(hPC hx.1).1⟩,(hPC hx.1).2⟩)
  have hLP : L ≤ normalizer (P : Set G) :=
    Chapter4.Section02.Unitary.sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S
  have hQ : L.pCoreIn 2 ≤ P := by
    apply (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      (componentCore_le_sectionCentralizer L.le_normalizer) ?_).trans
      (pCoreIn_le_sylow C S)
    exact ((le_sectionCentralizer_iff C L).mp inf_le_right).1.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  obtain ⟨c,hPc,hVW⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison h.toHypothesis1221 D hM S
  have ha := aligned_sylow_core hyp.plus_perfect D.sylow_normalizes_component c
  have hPa : (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2 = P :=
    ha.1.trans hPc
  have hLc : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hMc : M.map (MulAut.conj (c : G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer c.property.1)
  have hgen : (L ⊔ (T : Subgroup G)).map (MulAut.conj (c : G)).toMonoidHom = L ⊔ P := by
    rw [s.join_eq_component_sup_core,Subgroup.map_sup,hLc,hPc]
  have hgen' : L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G) = L ⊔ P := by
    change L ⊔ (T : Subgroup G).map (MulAut.conj (c : G)).toMonoidHom = L ⊔ P
    simpa only [Subgroup.map_sup,hLc] using hgen
  have hu : UniqueMaximalOvergroup (L ⊔ P) M := by
    have hh := unique_map hM (MulAut.conj (c : G))
    rwa [hgen,hMc] at hh
  have hlt : R < P := by
    apply lt_of_le_not_ge hRP
    intro he
    have hPH' : P ≤ H := he.trans hRH
    have hLH : L ≤ H := by
      intro l hl
      obtain ⟨f,hf,q,hq,rfl⟩ := hw.2.2.2.2.2.2.2.1 ▸ (show l ∈ (L : Set G) from hl)
      exact mul_mem (((map_subtype_le _).trans inf_le_right) hf) (hPH' (hQ hq))
    have heq := hu.2.2 H hw.2.2.1 (sup_le hLH hPH')
    exact hw.2.2.2.2.1.ne (by rw [heq,inf_idem])
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy _ _).trans hw.2.2.2.2.2.2.1.span_normalizes_radical
  have hFP : F ≤ normalizer (P : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans hLP
  refine ⟨c,?_⟩
  dsimp only
  rw [hPa]
  refine ⟨hPc.symm,hPa.symm.trans ha.2,hgen',hlt,hPH,relative_normalizer_strict hP hlt,
    hP.to_le inf_le_left,?_⟩
  exact (le_inf hFP (hFR.trans (normalizer (R : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The original R₁ after involution-centralizer reselection, with its
literal normalizer, relative intersections, conjugator and nonzero commutator. -/
@[expose] def ExteriorPushingUpSelectedNormalizerData
    (T : Sylow 2 G) (L J H H' : Subgroup G) (r : G) : Prop :=
  ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
      let R := J.pCoreIn 2
      let R₁ := P ⊓ normalizer (R : Set G)
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      P = ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom ∧
      P = sectionCentralizerIn (((c : G) • T : Sylow 2 G) : Subgroup G) L ∧
      L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G) = L ⊔ P ∧
      R < P ∧ P ⊓ H' = R ∧ R < R₁ ∧ IsPGroup 2 R₁ ∧
      F ≤ normalizer (R₁ : Set G) ∧
      R₁ ⊓ centralizer ({r} : Set G) = R ∧
      ∃ q ∈ R₁, ¬ Commute r q

/-- Apply the literal normalizer construction after involution-centralizer
reselection. This produces a nonzero commutator at the same involution;
centralization of V and containment of its commutator image in V remain
separate source obligations. -/
theorem exterior_pushingUp_selected_normalizer (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H I H' W' : Subgroup G}
    (hw' : Witness L V A I H' W')
    (hcore : I.pCoreIn 2 = J.pCoreIn 2)
    (hFI : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ I)
    (r : G) (hRr : J.pCoreIn 2 ≤ centralizer ({r} : Set G))
    (hCH : centralizer ({r} : Set G) ≤ H') :
    ExteriorPushingUpSelectedNormalizerData T L J H H' r := by
  obtain ⟨c,hPc,hPsec,hgen,hlt,hPH,hlt₁,hR₁,hFN⟩ :=
    exterior_pushingUp_source_normalizer s h hw'
  rw [hcore] at hlt hPH hlt₁ hR₁ hFN
  let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
  let R₁ := P ⊓ normalizer (J.pCoreIn 2 : Set G)
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Group.IsPerfect F := Group.IsPerfect.map _
  have hFF' : F ≤ (solvableResidual (L ⊓ H' : Subgroup G)).map (L ⊓ H').subtype :=
    le_map_solvableResidual_of_isPerfect F (L ⊓ H')
      (le_inf ((map_subtype_le _).trans inf_le_left) (hFI.trans hw'.2.2.2.1))
  have hcent : R₁ ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hCH)).trans_eq hPH
    · exact le_inf hlt₁.le hRr
  obtain ⟨q,hq,hqr⟩ := SetLike.exists_of_lt hlt₁
  refine ⟨c,hPc,hPsec,hgen,hlt,hPH,hlt₁,hR₁,hFF'.trans hFN,hcent,q,hq,?_⟩
  intro hc
  exact hqr (hcent ▸ (show q ∈ R₁ ⊓ centralizer ({r} : Set G) from
    ⟨hq,mem_centralizer_singleton_iff.mpr hc.symm⟩))

/-- Full exterior data with the actual enlarged normalizer at the selected involution. -/
@[expose] def ExteriorPushingUpNormalizerCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        let R := solvableResidual (centralizer ({k} : Set K))
        (IsQuasisimple R ∧ Nonempty ((R ⧸ center R) ≃* Sporadic.Mathieu.M22) ∧
          IsComponent (centralizer ({(k : H)} : Set H))
            (R.map (K.subtype.elementCentralizerMap k)) ∧
          R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M) ∧
        let I := F ⊔ J.pCoreIn 2
        I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
          ∃ (r : G) (H' W' : Subgroup G),
            r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
            K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
            centralizer ({r} : Set G) ≤ H' ∧ Witness L V A I H' W' ∧
            IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
            ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal ∧
            let Rg := R.map (H.subtype.comp (K.subtype.comp
              (centralizer ({k} : Set K)).subtype))
            let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg C ∧ (Rg.subgroupOf C).Normal ∧
            let X := centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg X ∧ (Rg.subgroupOf X).Normal ∧
              ⁅zpowers r, X⁆ ≤ centralizer (Rg : Set G) ∧
              (∃ v ∈ V, v ∈ X ∧ v ∉ centralizer (Rg : Set G)) ∧
              (∀ Q : Subgroup G, IsPGroup 2 Q → V ≤ centralizer (Q : Set G) →
                F ≤ normalizer (Q : Set G) → (∀ q ∈ Q, ⁅r,q⁆ ∈ V) →
                Q ≤ centralizer ({r} : Set G)) ∧
              ExteriorPushingUpSelectedNormalizerData T L J H H' r

/-- Retain the original cubic and full cover, and construct the source
normalizer with a nonzero commutator at the same selected involution. -/
theorem exterior_pushingUp_normalizer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpCommutatorCase s A) :
    ExteriorPushingUpNormalizerCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm,hmoved,hvanish⟩ := hj
  refine ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm,hmoved,hvanish,?_⟩
  exact exterior_pushingUp_selected_normalizer (H := H) s h hw' hcore le_sup_left r
    (le_sup_right.trans hCr) hCH'

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
