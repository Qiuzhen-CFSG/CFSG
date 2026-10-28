module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedMaximal
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.GroupGeometry
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Overlap
public import Theory.GroupTheory.QuotientIntersection

/-!
# The actual exchanged component geometry

The genuine minimal-parabolic component theorem gives two commuting factors.
Removing the ambient two-core makes each factor simple. Self-normalization of
the component overlap then separates the two Borel coordinates. The local
wrappers retain precisely H/O₂(H), its residual image, and M∩H.

Source: Aschbacher–Smith E.2.2, pp.215–216; 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D : Type*} [Group D]

/-- Self-normalization of the first overlap separates the two commuting
coordinates of every element of the overlap with the product. -/
theorem overlap_sup_of_self_normalizing (M K L : Subgroup D)
    (hc : K ≤ centralizer (L : Set D))
    (hself : K ⊓ normalizer ((K ⊓ M : Subgroup D) : Set D) = K ⊓ M) :
    M ⊓ (K ⊔ L) = (M ⊓ K) ⊔ (M ⊓ L) := by
  have hLK := le_centralizer_iff.mp hc
  apply le_antisymm ?_ (sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
    (le_inf inf_le_left (inf_le_right.trans le_sup_right)))
  rintro r ⟨hrM,hr⟩
  have hrprod : r ∈ (K : Set D) * (L : Set D) := by
    rw [← coe_mul_of_right_le_normalizer_left K L
      (hLK.trans (Subgroup.centralizer_le_normalizer _))]
    exact hr
  obtain ⟨k,hk,l,hl,hkl⟩ := hrprod
  have hlA : l ∈ normalizer ((K ⊓ M : Subgroup D) : Set D) :=
    (Subgroup.centralizer_le_normalizer _) (fun a ha => hLK hl a ha.1)
  have hrA : r ∈ normalizer ((K ⊓ M : Subgroup D) : Set D) := by
    apply inf_normalizer_le_normalizer_inf
    refine ⟨?_,M.le_normalizer hrM⟩
    rw [← hkl]
    exact (normalizer (K : Set D)).mul_mem (K.le_normalizer hk)
      (Subgroup.centralizer_le_normalizer _ (hLK hl))
  have hkA : k ∈ normalizer ((K ⊓ M : Subgroup D) : Set D) := by
    have hh := (normalizer ((K ⊓ M : Subgroup D) : Set D)).mul_mem hrA
      ((normalizer ((K ⊓ M : Subgroup D) : Set D)).inv_mem hlA)
    simpa only [← hkl,mul_inv_cancel_right] using hh
  have hkM : k ∈ M := (show k ∈ K ⊓ M from hself ▸ ⟨hk,hkA⟩).2
  have hlM : l ∈ M := by
    have hh := M.mul_mem (M.inv_mem hkM) hrM
    simpa only [← hkl,inv_mul_cancel_left] using hh
  rw [← hkl]
  exact mul_mem_sup ⟨hkM,hk⟩ ⟨hlM,hl⟩

variable [Finite D]

/-- The original generating simple component gives all the product and
Borel geometry used by the exchanged representation calculation. -/
theorem geometry_of_generating_component
    (hD : IsStronglyQuasithin D) (T : Sylow 2 D) (M K : Subgroup D)
    (hK : IsComponent D K) (hz : center K = ⊥)
    (hgen : K ⊔ (T : Subgroup D) = ⊤) (hn : ¬K.Normal)
    (hTM : (T : Subgroup D) ≤ M)
    (hself : K ⊓ normalizer ((K ⊓ M : Subgroup D) : Set D) = K ⊓ M) :
    ExchangedGeometry K (pResidual 2 D) (T : Subgroup D)
      (M ⊓ pResidual 2 D) (M ⊓ K) := by
  rcases ChapterE.Structure.component_normal_or_pair hD T hK hgen with h |
    ⟨s,hne,hL,hcomm,hR,hres,hswap,hindex⟩
  · exact (hn h.1).elim
  let L := K.conjBy (s : D)
  have hc : K ≤ centralizer (L : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hLK := le_centralizer_iff.mp hc
  have hKR : K ≤ pResidual 2 D := by rw [hres]; exact le_sup_left
  have hNR : pResidual 2 D ≤ normalizer (K : Set D) := by
    rw [hres]
    exact sup_le K.le_normalizer (hLK.trans (Subgroup.centralizer_le_normalizer _))
  have hdis : Disjoint K L := by
    rw [disjoint_iff_inf_le]
    intro k hk
    have hkz : (⟨k,hk.1⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun x => Subtype.ext (hLK hk.2 x x.property))
    rw [hz,mem_bot] at hkz
    exact mem_bot.mpr (congrArg Subtype.val hkz)
  have hB : (T : Subgroup D) ≤ normalizer ((M ⊓ pResidual 2 D : Subgroup D) : Set D) := by
    apply (le_inf (hTM.trans M.le_normalizer) ?_).trans inf_normalizer_le_normalizer_inf
    rw [normalizer_eq_top]
    exact le_top
  have hsout : (s : D)⁻¹ ∉ normalizer (K : Set D) := by
    intro hs
    exact hne (mem_normalizer_iff_map_conj_eq.mp
      (by simpa using (normalizer (K : Set D)).inv_mem hs))
  refine ⟨hKR,hNR,inf_le_right,hB,⟨(s : D)⁻¹,T.inv_mem s.property,hsout⟩,?_⟩
  intro t ht hout
  have hti : t⁻¹ ∉ normalizer (K : Set D) := fun h =>
    hout (by simpa using (normalizer (K : Set D)).inv_mem h)
  have htL : K.conjBy t⁻¹ = L := by
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex hne t⁻¹ with h | h
    · exact (hti (mem_normalizer_iff_map_conj_eq.mpr h)).elim
    · exact h
  have hret : K.conjBy t = K.conjBy t⁻¹ :=
    rightConjugate_return_of_square ((normalizer (K : Set D)).sq_mem_of_index_two hindex t)
  refine ⟨?_,?_,?_,hret,?_⟩
  · rw [htL]; exact hres.symm
  · rw [htL]; exact hdis
  · rw [htL]; exact hc
  · have hov := overlap_sup_of_self_normalizing M K L hc hself
    have hresL : pResidual 2 D = K ⊔ L := hres
    rw [← hresL] at hov
    rw [hov]
    congr 1
    change M ⊓ L = (M ⊓ K).map (MulAut.conj t⁻¹).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective]
    have hm : M.map (MulAut.conj t⁻¹).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hTM (T.inv_mem ht)))
    rw [hm]
    exact congrArg (fun A : Subgroup D => M ⊓ A) htL.symm

/-- The E.2 minimal parabolic source supplies the overlap premise itself. -/
theorem geometry_of_minimal_parabolic
    (hD : IsStronglyQuasithin D) (T : Sylow 2 D)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup D)
    (hK : IsComponent D K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup D) = ⊤) (hn : ¬K.Normal) :
    ExchangedGeometry K (pResidual 2 D) (T : Subgroup D)
      (ChapterB.minimalParabolicMax T hP ⊓ pResidual 2 D)
      (ChapterB.minimalParabolicMax T hP ⊓ K) := by
  have hz : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance with h | h
    · exact h
    · let := hK.2
      exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  exact geometry_of_generating_component hD T _ K hK hz hgen hn
    (ChapterB.minimalParabolicMax_spec T hP).2
    (ChapterE.Structure.component_maximal_intersection_self_normalizing hD T hP hK hgen)

/-- The source E.2 component and core identity supply the preceding geometry
on the literal quotient by O₂(D). -/
theorem simple_geometry_on_twoCore_quotient
    (hD : IsSQTK KnownSimple.IsKnownSimple D) (T : Sylow 2 D)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable D)
    (K : Subgroup D) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup D) = ⊤) (hn : ¬K.Normal) :
    let q := QuotientGroup.mk' (pCore 2 D)
    let M := (ChapterB.minimalParabolicMax T hP).map q
    IsSimpleGroup (K.map q) ∧ ExchangedGeometry (K.map q) (pResidual 2 (D ⧸ pCore 2 D))
      ((T : Subgroup D).map q) (M ⊓ pResidual 2 (D ⧸ pCore 2 D))
      (M ⊓ K.map q) := by
  let q := QuotientGroup.mk' (pCore 2 D)
  have hq := QuotientGroup.mk'_surjective (pCore 2 D)
  let S := T.mapSurjective hq
  have hker : q.ker ≤ (T : Subgroup D) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal T
  have hPs := ChapterB.minimalParabolic_surjective T hP q hq hker
  let : Group.IsNilpotent (pCore 2 D) := (pCore_isPGroup (p := 2) (G := D)).isNilpotent
  have hsQ : ¬ Group.IsSolvable (D ⧸ pCore 2 D) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient (pCore 2 D)).mpr ⟨inferInstance,hh⟩)
  let : IsQuasisimple (K ⧸ pCore 2 K) := hqK
  have hKQ : IsComponent (D ⧸ pCore 2 D) (K.map q) :=
    ⟨hK.subnormal.map hq, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  have hgenQ : K.map q ⊔ (S : Subgroup (D ⧸ pCore 2 D)) = ⊤ := by
    change K.map q ⊔ (T : Subgroup D).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hnq : ¬ (K.map q).Normal := fun h =>
    hn (cComponent_normal_of_quotient_normal hK (pCore 2 D) h)
  have hSQ := ChapterE.Structure.sqtk_two_quotient hD (pCore 2 D) pCore_isPGroup
  have hz := ChapterE.Structure.PairedCore.component_center_eq_bot
    ChapterA.Section02.theoremA_knownSimple hSQ S hPs hsQ
    (pCore_quotient_pCore_eq_bot (G := D) 2) hKQ hgenQ hnq
  let : IsQuasisimple (K.map q) := hKQ.2
  let : IsSimpleGroup ((K.map q) ⧸ center (K.map q)) := IsQuasisimple.simple
  let : IsSimpleGroup (K.map q) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hm : ChapterB.minimalParabolicMax S hPs =
      (ChapterB.minimalParabolicMax T hP).map q :=
    (ChapterB.minimalParabolicMax_map T hP q hq hker).symm
  have hgeo := geometry_of_minimal_parabolic
    hSQ.stronglyQuasithin S hPs
    (K.map q) hKQ hgenQ hnq
  rw [hm] at hgeo
  exact ⟨inferInstance,hgeo⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {G : Type*} [Group G] [Finite G]

/-- All product and Borel maps in the source geometry are those of the
original local quotient H/O₂(H). -/
theorem local_geometry {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup G).subgroupOf H = ⊤) (hn : ¬K.Normal) :
    ExchangedGeometry (actorImage H (K.map H.subtype)) (actorImage H (residual H))
      (actorImage H T) (borelImage H M) (actorImage H (M ⊓ K.map H.subtype)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hM := BorelReduction.SourceCases.overlap_eq_minimalParabolicMax hH hP
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  have hcore : q.ker ≤ M.subgroupOf H := by
    rw [QuotientGroup.ker_mk',hM]
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.prop.1.2)).trans
      (ChapterB.minimalParabolicMax_spec _ hP).2
  have hgeo := (simple_geometry_on_twoCore_quotient hSQTK (T.subtype hH.prop.1.2)
    hP hs K hK hqK hgen hn).2
  rw [← hM] at hgeo
  have hk : actorImage H (K.map H.subtype) = K.map q := by
    unfold actorImage subgroupOf
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  have hr : actorImage H (residual H) = pResidual 2 (H ⧸ pCore 2 H) := by
    unfold actorImage residual subgroupOf
    rw [comap_map_eq_self_of_injective H.subtype_injective,map_pResidual_quotient]
  have hb : borelImage H M = (M.subgroupOf H).map q ⊓ pResidual 2 (H ⧸ pCore 2 H) := by
    unfold borelImage actorImage residual subgroupOf
    rw [comap_inf,comap_map_eq_self_of_injective H.subtype_injective]
    change (M.subgroupOf H ⊓ pResidual 2 H).map q = _
    rw [inf_comm,map_inf_of_ker_le q _ _ hcore,inf_comm]
    exact congrArg ((M.subgroupOf H).map q ⊓ ·) (map_pResidual_quotient 2 (pCore 2 H))
  have hc : actorImage H (M ⊓ K.map H.subtype) = (M.subgroupOf H).map q ⊓ K.map q := by
    unfold actorImage subgroupOf
    rw [comap_inf,comap_map_eq_self_of_injective H.subtype_injective]
    change (M.subgroupOf H ⊓ K).map q = _
    rw [inf_comm,map_inf_of_ker_le q _ _ hcore,inf_comm]
    rfl
  rw [hk,hr,hb,hc]
  exact hgeo

/-- Simplicity of the actual component image used by the moving-actor argument. -/
theorem local_component_simple {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup G).subgroupOf H = ⊤) (hn : ¬K.Normal) :
    IsSimpleGroup (actorImage H (K.map H.subtype)) := by
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  have hi := (simple_geometry_on_twoCore_quotient hSQTK (T.subtype hH.prop.1.2)
    hP hs K hK hqK hgen hn).1
  unfold actorImage subgroupOf
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact hi

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
