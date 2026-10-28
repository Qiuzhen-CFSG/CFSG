module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionPointQuotient
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains

/-!
# The source central-line configuration in the exceptional A₇ branch

Notation 12.2.5(3) defines L_z=O²(C_L(z)). Its solvable residual is
C_L(z)∞, whose concrete PSL₃(2) quotient was established in PointQuotient.
The point-stabilizer action moves all of V, and relative normality puts V
inside this residual. The actual core O₂(C_L(z)∞ T) equals O₂(LT): one
inclusion uses the faithful action, the other uses normality of O₂(LT).
This supplies characteristic-normalizer control and every clause of C.2.8.

Faithfulness and source 1.2.4 then construct the unique containing component
of G_z. Source 1.2.9 makes it faithful, and the local-chain normalizer theorem
makes it T-invariant. SourceEndgame applies the proved block and Frattini
argument; the proper-enlargement exclusions remain obligations of
qt-d-1233-natural-coordinates.

The later sentence on printed p.808 instead writes O²(C_{M_V}(z)). This
module preserves that published normalizer-residual API without identifying
its residual with C_L(z)∞. It uses the original definition in 12.2.5 and
proves each local assertion directly on that subgroup.

Source: Aschbacher--Smith, Notation 12.2.5 and Lemmas 12.2.12, 12.3.3,
printed pp.796,799,808; local-component deductions 1.2.4, 1.2.8, 1.2.9.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

abbrev fourComponentPointCore (z : G) : Subgroup G :=
  (S.fourComponentPointPerfect z ⊔ (T : Subgroup G)).pCoreIn 2

private theorem source_point_le (z : G) : S.fourComponentPointPerfect z ≤ L ⊓ centralizer ({z} : Set G) :=
  map_subtype_le _

private theorem source_point_local (z : G) : S.fourComponentPointPerfect z ≤ S.fourPointLocal z :=
  (S.source_point_le z).trans (inf_le_inf_right _ L.le_normalizer)

private theorem source_faithful_projection_action
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (l : L) : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
  let := S.chosen.actionCentralizer_normal
  change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
  rw [e.symm_apply_apply]
  rfl

private theorem source_pointVector_val (z : V) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
  congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)

private theorem source_chosenAction_val (l : L) (w : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l w)) : G) =
      l * (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ := by
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem source_pointVector_ne_zero {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  apply hz
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

private theorem source_covers
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1)
    (g : BinaryAlternatingSevenControl.pointStabilizer
      (S.fourFaithfulAction e) (S.fourPointVector z)) :
    ∃ l : L, (l : G) ∈ S.fourComponentPointPerfect z ∧ S.fourFaithfulProjection e l = g := by
  obtain ⟨l,hl,he⟩ := (S.four_componentPointPerfect_image e hd z hz).ge g.property
  exact ⟨l,hl,he⟩

/-- The whole original V is moved by the residual inside C_L(z). -/
theorem four_componentPointPerfect_moved
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    V = ⁅V,S.fourComponentPointPerfect z⁆ := by
  let := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  have hz' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  let ρ := S.fourFaithfulAction e
  let j : Multiplicative S.chosen.space →* G :=
    V.subtype.comp S.chosen.spaceEquiv.toMonoidHom
  have hfull := BinaryAlternatingSevenControl.pointStabilizer_moved ρ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd (S.source_pointVector_ne_zero hz')
  have hspan : ∀ w ∈ subspaceCommutator ρ ⊤
      (BinaryAlternatingSevenControl.pointStabilizer ρ (S.fourPointVector z')),
      j (Multiplicative.ofAdd w) ∈ ⁅V,S.fourComponentPointPerfect z⁆ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a,ha,v,_,rfl⟩ := hw
      obtain ⟨l,hl,he⟩ := S.source_covers e hd z' hz' ⟨a,ha⟩
      change S.fourFaithfulProjection e l = a at he
      have hact : ρ a v = S.chosen.chosenAction l v := by
        rw [← he]
        exact LinearMap.congr_fun (S.source_faithful_projection_action e l) v
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      change (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l v)) : G) *
        (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G)⁻¹ ∈ _
      rw [S.source_chosenAction_val,commutator_comm V]
      exact commutator_mem_commutator hl (S.chosen.spaceEquiv (Multiplicative.ofAdd v)).property
    | zero => simpa only [ofAdd_zero,map_one] using (⁅V,S.fourComponentPointPerfect z⁆).one_mem
    | add a b _ _ ha hb =>
      change j (Multiplicative.ofAdd a * Multiplicative.ofAdd b) ∈ _
      rw [map_mul]
      exact mul_mem ha hb
    | smul a w _ hw =>
      have ha : a = 0 ∨ a = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
      rcases ha with rfl | rfl
      · simpa only [zero_smul] using (show j (Multiplicative.ofAdd (0 : S.chosen.space)) ∈
          ⁅V,S.fourComponentPointPerfect z⁆ from by simpa only [ofAdd_zero,map_one] using (⁅V,S.fourComponentPointPerfect z⁆).one_mem)
      · simpa only [one_smul] using hw
  apply le_antisymm
  · intro v hv
    obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
    have hm := hspan w.toAdd (hfull.symm ▸ Submodule.mem_top)
    change (S.chosen.spaceEquiv w : G) ∈ _ at hm
    rwa [hw] at hm
  · have hn : S.fourComponentPointPerfect z ≤ normalizer (V : Set G) :=
      (S.source_point_le z).trans (inf_le_left.trans S.chosen.normalizes)
    exact le_normalizer_iff_commutator_le_left.mp hn

/-- Local normalization puts the whole V inside the source residual. -/
theorem four_module_le_componentPointPerfect
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) : V ≤ S.fourComponentPointPerfect z :=
  (S.four_componentPointPerfect_moved e hd hz hz1).le.trans
    (le_normalizer_iff_commutator_le_right.mp
      ((S.four_module_le_pointLocal hz).trans
        (S.four_componentPointPerfect_normalized)))

private theorem source_point_join_le_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (z : G) :
    S.fourComponentPointPerfect z ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le ((S.source_point_le z).trans (inf_le_left.trans S.chosen.normalizes))
    ((structural G T L S.hypothesis).2.2 V S.chosen).1

private theorem source_point_join_le_centralizer {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointPerfect z ⊔ (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  apply sup_le ((S.source_point_le z).trans inf_le_right)
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem source_normalizerProjection_fixes_point
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (n : normalizer (V : Set G))
    (hn : (n : G) ∈ centralizer ({(z : G)} : Set G)) :
    S.fourNormalizerProjection structural e hd n ∈
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e)
        (S.fourPointVector z) := by
  apply (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mpr
  apply Multiplicative.ofAdd.injective
  apply S.chosen.spaceEquiv.injective
  apply Subtype.ext
  rw [S.fourNormalizerProjection_action]
  have hv : S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) = z :=
    S.chosen.spaceEquiv.apply_symm_apply z
  rw [hv]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hn)

private def source_pointJoinProjection
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) →*
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e)
        (S.fourPointVector z) :=
  ((S.fourNormalizerProjection structural e hd).comp
    (inclusion (S.source_point_join_le_normalizer structural z))).codRestrict _
      (fun x => S.source_normalizerProjection_fixes_point structural e hd z _
        (S.source_point_join_le_centralizer hzT x.property))

private theorem source_source_pointJoinProjection_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) (hzT : (z : G) ∈ omegaCenterIn (T : Subgroup G)) :
    Function.Surjective (S.source_pointJoinProjection structural e hd z hzT) := by
  intro a
  obtain ⟨l,hl,he⟩ := S.source_covers e hd z hz a
  have hlJ : (l : G) ∈ S.fourComponentPointPerfect z ⊔ (T : Subgroup G) := mem_sup_left hl
  refine ⟨⟨l,hlJ⟩,?_⟩
  apply Subtype.ext
  change S.fourNormalizerProjection structural e hd
    ⟨l,S.source_point_join_le_normalizer structural z hlJ⟩ = a
  rw [S.fourNormalizerProjection_component]
  exact he

/-- The core of the source residual joined with T centralizes the whole V. -/
theorem four_componentPointCore_centralizes
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : let := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointCore z ≤ centralizer (V : Set G) := by
  let := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  have hz' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  have hv : S.fourPointVector z' ≠ 0 := by
    intro he
    apply hz'
    have h := congrArg (fun v => S.chosen.spaceEquiv (Multiplicative.ofAdd v)) he
    simpa only [fourPointVector,ofAdd_toAdd,MulEquiv.apply_symm_apply,
      ofAdd_zero,map_one] using h
  let f := S.source_pointJoinProjection structural e hd z' hzT
  have hf := S.source_source_pointJoinProjection_surjective structural e hd z' hz' hzT
  let A := BinaryAlternatingSevenControl.pointStabilizer
    (S.fourFaithfulAction e) (S.fourPointVector z')
  let a := BinaryAlternatingSevenControl.pointStabilizerEquivLinear
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective) hd hv
  have hA : pCore 2 A = ⊥ := by
    apply (map_eq_bot_iff_of_injective (pCore 2 A) (f := a.toMonoidHom) a.injective).mp
    rw [pCore_map_iso,BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot]
  have hm : (pCore 2 (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G)).map f ≤
      pCore 2 A :=
    le_sSup ⟨(inferInstance : (pCore 2 _).Normal).map f hf, pCore_isPGroup.map f⟩
  rintro q ⟨x,hx,rfl⟩
  have hx0 : f x = 1 := mem_bot.mp (hA ▸ hm (mem_map_of_mem f hx))
  have hxproj : S.fourNormalizerProjection structural e hd
      ⟨x,S.source_point_join_le_normalizer structural z x.property⟩ = 1 :=
    congrArg Subtype.val hx0
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
  have h := S.fourNormalizerProjection_action structural e hd
    ⟨x,S.source_point_join_le_normalizer structural z x.property⟩ w.toAdd
  rw [hxproj,map_one] at h
  have hval : (S.chosen.spaceEquiv w : G) = v := congrArg Subtype.val hw
  change (S.chosen.spaceEquiv w : G) =
    (x : G) * (S.chosen.spaceEquiv w : G) * (x : G)⁻¹ at h
  rw [hval] at h
  exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm

/-- The source two-core is Sylow in the literal section centralizer. -/
theorem four_componentPointCore_section_sylow
    {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    Chapter1.IsSylowIn 2 (S.fourComponentPointCore z) (ChapterA.Section04.twoSectionCentralizer (S.fourComponentPointPerfect z) (S.fourPointCentralizer z)) := by
  have hTC : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp ((mem_omegaCenterIn_iff _ _).mp hzT).2.1) t ht)
  have hTM : (T : Subgroup G) ≤ S.fourPointLocal z :=
    le_inf S.chosen.sylow_normalizes_component hTC
  have hTK := hTM.trans (S.four_componentPointPerfect_normalized)
  let K := S.fourComponentPointPerfect z
  have hperfect : IsPPerfect 2 K := by
    intro N hn hq
    let := hn
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hs : Chapter1.IsSylowIn 2 (S.fourComponentPointCore z)
      (ChapterA.Section04.twoSectionCentralizer K (normalizer (K : Set G))) :=
    ChapterA.Section04.sylow_core_sectionCentralizer T K hperfect hTK
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    let P := T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)
    have hh := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) P
    simpa only [P, Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using hh
  have hQ := (Chapter1.isSylowIn_iff.mp hs).2.1
  apply hs.restrict
  · intro q hq
    exact ⟨hTC (hQT hq),(hQ hq).2⟩
  · intro y hy
    exact ⟨hy.2.1,hy.2⟩


/-- The point two-residual specified in Notation 12.2.5(3). -/
def fourComponentPointResidual (_S : Setup T L V) (z : G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({z} : Set G)).subtype

/-- Taking the solvable residual after the two-residual gives precisely the
already recognized subgroup C_L(z)∞. -/
theorem four_componentPointPerfect_eq_residual (z : G) :
    S.fourComponentPointPerfect z =
      (solvableResidual (S.fourComponentPointResidual z)).map
        (S.fourComponentPointResidual z).subtype := by
  have hs : solvableResidual (L ⊓ centralizer ({z} : Set G) : Subgroup G) ≤
      pResidual 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    apply le_sInf
    rintro N ⟨hn,hq⟩
    let := hn
    let := hq.isNilpotent
    exact solvableResidual_le_of_solvable_quotient N
  apply le_antisymm
  · exact le_map_solvableResidual_of_isPerfect _ _ (map_mono hs)
  · exact map_solvableResidual_mono (map_subtype_le _)

/-- The source core agrees with the original Q of Notation 12.2.5. -/
theorem four_componentPointCore_eq_chosenCore
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointCore z = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := S.fourComponentPointPerfect z ⊔ (T : Subgroup G)
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  apply le_antisymm
  · rw [← S.chosen_sylowCentralizer_eq_core structural]
    exact le_inf hQT (S.four_componentPointCore_centralizes structural e hd hz hz1 hzT)
  · have hRT : R ≤ (T : Subgroup G) := by
      dsimp only [R]
      rw [← S.chosen_sylowCentralizer_eq_core structural]
      exact inf_le_left
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hRT.trans le_sup_right)
    have hJ : J ≤ L ⊔ (T : Subgroup G) :=
      sup_le_sup ((S.source_point_le z).trans inf_le_left) le_rfl
    exact hJ.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))

private theorem source_sylow_le_local {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointLocal z := by
  refine le_inf S.chosen.sylow_normalizes_component ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem source_core_control
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ((S.fourComponentPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z) := by
  have hc : (S.fourComponentPointCore z).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
    rw [S.four_componentPointCore_eq_chosenCore structural e hd hz hz1 hzT]
    exact S.chosen_core_characteristicControl structural
  have hQH := (Chapter1.isSylowIn_iff.mp
    (S.four_componentPointCore_section_sylow hzT)).2.1.trans
      (ChapterA.Section04.twoSectionCentralizer_le _ _)
  have hh := characteristicNormalizerClosure_subgroupOf_le hQH hc
  intro g hg
  exact ⟨hh hg, g.property⟩

private theorem source_point_span (z : G) :
    conjugateSpanBy (S.fourComponentPointPerfect z) (S.fourPointLocal z) =
      S.fourComponentPointPerfect z :=
  le_antisymm (conjugateSpanBy_le le_rfl S.four_componentPointPerfect_normalized)
    (le_conjugateSpanBy _ _)

private theorem source_point_join_core {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (S.fourComponentPointPerfect z ⊔ S.fourComponentPointCore z).pCoreIn 2 =
      S.fourComponentPointCore z := by
  let J := S.fourComponentPointPerfect z ⊔ (T : Subgroup G)
  have hJK : J ≤ normalizer (S.fourComponentPointPerfect z : Set G) :=
    sup_le (S.fourComponentPointPerfect z).le_normalizer
      ((S.source_sylow_le_local hzT).trans S.four_componentPointPerfect_normalized)
  have hJQ : J ≤ normalizer (S.fourComponentPointCore z : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKQJ : S.fourComponentPointPerfect z ⊔ S.fourComponentPointCore z ≤ J :=
    sup_le le_sup_left (pCoreIn_le 2 J)
  refine le_antisymm (pCoreIn_mono_of_normalizes hKQJ ?_) ?_
  · exact (le_inf hJK hJQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) le_sup_right (hKQJ.trans hJQ)

private theorem source_module_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ (center (S.fourComponentPointCore z)).map (S.fourComponentPointCore z).subtype := by
  have hVQ : V ≤ S.fourComponentPointCore z := by
    rw [S.four_componentPointCore_eq_chosenCore structural e hd hz hz1 hzT]
    exact S.chosen.le_core
  have hQV := S.four_componentPointCore_centralizes structural e hd hz hz1 hzT
  intro v hv
  refine ⟨⟨v,hVQ hv⟩,mem_center_iff.mpr ?_,rfl⟩
  intro q
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (hQV q.property) v hv).symm

/-- The C.2.8 configuration on the residual specified by Notation 12.2.5.
Every component, core, and control premise is discharged. -/
theorem four_component_pushingUp
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourComponentPointPerfect z)
      (S.fourComponentPointCore z) V := by
  have hTM := S.source_sylow_le_local hzT
  have hQT : S.fourComponentPointCore z ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (S.fourComponentPointPerfect z ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hQM := hQT.trans hTM
  have hsection := S.four_componentPointCore_section_sylow hzT
  have hsectionM : Chapter1.IsSylowIn 2 (S.fourComponentPointCore z)
      (ChapterA.Section04.twoSectionCentralizer (S.fourComponentPointPerfect z) (S.fourPointLocal z)) := by
    apply hsection.restrict
    · intro q hq
      exact ⟨hQM hq,((Chapter1.isSylowIn_iff.mp hsection).2.1 hq).2⟩
    · intro y hy
      exact ⟨hy.1.2,hy.2⟩
  refine {
    sqtk := S.hypothesis.simpleQTKE.involution_centralizer_sqtk
      (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
    radical_isTwoGroup := isPGroup_pCoreIn 2 _
    radical_le := hQM
    local_le := inf_le_right
    local_fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (S.four_pointLocal_characteristicTwo hz hz1 hzT))
    core_nontrivial := ?_
    component_le := S.source_point_local z
    component := S.four_componentPointPerfect_component e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he))
    section_sylow := by rw [S.source_point_span]; exact hsectionM
    characteristic_control := S.source_core_control structural e hd hz hz1 hzT
    module_nontrivial := S.chosen.ne_bot
    module_elementary := S.chosen.elementary
    module_le := by rw [S.source_point_span]; exact S.four_module_le_componentPointPerfect e hd hz hz1
    module_commutator := by rw [S.source_point_span]; exact S.four_componentPointPerfect_moved e hd hz hz1
    module_central := by
      rw [S.source_point_span,S.source_point_join_core hzT]
      exact S.source_module_central structural e hd hz hz1 hzT
    module_normalizer := ?_ }
  · have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,pow_one]
      exact orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
    have hle : zpowers z ≤ (S.fourPointCentralizer z).pCoreIn 2 :=
      le_pCoreIn_of_normalizes hp (zpowers_le.mpr (by simp [mem_centralizer_singleton_iff]))
        (by change centralizer ({z} : Set G) ≤ _
            rw [← centralizer_closure,← zpowers_eq_closure]
            exact Subgroup.centralizer_le_normalizer _)
    exact fun he => hz1 (mem_bot.mp (he ▸ hle (mem_zpowers z)))
  · rw [S.four_pointLocal_eq structural hz hz1]
    exact inf_comm _ _ |>.le

private theorem source_point_twoPerfect (z : G) : IsPPerfect 2 (S.fourComponentPointPerfect z) := by
  intro N hn hq
  let := hn
  let := hq.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

/-- Characteristic two passes to the normal perfect residual. -/
theorem four_componentPointPerfect_characteristicTwo
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourComponentPointPerfect z ∈ Chapter1.He G := by
  have hn : ((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z)).Normal :=
    normal_subgroupOf_of_le_normalizer (S.four_componentPointPerfect_normalized)
  exact Chapter1.lemma_1_1_3_1 (S.four_pointLocal_characteristicTwo hz hz1 hzT)
    (fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_componentPointPerfect e hd hz hz1).trans he.le)))
    (S.source_point_local z) hn.isSubnormal

/-- The full original module lies in the omega-center of the intrinsic core. -/
theorem four_module_le_componentPerfectCore_omegaCenter
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ omegaCenterIn ((S.fourComponentPointPerfect z).pCoreIn 2) := by
  let := S.chosen.elementary
  have hKN : S.fourComponentPointPerfect z ≤ normalizer (V : Set G) :=
    (S.source_point_le z).trans (inf_le_left.trans S.chosen.normalizes)
  have hVK : V ≤ S.fourComponentPointPerfect z := S.four_module_le_componentPointPerfect e hd hz hz1
  have hVc : V ≤ (S.fourComponentPointPerfect z).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVK hKN
  have hTJ : (S.fourComponentPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) ≤
      normalizer (S.fourComponentPointPerfect z : Set G) :=
    sup_le (S.fourComponentPointPerfect z).le_normalizer
      ((S.source_sylow_le_local hzT).trans
        (S.four_componentPointPerfect_normalized))
  have hcQ : (S.fourComponentPointPerfect z).pCoreIn 2 ≤ S.fourComponentPointCore z :=
    pCoreIn_mono_of_normalizes le_sup_left hTJ
  have hVcC : V ≤ centralizer ((S.fourComponentPointPerfect z).pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hcQ.trans (S.four_componentPointCore_centralizes structural e hd hz hz1 hzT))
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hVc hv, hVcC hv, elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- The original module is contained in the actual intrinsic signalizer module. -/
theorem four_componentModule_le_intrinsicSignalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ ChapterA.Section04.intrinsicSignalizerModule (S.fourComponentPointPerfect z) := by
  rw [ChapterA.Section04.intrinsicSignalizerModule,
    ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]
  exact (S.four_componentPointPerfect_moved e hd hz hz1).le.trans
    (commutator_mono (S.four_module_le_componentPerfectCore_omegaCenter structural e hd hz hz1 hzT) le_rfl)

/-- Faithful signalizer membership follows from the original four-space. -/
theorem four_componentPointPerfect_faithful
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterA.Section04.IsFaithfulSignalizerType (S.fourComponentPointPerfect z) := by
  refine ⟨⟨?_, S.source_point_twoPerfect z, ?_⟩, ?_⟩
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_componentPointPerfect e hd hz hz1).trans he.le))
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (S.four_componentPointPerfect_characteristicTwo e hd hz hz1 hzT))
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_componentModule_le_intrinsicSignalizer structural e hd hz hz1 hzT).trans he.le))

/-- The recognized source component belongs to the genuine Sylow local family. -/
theorem four_componentPointPerfect_local
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) :
    S.fourComponentPointPerfect z ∈ Chapter1.L G (T : Subgroup G) := by
  have hTM := S.source_sylow_le_local hzT
  apply Chapter1.mem_L_of_cComponent ?_
    ⟨T.subtype hTM, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]⟩
    (S.source_point_local z) (S.four_componentPointPerfect_component e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he)))
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
  have hle : zpowers z ≤ (S.fourPointLocal z).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (zpowers_le.mpr (S.four_module_le_pointLocal hz hz))
      (inf_le_right.trans (by
        rw [← centralizer_closure,← zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer _))
  exact fun he => hz1 (mem_bot.mp (he ▸ hle (mem_zpowers z)))

/-- The source residual lies in a unique actual component of G_z. The
containing component is in the faithful local family and is normalized by T. -/
theorem four_component_exists_unique_overcomponent
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z) ∧
      S.fourComponentPointPerfect z ≤ K ∧
      (∀ J : Subgroup G, J ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z) →
        S.fourComponentPointPerfect z ≤ J → J = K) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) := by
  have hb := S.four_componentPointPerfect_local hz hz1 hzT e hd
  have hfaith := S.four_componentPointPerfect_faithful structural e hd hz hz1 hzT
  have hTH := (S.source_sylow_le_local hzT).trans inf_le_right
  have hBH : S.fourComponentPointPerfect z ≤ S.fourPointCentralizer z :=
    (S.source_point_le z).trans inf_le_right
  have hH : S.fourPointCentralizer z ∈ Chapter1.HOver G (T : Set G) :=
    ⟨(S.four_component_pushingUp structural e hd hz hz1 hzT).core_nontrivial,hTH⟩
  have hbH : (S.fourComponentPointPerfect z).subgroupOf (S.fourPointCentralizer z) ∈
      Chapter1.L (S.fourPointCentralizer z) ((T.subtype hTH) : Subgroup (S.fourPointCentralizer z)) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTH hBH).mp ⟨hBH,hb⟩
  obtain ⟨K,⟨hK,hBK⟩,hu⟩ := (Chapter1.existsUnique_cComponentsIn_iff hBH).mp
    (Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
      (Chapter1.Section02.containment_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      (Chapter1.Section02.uniqueness_local_quotient_sqtk S.hypothesis.simpleQTKE hH.1)
      (T.subtype hTH) hbH)
  have hKL := ((Chapter1.lemma_1_2_6 T hH).1 hK).2
  have hKf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (S.hypothesis.simpleQTKE.evenCharacteristic T)
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr ⟨hb,hfaith⟩)
    hKL hBK
  exact ⟨K,hK,hBK,fun J hJ hj => hu J ⟨hJ,hj⟩,hKL,
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hKf).2,
    Chapter1.Section02.Adequate.local_chain_normalizes hb hKL hBK
      ((S.source_sylow_le_local hzT).trans S.four_componentPointPerfect_normalized)⟩

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
