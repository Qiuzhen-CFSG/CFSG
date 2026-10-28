module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionResiduals
public import Theory.Representation.BinaryAlternatingSevenControl.PointStabilizer
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction

/-!
# The action of the literal central-line residual in the A₇ four-space

The point stabilizer in A₇ is perfect and moves the entire four-space.
Surjectivity of the original projection therefore lifts its operators through
the solvable residual of C_L(z), which lies in the literal K_z=L_z^∞.
This proves V=[V,K_z] and V≤K_z, and realizes every operator on V/⟨z⟩
by an actual element of L∩K_z. The same representatives give transitivity
on the fourteen points outside ⟨z⟩.

For a central involution of T, the actual O₂(K_z T) is Sylow in the
section centralizer C_{G_z}(K_z/O₂(K_z)), by the two-perfect signalizer
calculus. The C.2.8, local-family and two-core quotient fields remain
explicit in the final conditional assembly; their construction and the
ambient exclusion remain with qt-d-1233-natural-coordinates.

Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808, using B.4.12(2),
12.2.12, and A.4.2.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

private abbrev pointComponent (_S : Setup T L V) (z : G) := L ⊓ centralizer ({z} : Set G)

def fourFaithfulProjection
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) :
    L →* alternatingGroup (Fin 7) := by
  letI := S.chosen.actionCentralizer_normal
  exact e.toMonoidHom.comp (QuotientGroup.mk' _)

def fourFaithfulAction
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) :
    Representation (ZMod 2) (alternatingGroup (Fin 7)) S.chosen.space := by
  letI := S.chosen.actionCentralizer_normal
  exact S.chosen.faithfulAction.comp e.symm.toMonoidHom

private theorem faithful_projection_action
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (l : L) : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
  letI := S.chosen.actionCentralizer_normal
  change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
  rw [e.symm_apply_apply]
  rfl

abbrev fourPointVector (z : V) : S.chosen.space :=
  (S.chosen.spaceEquiv.symm z).toAdd

private theorem pointVector_val (z : V) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
  congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)

private theorem chosenAction_val (l : L) (w : S.chosen.space) :
    (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l w)) : G) =
      l * (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ := by
  rw [S.chosen.spaceEquiv_apply, S.chosen.spaceEquiv_apply]
  rfl

private theorem fixes_point_iff
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) (l : L) :
    S.fourFaithfulAction e (S.fourFaithfulProjection e l) (S.fourPointVector z) = S.fourPointVector z ↔
      (l : G) ∈ centralizer ({(z : G)} : Set G) := by
  rw [S.faithful_projection_action]
  have hi : Function.Injective (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) :=
    Subtype.val_injective.comp (S.chosen.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  rw [← hi.eq_iff, S.chosenAction_val, S.pointVector_val,
    mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

private def pointActor
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) : S.pointComponent z →*
      BinaryAlternatingSevenControl.pointStabilizer (S.fourFaithfulAction e) (S.fourPointVector z) :=
  ((S.fourFaithfulProjection e).comp (inclusion inf_le_left)).codRestrict _ (fun l =>
    (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mpr
      ((S.fixes_point_iff e z ⟨l,l.property.1⟩).mpr l.property.2))

private theorem pointActor_surjective
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) : Function.Surjective (S.pointActor e z) := by
  letI := S.chosen.actionCentralizer_normal
  intro g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) (e.symm g)
  have hf : S.fourFaithfulProjection e l = g := by
    change e (QuotientGroup.mk' _ l) = g
    rw [hl,e.apply_symm_apply]
  have hc : (l : G) ∈ centralizer ({(z : G)} : Set G) := by
    apply (S.fixes_point_iff e z l).mp
    rw [hf]
    exact (BinaryAlternatingSevenControl.mem_pointStabilizer _ _ _).mp g.property
  exact ⟨⟨l,l.property,hc⟩,Subtype.ext hf⟩

private theorem pointVector_ne_zero {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  apply hz
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

private theorem component_residual_le_perfect {z : G} :
    (solvableResidual (S.pointComponent z)).map (S.pointComponent z).subtype ≤
      S.fourPointPerfect z := by
  have hj : S.pointComponent z ≤ S.fourPointModuleNormalizer z :=
    inf_le_inf_right _ S.chosen.normalizes
  have hs : solvableResidual (S.fourPointModuleNormalizer z) ≤
      pResidual 2 (S.fourPointModuleNormalizer z) := by
    apply le_sInf
    rintro N ⟨hn,hN⟩
    letI := hn
    letI : Group.IsNilpotent ((S.fourPointModuleNormalizer z) ⧸ N) := hN.isNilpotent
    exact solvableResidual_le_of_solvable_quotient N
  have hr := map_solvableResidual_eq_of_residual_le
    (pResidual 2 (S.fourPointModuleNormalizer z)) hs
  let he := (pResidual 2 (S.fourPointModuleNormalizer z)).equivMapOfInjective
    (S.fourPointModuleNormalizer z).subtype (S.fourPointModuleNormalizer z).subtype_injective
  have hm := map_solvableResidual_eq he.toMonoidHom he.surjective
  have heq : S.fourPointPerfect z =
      (solvableResidual (S.fourPointModuleNormalizer z)).map
        (S.fourPointModuleNormalizer z).subtype := by
    unfold fourPointPerfect fourPointResidual
    rw [← hm, map_map]
    have hc : ((pResidual 2 (S.fourPointModuleNormalizer z)).map
        (S.fourPointModuleNormalizer z).subtype).subtype.comp he.toMonoidHom =
        (S.fourPointModuleNormalizer z).subtype.comp
          (pResidual 2 (S.fourPointModuleNormalizer z)).subtype := by
      apply MonoidHom.ext
      intro x
      exact coe_equivMapOfInjective_apply (pResidual 2 (S.fourPointModuleNormalizer z))
        (S.fourPointModuleNormalizer z).subtype (S.fourPointModuleNormalizer z).subtype_injective x
    rw [hc, ← map_map, hr]
  rw [heq]
  exact map_solvableResidual_mono hj

/-- Every point-stabilizer operator has a representative in the literal K_z. -/
theorem four_pointPerfect_covers_pointAction
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1)
    (g : BinaryAlternatingSevenControl.pointStabilizer
      (S.fourFaithfulAction e) (S.fourPointVector z)) :
    ∃ l : L, (l : G) ∈ S.fourPointPerfect z ∧ S.fourFaithfulProjection e l = g := by
  letI := S.chosen.actionCentralizer_normal
  letI := BinaryAlternatingSevenControl.pointStabilizer_perfect
    (S.fourFaithfulAction e)
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd (S.pointVector_ne_zero hz)
  have hm := map_solvableResidual_eq (S.pointActor e z) (S.pointActor_surjective e z)
  rw [solvableResidual_eq_top (G := BinaryAlternatingSevenControl.pointStabilizer
    (S.fourFaithfulAction e) (S.fourPointVector z))] at hm
  have hg : g ∈ (solvableResidual (S.pointComponent z)).map (S.pointActor e z) :=
    hm.symm ▸ mem_top g
  obtain ⟨l,hl,he⟩ := hg
  exact ⟨⟨l,l.property.1⟩,
    S.component_residual_le_perfect (mem_map_of_mem _ hl),congrArg Subtype.val he⟩

/-- The literal residual already realizes every linear automorphism of the
quotient of the original chosen space by its central line. The representatives
are actual elements of L ∩ K_z, with the original conjugation action. -/
theorem four_pointPerfect_covers_quotientAction
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1)
    (f : Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace (S.fourPointVector z) ≃ₗ[ZMod 2]
      Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace (S.fourPointVector z)) :
    ∃ l : L, (l : G) ∈ S.fourPointPerfect z ∧ ∀ v : S.chosen.space,
      (Theory.LinearAlgebra.BinaryFivePointStabilizer.line (S.fourPointVector z)).mkQ
        (S.chosen.chosenAction l v) =
      f ((Theory.LinearAlgebra.BinaryFivePointStabilizer.line (S.fourPointVector z)).mkQ v) := by
  letI := S.chosen.actionCentralizer_normal
  let ρ := S.fourFaithfulAction e
  obtain ⟨g,hg⟩ := (BinaryAlternatingSevenControl.pointQuotientAction_bijective ρ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd
    (S.pointVector_ne_zero hz)).surjective f
  obtain ⟨l,hl,he⟩ := S.four_pointPerfect_covers_pointAction e hd z hz g
  refine ⟨l,hl,?_⟩
  intro v
  have hact : S.chosen.chosenAction l v = ρ g v := by
    rw [← S.faithful_projection_action e l, he]
  rw [hact, ← BinaryAlternatingSevenControl.pointQuotientAction_mk, hg]

/-- Away from the fixed line, the actual K_z is transitive on the original
four-space. The conjugators lie in L ∩ K_z, not merely in an abstract model. -/
theorem four_pointPerfect_transitive
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z x y : G} (hz : z ∈ V) (hx : x ∈ V) (hy : y ∈ V)
    (hz1 : z ≠ 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ l ∈ L, l ∈ S.fourPointPerfect z ∧ l * x * l⁻¹ = y := by
  letI := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  let x' : V := ⟨x,hx⟩
  let y' : V := ⟨y,hy⟩
  have hn (v : V) (hv : (v : G) ≠ 1) : v ≠ 1 :=
    fun he => hv (congrArg Subtype.val he)
  have hsep (v : V) (hv : (v : G) ≠ z) : S.fourPointVector v ≠ S.fourPointVector z' := by
    intro he
    apply hv
    have h := congrArg (fun w => (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) he
    simpa only [S.pointVector_val] using h
  let ρ := S.fourFaithfulAction e
  obtain ⟨g,hg⟩ := BinaryAlternatingSevenControl.pointStabilizer_transitive ρ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd
    (S.pointVector_ne_zero (hn z' hz1)) (S.pointVector_ne_zero (hn x' hx1))
    (S.pointVector_ne_zero (hn y' hy1)) (hsep x' hxz) (hsep y' hyz)
  obtain ⟨l,hl,he⟩ := S.four_pointPerfect_covers_pointAction e hd z' (hn z' hz1) g
  refine ⟨l,l.property,hl,?_⟩
  have hact : S.chosen.chosenAction l (S.fourPointVector x') = S.fourPointVector y' := by
    rw [← S.faithful_projection_action e l, he]
    exact hg
  have h := congrArg (fun w => (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) hact
  simpa only [S.chosenAction_val, S.pointVector_val] using h

/-- The original V is moved by K_z, before any ambient normality of K_z. -/
theorem four_pointPerfect_moved
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    V = ⁅V,S.fourPointPerfect z⁆ := by
  letI := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  have hz' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  let ρ := S.fourFaithfulAction e
  let j : Multiplicative S.chosen.space →* G :=
    V.subtype.comp S.chosen.spaceEquiv.toMonoidHom
  have hfull := BinaryAlternatingSevenControl.pointStabilizer_moved ρ
    (S.chosen.faithfulAction_injective.comp e.symm.injective) hd (S.pointVector_ne_zero hz')
  have hspan : ∀ w ∈ subspaceCommutator ρ ⊤
      (BinaryAlternatingSevenControl.pointStabilizer ρ (S.fourPointVector z')),
      j (Multiplicative.ofAdd w) ∈ ⁅V,S.fourPointPerfect z⁆ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a,ha,v,_,rfl⟩ := hw
      obtain ⟨l,hl,he⟩ := S.four_pointPerfect_covers_pointAction e hd z' hz' ⟨a,ha⟩
      change S.fourFaithfulProjection e l = a at he
      have hact : ρ a v = S.chosen.chosenAction l v := by
        rw [← he]
        exact LinearMap.congr_fun (S.faithful_projection_action e l) v
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      change (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.chosen.chosenAction l v)) : G) *
        (S.chosen.spaceEquiv (Multiplicative.ofAdd v) : G)⁻¹ ∈ _
      rw [S.chosenAction_val,commutator_comm V]
      exact commutator_mem_commutator hl (S.chosen.spaceEquiv (Multiplicative.ofAdd v)).property
    | zero => simpa only [ofAdd_zero,map_one] using (⁅V,S.fourPointPerfect z⁆).one_mem
    | add a b _ _ ha hb =>
      change j (Multiplicative.ofAdd a * Multiplicative.ofAdd b) ∈ _
      rw [map_mul]
      exact mul_mem ha hb
    | smul a w _ hw =>
      have ha : a = 0 ∨ a = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
      rcases ha with rfl | rfl
      · simpa only [zero_smul] using (show j (Multiplicative.ofAdd (0 : S.chosen.space)) ∈
          ⁅V,S.fourPointPerfect z⁆ from by simpa only [ofAdd_zero,map_one] using (⁅V,S.fourPointPerfect z⁆).one_mem)
      · simpa only [one_smul] using hw
  apply le_antisymm
  · intro v hv
    obtain ⟨w,hw⟩ := S.chosen.spaceEquiv.surjective ⟨v,hv⟩
    have hm := hspan w.toAdd (hfull.symm ▸ Submodule.mem_top)
    change (S.chosen.spaceEquiv w : G) ∈ _ at hm
    rwa [hw] at hm
  · have hn : S.fourPointPerfect z ≤ normalizer (V : Set G) :=
      (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left)
    exact le_normalizer_iff_commutator_le_left.mp hn

/-- Local normalization and the moved equality put the full original V in K_z. -/
theorem four_module_le_pointPerfect
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) : V ≤ S.fourPointPerfect z :=
  (S.four_pointPerfect_moved e hd hz hz1).le.trans
    (le_normalizer_iff_commutator_le_right.mp
      ((S.four_module_le_pointLocal hz).trans
        (S.four_pointLocal_normalizes_perfect structural hz hz1)))

/-- The actual two-core Q is Sylow in C_{G_z}(K_z/O₂(K_z)). -/
theorem four_pointCore_section_sylow
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    Chapter1.IsSylowIn 2 (S.fourPointCore z) (S.fourPointSection z) := by
  have hTC : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp ((mem_omegaCenterIn_iff _ _).mp hzT).2.1) t ht)
  have hTM : (T : Subgroup G) ≤ S.fourPointLocal z :=
    le_inf S.chosen.sylow_normalizes_component hTC
  have hTK := hTM.trans (S.four_pointLocal_normalizes_perfect structural hz hz1)
  let K := S.fourPointPerfect z
  let eK := (solvableResidual (S.fourPointResidual z)).equivMapOfInjective
    (S.fourPointResidual z).subtype (S.fourPointResidual z).subtype_injective
  letI : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hperfect : IsPPerfect 2 K := by
    intro N hn hq
    letI := hn
    by_contra hne
    letI : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    letI : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    letI : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hs : Chapter1.IsSylowIn 2 (S.fourPointCore z)
      (ChapterA.Section04.twoSectionCentralizer K (normalizer (K : Set G))) :=
    ChapterA.Section04.sylow_core_sectionCentralizer T K hperfect hTK
  have hQT : S.fourPointCore z ≤ (T : Subgroup G) := by
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

/-- Assemble the residual interface once its remaining local-structure inputs
are proved. The moved-module and section-Sylow fields are discharged here.
The source-theorem assembly remains with the natural-coordinate owner. -/
theorem fourResidualData_of_local_structure
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (pushingUp : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourPointPerfect z)
      (S.fourPointCore z) V)
    (faithful : ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z))
    (local_member : S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z where
  pushingUp := pushingUp
  faithful := faithful
  local_member := local_member
  quotient := quotient
  moved := S.four_pointPerfect_moved e hd hz hz1
  section_sylow := S.four_pointCore_section_sylow structural hz hz1 hzT

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
