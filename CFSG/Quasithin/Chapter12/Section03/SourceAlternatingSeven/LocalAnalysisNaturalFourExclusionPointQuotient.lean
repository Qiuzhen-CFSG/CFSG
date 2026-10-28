module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionControl
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalCoordinates
public import Theory.GroupTheory.PerfectCentralCoverLocalResidual
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover

/-!
# The literal central-line quotient inside the original A₇ component

Let D be the solvable residual of C_L(z). The original faithful projection
maps D onto the point stabilizer PSL₃(2). After removing O₂(L), its kernel
is central. Transfer for the cyclic odd Sylow subgroups of PSL₃(2) removes
the odd kernel, so the original map identifies D/O₂(D) with the actual
matrix carrier. In particular D is a C-component of M_z.

The original L-point residual is contained in the published normalizer
residual K_z=(O²(C_{N(V)}(z)))∞. If K_z≤L, perfectness makes them equal;
the final application then supplies the complete published FourResidualData.
This containment, the enlargement exclusions and the block contradiction
remain with qt-d-1233-natural-coordinates. The two residual conventions
are kept distinct rather than inferred from equality of their action images.

Source: Aschbacher--Smith, Notation 12.2.5 and Lemma 12.3.3, printed
pp.796,807–808; the central-cover transfer input is I.1.2, printed p.407.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- The solvable residual of the point centralizer inside the original L. -/
def fourComponentPointPerfect (_S : Setup T L V) (z : G) : Subgroup G :=
  (solvableResidual (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({z} : Set G)).subtype

instance fourComponentPointPerfect_perfect (z : G) :
    Group.IsPerfect (S.fourComponentPointPerfect z) := Group.IsPerfect.map _

private theorem component_point_comap
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (z : V) :
    (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
      (BinaryAlternatingSevenControl.pointStabilizer
        (S.fourFaithfulAction e) (S.fourPointVector z)).comap (S.fourFaithfulProjection e) := by
  let := S.chosen.actionCentralizer_normal
  ext l
  change ((l : G) ∈ L ∧ (l : G) ∈ centralizer ({(z : G)} : Set G)) ↔ _
  rw [and_iff_right l.property, mem_comap, BinaryAlternatingSevenControl.mem_pointStabilizer]
  have he : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
      S.chosen.chosenAction l := by
    change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he]
  have hi : Function.Injective (fun w : S.chosen.space =>
      (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) :=
    Subtype.val_injective.comp (S.chosen.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  rw [← hi.eq_iff]
  have hv : (S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector z)) : G) = z :=
    congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply z)
  have ha : (S.chosen.spaceEquiv (Multiplicative.ofAdd
      (S.chosen.chosenAction l (S.fourPointVector z))) : G) =
      (l : G) * (z : G) * (l : G)⁻¹ := by
    rw [S.chosen.spaceEquiv_apply]
    change (l : G) * _ * (l : G)⁻¹ = _
    congr 1
    congr 1
    exact (S.chosen.spaceEquiv_apply (S.fourPointVector z)).symm.trans hv
  rw [ha,hv,mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]

private theorem vector_nonzero {z : V} (hz : z ≠ 1) : S.fourPointVector z ≠ 0 := by
  intro he
  apply hz
  have h := congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he
  simpa only [fourPointVector, ofAdd_toAdd, MulEquiv.apply_symm_apply, ofAdd_zero, map_one] using h

/-- The actual L-point residual covers the exact stabilizer in the faithful A₇. -/
theorem four_componentPointPerfect_image
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) :
    ((S.fourComponentPointPerfect z).subgroupOf L).map (S.fourFaithfulProjection e) =
      BinaryAlternatingSevenControl.pointStabilizer
        (S.fourFaithfulAction e) (S.fourPointVector z) := by
  let := S.chosen.actionCentralizer_normal
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let f := (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).symm
  have hm := map_solvableResidual_eq f.toMonoidHom f.surjective
  have hr : (S.fourComponentPointPerfect z).subgroupOf L =
      (solvableResidual (C.subgroupOf L)).map (C.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    have hKL : S.fourComponentPointPerfect z ≤ L := (map_subtype_le _).trans inf_le_left
    rw [map_subgroupOf_eq_of_le hKL, ← hm, map_map, map_map]
    rfl
  let := BinaryAlternatingSevenControl.pointStabilizer_perfect
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective)
    hd (S.vector_nonzero hz)
  rw [hr, S.component_point_comap e z,
    map_solvableResidual_comap _ (e.surjective.comp (QuotientGroup.mk'_surjective _)),
    solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

/-- The perfect subgroup in the original central cover has only a two-group
kernel on V; the possible odd central kernel is removed by Sylow transfer. -/
theorem four_componentPointPerfect_kernel_isTwoGroup
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) :
    IsPGroup 2 ((S.fourFaithfulProjection e).comp (inclusion
      (show S.fourComponentPointPerfect z ≤ L from (map_subtype_le _).trans inf_le_left))).ker := by
  let := S.chosen.actionCentralizer_normal
  let K := S.fourComponentPointPerfect z
  have hKL : K ≤ L := (map_subtype_le _).trans inf_le_left
  let B := K.subgroupOf L
  let d := (subgroupOfEquivOfLe hKL).symm
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  let Q := L ⧸ pCore 2 L
  let π : L →* Q := QuotientGroup.mk' (pCore 2 L)
  let q : Q →* alternatingGroup (Fin 7) := e.toMonoidHom.comp S.chosen.coreToFaithful
  have hqπ : q.comp π = S.fourFaithfulProjection e := rfl
  have hcentral : q.ker ≤ center Q := by
    intro x hx
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    have hl : l ∈ (centralizer (V : Set G)).subgroupOf L :=
      (QuotientGroup.eq_one_iff l).mp (e.map_eq_one_iff.mp hx)
    rw [S.actionCentralizer_eq_centralPreimage e] at hl
    exact hl
  let : IsQuasisimple Q := S.hypothesis.quasisimple
  let c : PerfectCentralCovering.Cover Q (alternatingGroup (Fin 7)) :=
    ⟨q,e.surjective.comp S.chosen.coreToFaithful_surjective,inferInstance,hcentral⟩
  let D := B.map π
  let : Group.IsPerfect D := Group.IsPerfect.map π
  have hD : D.map q = BinaryAlternatingSevenControl.pointStabilizer
      (S.fourFaithfulAction e) (S.fourPointVector z) := by
    rw [map_map,hqπ]
    exact S.four_componentPointPerfect_image e hd z hz
  let a := (BinaryAlternatingSevenControl.pointStabilizerEquivPSL
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective)
      hd (S.vector_nonzero hz)).trans Matrix.PSL3Two.equiv.symm
  have hinj : Function.Injective (q.subgroupMap D) :=
    c.injective_on_perfect_subgroup (pCore_quotient_pCore_eq_bot 2) D (by
      intro p hp ho
      change primeRank p (D.map q) ≤ 1
      rw [hD,primeRank_equiv p a]
      let : Fact p.Prime := ⟨hp⟩
      let P : Sylow p Matrix.PSL3Two.SL := default
      exact P.primeRank_le_one_of_isCyclic
        (Matrix.PSL3Two.odd_sylow_isCyclic hp (fun he => by subst p; norm_num at ho) P))
  let f := (S.fourFaithfulProjection e).comp (inclusion hKL)
  let j : f.ker →* pCore 2 L :=
    ((inclusion hKL).comp f.ker.subtype).codRestrict _ (fun x => by
      apply (QuotientGroup.eq_one_iff _).mp
      have hxD : π (inclusion hKL x.val) ∈ D := mem_map_of_mem π x.val.property
      have hh : q.subgroupMap D ⟨π (inclusion hKL x.val),hxD⟩ = 1 := by
        apply Subtype.ext
        exact x.property
      exact congrArg Subtype.val (hinj (hh.trans (map_one _).symm)))
  exact pCore_isPGroup.of_injective j (by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : pCore 2 L => ((a : L) : G)) hxy)

/-- Restriction of the original faithful projection to the exact point stabilizer. -/
def fourComponentPointProjection
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) : S.fourComponentPointPerfect z →*
      BinaryAlternatingSevenControl.pointStabilizer
        (S.fourFaithfulAction e) (S.fourPointVector z) :=
  ((S.fourFaithfulProjection e).comp (inclusion
    (show S.fourComponentPointPerfect z ≤ L from (map_subtype_le _).trans inf_le_left))).codRestrict _
      (fun x => (S.four_componentPointPerfect_image e hd z hz).le
        (mem_map_of_mem (S.fourFaithfulProjection e) x.property))

theorem fourComponentPointProjection_surjective
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) : Function.Surjective (S.fourComponentPointProjection e hd z hz) := by
  intro a
  obtain ⟨l,hl,he⟩ := (S.four_componentPointPerfect_image e hd z hz).ge a.property
  exact ⟨⟨l,hl⟩,Subtype.ext he⟩

/-- The quotient of the actual L-point residual is the concrete PSL₃(2) carrier. -/
def fourComponentPointCoreEquiv
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) :
    ((S.fourComponentPointPerfect z) ⧸ pCore 2 (S.fourComponentPointPerfect z)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  let := S.chosen.actionCentralizer_normal
  let a := BinaryAlternatingSevenControl.pointStabilizerEquivLinear
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective)
      hd (z := S.fourPointVector z) (by
        exact S.vector_nonzero hz)
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 3) := Finite.of_surjective a a.surjective
  let f := a.toMonoidHom.comp (S.fourComponentPointProjection e hd z hz)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    have he : (S.fourComponentPointProjection e hd z hz).ker =
        ((S.fourFaithfulProjection e).comp (inclusion
          (show S.fourComponentPointPerfect z ≤ L from (map_subtype_le _).trans inf_le_left))).ker := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact S.four_componentPointPerfect_kernel_isTwoGroup e hd z hz
  exact (f.pCoreQuotientEquiv
    (a.surjective.comp (S.fourComponentPointProjection_surjective e hd z hz)) hk).trans
      (((QuotientGroup.quotientMulEquivOfEq
        BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot).trans
          QuotientGroup.quotientBot).trans
            BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective)

/-- The quotient marking is induced by the original projection, followed by
the actual action on V/⟨z⟩. -/
theorem fourComponentPointCoreEquiv_mk
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) (hzv : S.fourPointVector z ≠ 0)
    (x : S.fourComponentPointPerfect z) :
    letI := S.chosen.actionCentralizer_normal
    S.fourComponentPointCoreEquiv e hd z hz (QuotientGroup.mk' _ x) =
      BinaryAlternatingSevenControl.pointStabilizerEquivPSL
        (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective)
          hd hzv (S.fourComponentPointProjection e hd z hz x) := rfl

/-- Relative normality uses the same point-local group as the source. -/
theorem four_componentPointPerfect_normalized {z : G} :
    S.fourPointLocal z ≤ normalizer (S.fourComponentPointPerfect z : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer ({z} : Set G)) (solvableResidual (L ⊓ centralizer ({z} : Set G) : Subgroup G)))
  exact (le_inf inf_le_left (inf_le_right.trans
    (centralizer ({z} : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- Application: the recognized original L-point residual is a genuine
C-component of M_z, with its literal embedding retained. -/
theorem four_componentPointPerfect_component
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    (z : V) (hz : z ≠ 1) :
    ((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent := by
  have hKM : S.fourComponentPointPerfect z ≤ S.fourPointLocal z :=
    (map_subtype_le _).trans (inf_le_inf_right _ L.le_normalizer)
  let d := subgroupOfEquivOfLe hKM
  let q := d.toMonoidHom.pCoreQuotientEquiv (p := 2) d.surjective
    (by rw [d.toMonoidHom.ker_eq_bot d.injective]; exact IsPGroup.of_bot)
  let := Theory.SpecificGroups.LinearHigher.psl_isQuasisimple (F := ZMod 2) (n := 3) (by decide)
  let : IsQuasisimple (((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z)) ⧸
      pCore 2 ((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z))) :=
    IsQuasisimple.of_mulEquiv (q.trans (S.fourComponentPointCoreEquiv e hd z hz)).symm
  let : Group.IsPerfect ((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z)) :=
    Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  have hn : ((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z)).Normal :=
    normal_subgroupOf_of_le_normalizer S.four_componentPointPerfect_normalized
  apply isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2) hn.isSubnormal
  intro N hN hquot
  let := hN
  by_contra hne
  let : Nontrivial ((((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z))) ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect ((((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z))) ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent ((((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z))) ⧸ N) :=
    hquot.isNilpotent
  exact Group.IsPerfect.not_isSolvable
    ((((S.fourComponentPointPerfect z).subgroupOf (S.fourPointLocal z))) ⧸ N) inferInstance

/-- The smaller original residual is contained in the published K_z. -/
theorem four_componentPointPerfect_le_pointPerfect (z : G) :
    S.fourComponentPointPerfect z ≤ S.fourPointPerfect z := by
  let D := S.fourComponentPointPerfect z
  let H := S.fourPointModuleNormalizer z
  have hDH : D ≤ H := (map_subtype_le _).trans
    (inf_le_inf_right _ S.chosen.normalizes)
  let d := (subgroupOfEquivOfLe hDH).symm
  let : Group.IsPerfect (D.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  have htwo : IsPPerfect 2 (D.subgroupOf H) := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial ((D.subgroupOf H) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((D.subgroupOf H) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent ((D.subgroupOf H) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((D.subgroupOf H) ⧸ N) inferInstance
  have hDR : D ≤ S.fourPointResidual z := by
    have hh := map_mono (f := H.subtype) (le_pResidual_of_isPPerfect (D.subgroupOf H) htwo)
    rwa [map_subgroupOf_eq_of_le hDH] at hh
  exact le_map_solvableResidual_of_isPerfect D (S.fourPointResidual z) hDR

/-- To compare the two source residual conventions, it suffices to place
K_z inside the original component L. The opposite inclusion is already proved. -/
theorem four_pointPerfect_eq_componentPointPerfect_of_le
    {z : G} (hKL : S.fourPointPerfect z ≤ L) :
    S.fourPointPerfect z = S.fourComponentPointPerfect z := by
  let := S.four_pointPerfect_perfect z
  apply le_antisymm ?_ (S.four_componentPointPerfect_le_pointPerfect z)
  apply le_map_solvableResidual_of_isPerfect
  exact le_inf hKL ((map_subtype_le _).trans ((map_subtype_le _).trans inf_le_right))

/-- Application to the published residual interface. Its only new local
premise is containment of the normalizer residual in L; this remains an
obligation of qt-d-1233-natural-coordinates, not an asserted source result. -/
theorem fourResidualData_of_pointPerfect_le_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (hKL : S.fourPointPerfect z ≤ L) : S.FourResidualData z := by
  apply S.fourResidualData_of_quotient structural e hd hz hz1 hzT
  rw [S.four_pointPerfect_eq_componentPointPerfect_of_le hKL]
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨S.fourComponentPointCoreEquiv e hd ⟨z,hz⟩
      (fun he => hz1 (congrArg Subtype.val he))⟩⟩

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
