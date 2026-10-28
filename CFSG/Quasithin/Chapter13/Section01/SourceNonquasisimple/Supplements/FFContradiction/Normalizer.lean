module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.ActorLift
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NormalizerImage
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# Lifting the tensor actor normalizer to the original group

The simple quotient of the escaping Y detects exactly O₂(Y) as its kernel
on D. Since KR = YR has a two-group supplement, the whole restricted kernel
is a two-group and lies in its original Sylow R. The inverse image of the
Thompson image is therefore intermediate between J_j(R) and R. Thompson
heredity lifts its full normalizer into N_G(J_j(R)), hence into N_G(L).
The literal candidate retains the same common chief section, tensor maps,
original actor and common-axis marking throughout this lift.

The controlled index, whole moved-module identification and generation
contradiction remain with qt-d-1319-ff-contradiction. Earlier geometry is
assembled by qt-d-1317-supplements. Source: Aschbacher--Smith 13.1.9, p.871.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original action map restricted to KR. -/
@[expose] def secondHatHom (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] :
    (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L : Subgroup G) →*
      HatGroup T L Y j :=
  (hatMap T L Y j).comp (inclusion (show
    thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L ≤ commonGroup T L Y j from le_sup_right))

/-- The kernel on the original Y is exactly O₂(Y), using its actual simple
quotient and nontrivial action. -/
theorem common_escaping_hat_ker (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (XiQuotient Y)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hKY : thompsonCommutator (T : Subgroup G) L Y j = Y)
    (hYE : Y ≤ commonGroup (T : Subgroup G) L Y j) :
    ((hatMap (T : Subgroup G) L Y j).comp (inclusion hYE)).ker = pCore 2 Y := by
  let f := (hatMap (T : Subgroup G) L Y j).comp (inclusion hYE)
  have hc := escaping_core_centralizes_omegaClosure h w hH hTH hAH hTL hcore j
  have hk : pCore 2 Y ≤ f.ker := by
    intro y hy
    change hatMap (T : Subgroup G) L Y j ⟨y.val,hYE y.property⟩ = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro d hd
    exact Subtype.ext (hc (mem_map_of_mem Y.subtype hy) d hd)
  let q := QuotientGroup.lift (pCore 2 Y) f hk
  have hq : q.ker = ⊥ := by
    rcases q.normal_ker.eq_bot_or_eq_top with hz | ht
    · exact hz
    · exfalso
      apply ha.commutator_nontrivial
      rw [hKY]
      apply bot_unique
      rintro _ ⟨y,hy,rfl⟩
      have he : q (QuotientGroup.mk' (pCore 2 Y) ⟨y.val,hy⟩) = 1 := ht.ge (mem_top _)
      exact he
  apply le_antisymm _ hk
  intro y hy
  apply (QuotientGroup.eq_one_iff y).mp
  have he : q (QuotientGroup.mk' (pCore 2 Y) y) = 1 := hy
  exact mem_bot.mp (hq.le he)

/-- The kernel of KR on the original D lies in the original Sylow R. -/
theorem secondHatHom_ker_le_radical (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (XiQuotient Y)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hKY : thompsonCommutator (T : Subgroup G) L Y j = Y) :
    (secondHatHom (T : Subgroup G) L Y j).ker ≤
      (radicalSylowCentralizer (T : Subgroup G) L).subgroupOf
        (thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer (T : Subgroup G) L) := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let B := thompsonCommutator (T : Subgroup G) L Y j ⊔ R
  let E := commonGroup (T : Subgroup G) L Y j
  let q := secondHatHom (T : Subgroup G) L Y j
  have hYB : Y ≤ B := hKY ▸ (show thompsonCommutator (T : Subgroup G) L Y j ≤ B from le_sup_left)
  have hYE : Y ≤ E := hYB.trans le_sup_right
  have hBY : B ≤ normalizer (Y : Set G) := by
    change thompsonCommutator (T : Subgroup G) L Y j ⊔ R ≤ _
    rw [hKY]
    exact sup_le Y.le_normalizer ((radicalSylowCentralizer_le _ _).trans
      (hTH.trans ((normal_subgroupOf_iff_le_normalizer w.witness.le_overgroup).mp w.witness.normal)))
  let : (Y.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hBY
  have hkerY := common_escaping_hat_ker h w hH hTH hAH hTL hcore ha hKY hYE
  have hpY : IsPGroup 2 (q.comp (Y.subgroupOf B).subtype).ker := by
    let e := subgroupOfEquivOfLe hYB
    let f := (hatMap (T : Subgroup G) L Y j).comp (inclusion hYE)
    have hp : IsPGroup 2 f.ker := hkerY.symm ▸ pCore_isPGroup
    exact hp.comap_of_injective e.toMonoidHom e.injective
  have hp : IsPGroup 2 q.ker := q.kernel_isPGroup_of_normal_supplement
    (Y.subgroupOf B) (R.subgroupOf B)
    ((T.isPGroup'.to_le (radicalSylowCentralizer_le _ _)).comap_subtype)
    (by
      rw [←subgroupOf_sup hYB le_sup_right]
      have he : Y ⊔ R = B := congrArg (fun U : Subgroup G => U ⊔ R) hKY.symm
      rw [he]
      exact subgroupOf_self B) hpY
  obtain ⟨P,hP⟩ := (thompson_commutator_invariance w hTH hAH hTL j).2.2.2.2
  have hkerP := hp.le_sylow_of_normal P
  intro x hx
  have hxR := mem_map_of_mem B.subtype (hkerP hx)
  rwa [hP] at hxR


/-- The restriction to KR has the same literal subgroup images. -/
theorem secondHatHom_image {T L Y X : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal]
    (hX : X ≤ thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) :
    (X.subgroupOf (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)).map
      (secondHatHom T L Y j) = hatImage T L Y j X := by
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨inclusion (show thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L ≤
      commonGroup T L Y j from le_sup_right) b,hb,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b.val,hX hb⟩,hb,rfl⟩

/-- The full inverse image in KR of the actor-image normalizer. -/
@[expose] def liftedActorNormalizer (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] : Subgroup G :=
  ((normalizer (hatImage T L Y j A : Set (HatGroup T L Y j))).comap
    (secondHatHom T L Y j)).map
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).subtype

/-- Identifying the original Thompson image controls the full inverse image
of its normalizer, rather than only a chosen lift of each element. -/
theorem common_actor_normalizer_le (h : Hypothesis1311 T)
    {L H C Y A : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (XiQuotient Y)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hKY : thompsonCommutator (T : Subgroup G) L Y j = Y)
    (hJA : hatImage (T : Subgroup G) L Y j
        (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j) =
      hatImage (T : Subgroup G) L Y j A)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    liftedActorNormalizer (T : Subgroup G) L Y A j ≤
      normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ∧
    liftedActorNormalizer (T : Subgroup G) L Y A j ≤ normalizer (L : Set G) := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let B := thompsonCommutator (T : Subgroup G) L Y j ⊔ R
  have hj := thompson_index_lt_of_normalizer_control Y R (normalizer (L : Set G))
    w.witness.outside hN
  have hn := normalizer_image_thompson_le B R le_sup_right hj
    (secondHatHom (T : Subgroup G) L Y j)
    (secondHatHom_ker_le_radical h w hH hTH hAH hTL hcore ha hKY)
  rw [secondHatHom_image ((thompsonJ_le R j).trans le_sup_right),hJA] at hn
  exact ⟨hn,hn.trans hN⟩

/-- The literal candidate has normalizer control on the very same natural
tensor and the same original Thompson image. -/
theorem candidate_tensor_actor_normalizer (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    j = 1 ∧ ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧
            rank (hatImage (T : Subgroup G) L Y j A) = 2 ∧
            fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) = 3 ∧
            hatImage (T : Subgroup G) L Y j (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j) =
              hatImage (T : Subgroup G) L Y j A ∧
            liftedActorNormalizer (T : Subgroup G) L Y A j ≤ normalizer (L : Set G) ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
                hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
                  hatImage (T : Subgroup G) L Y j A⁆ = ⊥,
                  ∃ t : c.NaturalTensor hc, ∃ o : t.OtherNatural,
                    o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
                      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2 := by
  obtain ⟨hj1,Y,w,n,rest⟩ :=
    candidate_thompson_image_eq_actor h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,rest⟩ := rest
  let := e
  obtain ⟨ha,hKY,h3,A,hA,hAn,hr,hcod,hJA,c,hε,hc,t,o,haxis⟩ := rest
  have hsimple : IsSimpleGroup (XiQuotient Y) := by
    obtain ⟨F,hF,hfin,_,⟨f⟩⟩ := h3
    let := hF
    let := hfin
    let := Atlas.psl_simple_high_rank (F := F) 3 (by decide)
    exact f.isSimpleGroup
  let := hsimple
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  have hnorm := common_actor_normalizer_le h w hH hTH (hAC.trans hC.1) hTL hcore ha hKY hJA hN
  exact ⟨hj1,Y,w,n,e,ha,hKY,h3,A,hA,hAn,hr,hcod,hJA,hnorm.2,c,hε,hc,t,o,haxis⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
