module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.WholeMoved
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.Generation
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.ControlledIndex

/-!
# The escaping candidate's parabolic generation contradiction

The literal R-image meets the normal K-image in a Sylow two-subgroup.
On the same whole natural tensor, the Sylow-fixed centralizer and the
normalizer of the marked common-axis actor generate the second factor.
Taking full preimages under the original action map gives the actual
ambient equality K = ⟨C_K(Z ∩ [D,K]), N_K(Â)⟩. The whole moved subgroup
is T-invariant and nonzero, so its intersection with Z is nontrivial.
Canonical centralizer uniqueness and the checked Thompson normalizer lift
put both generators in N_G(L), contradicting the original escaping Y = K.

The final candidate applications assume only the earlier source geometry
and a controlled Thompson index, or the exact GLS normalizer product which
selects it. Proving that product remains with qt-d-1319-ff-contradiction;
qt-d-1317-supplements assembles the earlier canonical geometry. No FF,
tensor, moved-module or generation conclusion is assumed by these applications.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871; GLS G.26.18(a).
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem image_normal_sylow {B Q : Type*} [Group B] [Finite B] [Group Q] [Finite Q]
    (f : B →* Q) (P : Sylow 2 B) (K : Subgroup Q) [K.Normal] (hK : K ≤ f.range) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = ((P : Subgroup B).map f).subgroupOf K := by
  let Pr := P.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  let K' := K.subgroupOf f.range
  let : K'.Normal := inferInstance
  obtain ⟨S,hS⟩ := Pr.exists_subgroupOf_eq_of_normal K'
  let e := subgroupOfEquivOfLe hK
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (S : Subgroup K').map e.toMonoidHom = _
  rw [hS]
  ext k
  constructor
  · rintro ⟨a,⟨b,hb,hba⟩,rfl⟩
    exact ⟨b,hb,congrArg Subtype.val hba⟩
  · rintro ⟨b,hb,hbk⟩
    refine ⟨⟨⟨k,hK k.property⟩,k.property⟩,?_,rfl⟩
    exact ⟨b,hb,Subtype.ext hbk⟩

/-- The original radical image cuts out a Sylow subgroup of the actual
simple second-factor image. -/
theorem common_hat_sylow {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ)
    [(commonModule (T : Subgroup G) L Y j).Normal] :
    ∃ P : Sylow 2 (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)),
      (P : Subgroup _) = (hatImage (T : Subgroup G) L Y j (radicalSylowCentralizer (T : Subgroup G) L)).subgroupOf
        (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) := by
  let B := thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let K := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  let q := secondHatHom (T : Subgroup G) L Y j
  let := hat_commutator_normal w hTH hAH hTL j
  obtain ⟨P,hP⟩ := (thompson_commutator_invariance w hTH hAH hTL j).2.2.2.2
  have hm : (P : Subgroup B).map q = hatImage (T : Subgroup G) L Y j R := by
    have hp : (P : Subgroup B) = R.subgroupOf B := by
      apply Subgroup.map_injective B.subtype_injective
      rw [map_subgroupOf_eq_of_le (show R ≤ B from le_sup_right)]
      exact hP
    rw [hp]
    exact secondHatHom_image le_sup_right
  have hK : K ≤ q.range := by
    change hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ≤ q.range
    rw [←secondHatHom_image (show thompsonCommutator (T : Subgroup G) L Y j ≤ B from le_sup_left)]
    exact map_le_range _ _
  obtain ⟨S,hS⟩ := image_normal_sylow q P K hK
  exact ⟨S,by rw [hS,hm]⟩

/-- Parabolic generation on the same whole moved module, using the Sylow
intersection supplied by the literal R and the original actor normalizer. -/
theorem common_whole_generation {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    {c : CommonHatChief (T : Subgroup G) L Y A j}
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} {t : c.NaturalTensor hc}
    (o : t.OtherNatural) (hz : c.lower = ⊥)
    (haxis : o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2) :
    let K := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
    let R := hatImage (T : Subgroup G) L Y j (radicalSylowCentralizer (T : Subgroup G) L)
    subspaceKernel ((hatRepresentation (T : Subgroup G) L Y j).comp K.subtype)
      (c.upper.toSubmodule ⊓ fixedSpace ((hatRepresentation (T : Subgroup G) L Y j).comp K.subtype)
        (R.subgroupOf K)) ⊤ ⊔
      normalizer ((hatImage (T : Subgroup G) L Y j A).subgroupOf K : Set K) = ⊤ := by
  obtain ⟨P,hP⟩ := common_hat_sylow w hTH hAH hTL j
  have hAK := common_chief_hat_actor_le w hTH hAH hTL ha hA o
  have hAR := map_mono (f := hatMap (T : Subgroup G) L Y j)
    (subgroupOf_mono (commonGroup (T : Subgroup G) L Y j) hA.1)
  have hAP : (hatImage (T : Subgroup G) L Y j A).subgroupOf
      (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ≤ (P : Subgroup _) := by
    rw [hP]
    exact subgroupOf_mono _ hAR
  have hh := o.whole_generation hz hAK P hAP haxis
  rwa [hP] at hh

/-- The whole upper space is the literal ambient commutator subgroup under
its original additive coordinates. -/
theorem common_upper_mem {L Y A : Subgroup G} {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (hD : omegaClosure (T : Subgroup G) L Y j ≤ commonGroup (T : Subgroup G) L Y j)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    (hwhole : c.upper.toSubmodule = subspaceCommutator (hatRepresentation (T : Subgroup G) L Y j) ⊤
      (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)))
    (v : Additive (commonModule (T : Subgroup G) L Y j)) :
    v ∈ c.upper.toSubmodule ↔ ((v.toMul : commonGroup (T : Subgroup G) L Y j) : G) ∈
      ⁅omegaClosure (T : Subgroup G) L Y j, thompsonCommutator (T : Subgroup G) L Y j⁆ := by
  let E := commonGroup (T : Subgroup G) L Y j
  let D := commonModule (T : Subgroup G) L Y j
  let K := thompsonCommutator (T : Subgroup G) L Y j
  have hK : K ≤ E := le_sup_left.trans le_sup_right
  have he := NormalElementaryQuotient.commutatorSpace_eq D (hatMap (T : Subgroup G) L Y j)
    (QuotientGroup.mk'_surjective _) (hatMap_ker (T : Subgroup G) L Y j) (K.subgroupOf E)
  change NormalElementaryQuotient.commutatorSpace D (K.subgroupOf E) =
    subspaceCommutator (hatRepresentation (T : Subgroup G) L Y j) ⊤
      (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) at he
  rw [hwhole,←he]
  change (v.toMul : E) ∈ ⁅D,K.subgroupOf E⁆ ↔ _
  have hm : (⁅D,K.subgroupOf E⁆).map E.subtype = ⁅omegaClosure (T : Subgroup G) L Y j,K⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hK]
    change ⁅((omegaClosure (T : Subgroup G) L Y j).subgroupOf E).map E.subtype,K⁆ = _
    rw [map_subgroupOf_eq_of_le hD]
  rw [←mem_map_iff_mem E.subtype_injective,hm]
  rfl


/-- Lift the parabolic generation to the original escaping K. The first
generator centralizes the literal Z-intersection of its whole moved subgroup. -/
theorem common_lifted_generation {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    {c : CommonHatChief (T : Subgroup G) L Y A j}
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} {t : c.NaturalTensor hc}
    (o : t.OtherNatural) (hz : c.lower = ⊥)
    (hwhole : c.upper.toSubmodule = subspaceCommutator (hatRepresentation (T : Subgroup G) L Y j) ⊤
      (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)))
    (haxis : o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2) :
    thompsonCommutator (T : Subgroup G) L Y j =
      (thompsonCommutator (T : Subgroup G) L Y j ⊓
        centralizer ((⁅omegaClosure (T : Subgroup G) L Y j,thompsonCommutator (T : Subgroup G) L Y j⁆ ⊓
          omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G)) ⊔
      (thompsonCommutator (T : Subgroup G) L Y j ⊓
        liftedActorNormalizer (T : Subgroup G) L Y A j) := by
  let E := commonGroup (T : Subgroup G) L Y j
  let D := omegaClosure (T : Subgroup G) L Y j
  let K := thompsonCommutator (T : Subgroup G) L Y j
  let Kh := hatImage (T : Subgroup G) L Y j K
  let Rh := hatImage (T : Subgroup G) L Y j (radicalSylowCentralizer (T : Subgroup G) L)
  let Ah := hatImage (T : Subgroup G) L Y j A
  let ρ := hatRepresentation (T : Subgroup G) L Y j
  let U := ⁅D,K⁆ ⊓ omegaOneCenterAmbient (T : Subgroup G)
  have hd := omegaClosure_geometry w hTH hAH hTL j
  have hDE : D ≤ E := hd.2.1.trans le_sup_right
  have hKE : K ≤ E := le_sup_left.trans le_sup_right
  have hWD : ⁅D,K⁆ ≤ D := le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hd.2.2.1)
  let f : K →* Kh := ((hatMap (T : Subgroup G) L Y j).comp (inclusion hKE)).codRestrict Kh
    (fun k => mem_map_of_mem _ k.property)
  have hf : Function.Surjective f := by
    rintro ⟨x,⟨k,hk,rfl⟩⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  let F := subspaceKernel (ρ.comp Kh.subtype)
    (c.upper.toSubmodule ⊓ fixedSpace (ρ.comp Kh.subtype) (Rh.subgroupOf Kh)) ⊤
  let N := normalizer (Ah.subgroupOf Kh : Set Kh)
  have hgen : F ⊔ N = ⊤ := common_whole_generation w hTH hAH hTL ha hA o hz haxis
  have hfix : (F.comap f).map K.subtype ≤ centralizer (U : Set G) := by
    rintro _ ⟨k,hk,rfl⟩ u hu
    let v : Additive (commonModule (T : Subgroup G) L Y j) :=
      Additive.ofMul ⟨⟨u,hDE (hWD hu.1)⟩,hWD hu.1⟩
    have hvU : v ∈ c.upper.toSubmodule := (common_upper_mem hDE c hwhole v).mpr hu.1
    have hvR : v ∈ fixedSpace (ρ.comp Kh.subtype) (Rh.subgroupOf Kh) := by
      intro r
      obtain ⟨b,hb,he⟩ := r.property
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (((ρ (r.val : HatGroup (T : Subgroup G) L Y j) v).toMul : E) : G) = u
      change hatMap (T : Subgroup G) L Y j b = (r.val : HatGroup (T : Subgroup G) L Y j) at he
      rw [←he,hatRepresentation_apply]
      have hcomm := ((mem_omegaOneCenterAmbient_iff _ _).mp hu.2).2.2 b
        (radicalSylowCentralizer_le _ _ hb)
      exact mul_inv_eq_iff_eq_mul.mpr hcomm
    have he := hk.2 v ⟨hvU,hvR⟩
    have hv := congrArg (fun z : Additive (commonModule (T : Subgroup G) L Y j) =>
      ((z.toMul : E) : G)) he
    change (((ρ (hatMap (T : Subgroup G) L Y j (inclusion hKE k)) v).toMul : E) : G) = u at hv
    rw [hatRepresentation_apply] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hAK := common_chief_hat_actor_le w hTH hAH hTL ha hA o
  have hnorm : (N.comap f).map K.subtype ≤ liftedActorNormalizer (T : Subgroup G) L Y A j := by
    rintro _ ⟨k,hk,rfl⟩
    have hn : (f k : HatGroup (T : Subgroup G) L Y j) ∈ normalizer (Ah : Set _) := by
      change f k ∈ normalizer (Ah.subgroupOf Kh : Set Kh) at hk
      rw [←subgroupOf_normalizer_eq hAK] at hk
      exact hk
    exact ⟨⟨k,mem_sup_left k.property⟩,hn,rfl⟩
  have hjoin : F.comap f ⊔ N.comap f = ⊤ := by
    rw [comap_sup_eq f F N hf,hgen,comap_top]
  have hm := congrArg (Subgroup.map K.subtype) hjoin
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hm
  apply le_antisymm
  · calc
      K = (F.comap f).map K.subtype ⊔ (N.comap f).map K.subtype := hm.symm
      _ ≤ _ := sup_le_sup (le_inf (map_subtype_le _) hfix) (le_inf (map_subtype_le _) hnorm)
  · exact sup_le inf_le_left inf_le_left


/-- The whole moved subgroup meets the original omega-center nontrivially,
so canonical uniqueness controls its seed centralizer. -/
theorem common_moved_seed_centralizer_le (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H C Y : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j) :
    centralizer ((⁅omegaClosure (T : Subgroup G) L Y j,thompsonCommutator (T : Subgroup G) L Y j⁆ ⊓
      omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let D := omegaClosure (T : Subgroup G) L Y j
  let K := thompsonCommutator (T : Subgroup G) L Y j
  let W := ⁅D,K⁆
  let U := W ⊓ omegaOneCenterAmbient (T : Subgroup G)
  have hd := omegaClosure_geometry w hTH hAH hTL j
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  have hDe := omegaClosure_elementary_le_radical h w hH hTH hAH hTL hcore j
  have hWD : W ≤ D := le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hd.2.2.1)
  have hWT : W ≤ (T : Subgroup G) := hWD.trans (hDe.2.trans (radicalSylowCentralizer_le _ _))
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change W.map (MulAut.conj g).toMonoidHom = W
    have hDmap : D.map (MulAut.conj g).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp ((le_sup_right.trans hd.2.2.2) hg)
    have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp ((le_sup_right.trans hi.2.2.1) hg)
    rw [map_commutator,hDmap,hKmap]
  have hWne : W ≠ ⊥ := by
    intro he
    exact ha.commutator_nontrivial ((hat_image_eq_bot_iff (T : Subgroup G) L Y K j
      (hd.2.1.trans le_sup_right) (le_sup_left.trans le_sup_right)).mpr he)
  have hUne : U ≠ ⊥ := by
    obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp (inf_centerIn_ne_bot T.isPGroup' hWne hWT hTW)
    let : IsElementaryAbelian 2 D := hDe.1
    have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G)
          (hWD z.property.1),z.property.2.2⟩
    intro he
    exact hz (Subtype.ext (mem_bot.mp (he ▸ (show (z : G) ∈ U from ⟨z.property.1,hzZ⟩))))
  have hu : U ≤ omegaOneCenterAmbient (T : Subgroup G) := inf_le_right
  have hc := (nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).2.2
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)).isPGroup.to_le hu,rfl⟩
  obtain ⟨N,hN,hmax⟩ := Finite.exists_le_maximal hloc
  have hcent := (centralizer_le_normalizer (U : Set G)).trans hN
  exact hcent.trans_eq (hc N hmax ((centralizer_le hu).trans hcent))

/-- The original FF and generation contradiction is complete for either
controlled Thompson index. Selection of such an index remains separate. -/
theorem candidate_false_of_controlled_index (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) : False := by
  obtain ⟨_,Y,w,n,rest⟩ :=
    candidate_whole_tensor h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,rest⟩ := rest
  let := e
  obtain ⟨ha,hKY,_,A,hA,_,_,_,_,hnorm,c,_,hc,t,o,hzero,hwhole,_,_,haxis⟩ := rest
  let := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  let := o.second.isSimpleGroup
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hgen := common_lifted_generation w hTH (hAC.trans hC.1) hTL ha hA o hzero hwhole haxis
  have hcent := common_moved_seed_centralizer_le h hmany hs hL hn w hH hTH
    (hAC.trans hC.1) hTL ha
  have hKM := hgen.le.trans (sup_le (inf_le_right.trans hcent) (inf_le_right.trans hnorm))
  rw [hKY] at hKM
  exact w.witness.outside hKM


/-- Literal candidate application with the exact GLS normalizer product as
the sole remaining Thompson-selection premise. The FF and final generation
steps are discharged internally. -/
theorem candidate_false_of_controlled_factorization (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hf : ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer (T : Subgroup G) L)) : False := by
  obtain ⟨j,hj,_,_,hN⟩ := controlledIndex_of_factorization h hmany hs hL hn p ho hd hf
  exact candidate_false_of_controlled_index h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
