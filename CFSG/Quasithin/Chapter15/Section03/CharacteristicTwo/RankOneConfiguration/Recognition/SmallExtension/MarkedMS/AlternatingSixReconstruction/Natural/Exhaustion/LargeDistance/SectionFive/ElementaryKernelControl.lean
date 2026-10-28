module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Join

/-!
# Elementary-actor control through the literal edge embedding

Transfer the two-cover fixed-hyperplane calculation to the full seed at an
actual endpoint. An elementary actor with nontrivial transposition image and
fixed index at most two has a fixed-kernel commutator of order at most two,
aligned with the critical line and the whole endpoint fixed subgroup, provided
its full displacement is not controlled by these two commutators.

The injective local embedding preserves the literal radical and core. The
incident central attachment commutes with the actor, so it is retained while
passing from the moving cover to the full seed. No full point-core or
three-pair-image equality is assumed.

Source: MS93 (3.3)(ii)(2) and (5.7), printed pp.866--867 and 919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Fixed-kernel line control on either literal moved cover. -/
theorem elementary_cover_kernel_small_aligned
    (A P : Subgroup d.overgroup) (hAP : A ≤ P) (hel : IsElementaryAbelian 2 P)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hfail : ¬ ⁅replacementMoved d,P⁆ ≤
      ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ ⊔ ⁅replacementMoved d,A⁆) :
    Nat.card (⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ : Subgroup d.overgroup) ≤ 2 ∧
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ ≤
      ⁅replacementMoved d,A⁆ ⊔ (replacementMoved d ⊓ center d.overgroup) := by
  let := replacementMoved_normal h d
  let := hel
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  let K := ⁅F,P⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hKU
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U s.projection s.surjective hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map s.projection) hnA hnat
  have hF : subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hK : subgroupSpace U K = subspaceCommutator (coverAction s)
      (fixedSpace (coverAction s) (A.map s.projection)) (P.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left,hF]
    rfl
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hC : subgroupSpace U (U ⊓ center d.overgroup) = fixedSpace (coverAction s) ⊤ := by
    ext v
    have hh := mem_fixedSpace_image U s.projection s.surjective hker (⊤ : Subgroup d.overgroup) v
    rw [map_top_of_surjective s.projection s.surjective,coe_top,centralizer_univ] at hh
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ center d.overgroup) ↔ _
    simp only [v.toMul.property,true_and]
    exact hh.symm
  have hwhole (B : Subgroup d.overgroup) : subgroupSpace U ⁅U,B⁆ =
      subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker U B le_rfl,hU]
    rfl
  have hfail' : ¬ subspaceCommutator (coverAction s) ⊤ (P.map s.projection) ≤
      subspaceCommutator (coverAction s) (fixedSpace (coverAction s) (zpowers t)) (P.map s.projection) ⊔
        subspaceCommutator (coverAction s) ⊤ (zpowers t) := by
    intro hh
    rw [←he,←hK,←hwhole P,←hwhole A,←subgroupSpace_sup U hKU (commutator_le_left U A)] at hh
    apply hfail
    intro v hv
    exact hh (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)
  have hh := ElementaryKernelModel.small_aligned_of_failure (coverAction s) (cover_model s) t
    (P.map s.projection) (IsElementaryAbelian.map s.projection) ((map_mono hAP) ht) hs hfail'
  rw [←he,←hK] at hh
  have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) := by
    calc Nat.card K = Nat.card (Additive K) := rfl
         _ = Nat.card (subgroupSpace U K) := Nat.card_congr (subgroupSpaceEquiv U K hKU).toEquiv
         _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  refine ⟨?_,?_⟩
  · change Nat.card K ≤ 2
    rw [hcard]
    calc 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh.1
         _ = 2 := rfl
  · have ha := hh.2
    rw [←hwhole A,←hC,←subgroupSpace_sup U (commutator_le_left U A) inf_le_left] at ha
    intro v hv
    exact ha (show Additive.ofMul (⟨v,hKU hv⟩ : U) ∈ subgroupSpace U K from hv)

include s in
private theorem embedded_elementary_kernel_small_aligned {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A P : Subgroup H) (hA : A ≤ d.radical.map i) (hP : P ≤ d.radical.map i)
    (hAP : A ≤ P) (hel : IsElementaryAbelian 2 P)
    (hne : ¬ A ≤ (pCore 2 d.overgroup).map i)
    (hindex : (centralizer (A : Set H)).relIndex ((replacementMoved d).map i) ≤ 2)
    (hfail : ¬ ⁅(replacementMoved d).map i,P⁆ ≤
      ⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ ⊔ ⁅(replacementMoved d).map i,A⁆) :
    Nat.card (⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ : Subgroup H) ≤ 2 ∧
    ⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ ≤
      ⁅(replacementMoved d).map i,A⁆ ⊔ ((replacementMoved d ⊓ center d.overgroup).map i) := by
  let := hel
  let : IsElementaryAbelian 2 (P.comap i) := IsElementaryAbelian.comap_of_injective i hi P
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans (map_le_range i _))
  have hmP : (P.comap i).map i = P := map_comap_eq_self (hP.trans (map_le_range i _))
  have hnA : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    exact hne (hmA ▸ map_mono hh)
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,inf_relIndex_left] at hindex
    exact hindex
  have hmk : (⁅replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup),P.comap i⁆).map i =
      ⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hmA,hmP]
  have hmw (B : Subgroup H) (hB : B ≤ i.range) :
      (⁅replacementMoved d,B.comap i⁆).map i = ⁅(replacementMoved d).map i,B⁆ := by
    rw [map_commutator,map_comap_eq_self hB]
  have hf : ¬ ⁅replacementMoved d,P.comap i⁆ ≤
      ⁅replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup),P.comap i⁆ ⊔
        ⁅replacementMoved d,A.comap i⁆ := by
    intro hh
    apply hfail
    have hh' := map_mono (f := i) hh
    rwa [Subgroup.map_sup,hmk,hmw A (hA.trans (map_le_range i _)),
      hmw P (hP.trans (map_le_range i _))] at hh'
  have hh := elementary_cover_kernel_small_aligned s (A.comap i) (P.comap i)
    (comap_mono hAP) inferInstance hnA hidx hf
  refine ⟨?_,?_⟩
  · have hc := hh.1
    rwa [←card_map_of_injective hi,hmk] at hc
  · have ha := map_mono (f := i) hh.2
    rwa [hmk,Subgroup.map_sup,hmw A (hA.trans (map_le_range i _))] at ha

private theorem elementary_commutator_sup_central {H : Type*} [Group H]
    (U Z P : Subgroup H) (hN : Z ≤ normalizer (U : Set H))
    (hC : Z ≤ centralizer (P : Set H)) : ⁅U ⊔ Z,P⁆ = ⁅U,P⁆ := by
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx r hr
  have hp : x ∈ (U : Set H) * (Z : Set H) := by
    rw [←coe_mul_of_right_le_normalizer_left U Z hN]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hC hz r hr).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

include s in
/-- The same line bound and alignment for the full seed on an actual edge. -/
theorem elementary_edge_kernel_small_aligned (hc : DistanceTwo.CentralLayer d)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A P : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) (hP : P ≤ Q d.radical t)
    (hAP : A ≤ P) (hel : IsElementaryAbelian 2 P)
    (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2)
    (hfail : ¬ ⁅Z d.radical c,P⁆ ≤
      ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ ⊔ ⁅Z d.radical c,A⁆) :
    Nat.card (⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ ≤
      ⁅Z d.radical c,A⁆ ⊔ (Z d.radical c ⊓
        centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [he]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hiG,hiR,hiQ,hiU⟩ := hcoords
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedP := hseed.trans (centralizer_le hP)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  let F := U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have heq : Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) = F ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      sup_comm (U d.radical c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hNF : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ = ⁅F,P⁆ := by
    rw [heq,elementary_commutator_sup_central F _ P hNF hseedP]
  have hwhole (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical t) :
      ⁅Z d.radical c,Y⁆ = ⁅U d.radical c,Y⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      elementary_commutator_sup_central _ _ Y hseedN (hseed.trans (centralizer_le hY))]
  rw [hcomm,hwhole P hP,hwhole A hA] at hfail
  have hh := embedded_elementary_kernel_small_aligned s i hi A P
    (hiR ▸ hA) (hiR ▸ hP) hAP hel (hiQ ▸ hne) (hiU ▸ hindex)
  rw [hiU] at hh
  obtain ⟨hcard,halign⟩ := hh hfail
  refine ⟨hcomm ▸ hcard,?_⟩
  rw [hcomm,hwhole A hA]
  apply halign.trans (sup_le_sup_left ?_ _)
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨DistanceEight.U_le_Z d.radical c (hiU ▸ mem_map_of_mem i hx.1),?_⟩
  intro y hy
  obtain ⟨w,rfl⟩ := hiG ▸ hy
  rw [←map_mul,←map_mul]
  exact congrArg i ((mem_center_iff.mp hx.2) w)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
