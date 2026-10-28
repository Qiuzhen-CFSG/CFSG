module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeResidualRotation

/-!
# Aligned displacement fixes the full critical kernel

On the actual moved cover, suppose an actor's whole displacement is contained
in the original critical line times the endpoint center. Project to the
faithful natural quotient. The invariant symplectic pairing recovers the
fixed hyperplane from the moved line. Its pointwise fixer has order two,
so the new actor image lies in the original critical transposition image.
Lifting through the entire two-core shows that the full critical kernel is
fixed, including every central attachment. This proves the aligned exclusion
on both the order-sixteen and order-thirty-two covers without assuming a
three-pair image, a splitting, or the disappearance of the central kernel.

Transport through the literal vertex embedding retains the relative endpoint
center, the original critical commutator, and the full seed kernel. Applying
this to the retained residual rotation in `CubeResidualRotation` forces the
same nonzero line outside the original critical line times the endpoint
center. The neighbor transporter, cubic, path orientation, residual element,
rotated path and inverse-conjugation convention are all unchanged.

This proves the model-exclusion half of MS93 (5.8). The other half, deriving
alignment from the selected nonnormalization/generation data, remains open.
In particular this module does not exclude trapped radii or prove the final
large-distance bound. No control alternative is discarded.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.0), (3.3) and (5.8), printed pp.859,866--867,920. The factor R in
R Z(G_alpha') is the original critical commutator, not the MS2(a) radical.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive

private theorem small_image_le_of_moved_le
    (A J : Subgroup (Equiv.Perm (Fin 6))) (hA : A ≠ ⊥)
    (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1)
    (hle : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ J ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) : J ≤ A := by
  have hfix : fixedSpace (naturalRepresentation (Fin 6)) A ≤
      fixedSpace (naturalRepresentation (Fin 6)) J := by
    rw [NaturalPairing.moved_eq_fixed_orthogonal,
      NaturalPairing.moved_eq_fixed_orthogonal] at hle
    have hh := LinearMap.BilinForm.orthogonal_le (B := NaturalPairing.form) hle
    simpa only [LinearMap.BilinForm.orthogonal_orthogonal
      NaturalPairing.form_nondegenerate NaturalPairing.form_alt.isRefl] using hh
  have hsup : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ J) =
      fixedSpace (naturalRepresentation (Fin 6)) A := by
    exact ((naturalRepresentation (Fin 6)).invariants_comp_sup A J).trans
      (inf_eq_left.mpr hfix)
  have hsupsmall : fixedCodim (naturalRepresentation (Fin 6)) (A ⊔ J) ≤ 1 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace _ (A ⊔ J)) ≤ 1
    rw [hsup]
    exact hsmall
  have hsupne : A ⊔ J ≠ ⊥ := fun he => hA (le_bot_iff.mp (he ▸ le_sup_left))
  obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A ⊔ J) hsupne hsupsmall
  have hc : Nat.card (A ⊔ J : Subgroup (Equiv.Perm (Fin 6))) = 2 := by rw [he,Nat.card_zpowers,ht.orderOf]
  have hAc := (one_lt_card_iff_ne_bot A).mpr hA
  have heq : A = A ⊔ J := eq_of_le_of_card_ge le_sup_left (by omega)
  exact heq ▸ le_sup_right

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Full displacement into the critical line times the actual central
attachment forces the actor into the original small critical image. -/
theorem cover_aligned_actor_le (A J : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (halign : ⁅replacementMoved d,J⁆ ≤
      ⁅replacementMoved d,A⁆ ⊔ center d.overgroup) :
    J ≤ pCore 2 d.overgroup ⊔ A := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U s.projection s.surjective hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      π (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hm (B : Subgroup d.overgroup) :
      (subgroupSpace U ⁅U,B⁆).map π =
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (B.map s.projection) := by
    have hB : subgroupSpace U ⁅U,B⁆ =
        subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
      rw [subgroupSpace_commutator U s.projection s.surjective hker U B le_rfl,hU]
      rfl
    rw [hB]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id _) π (fun g v => (coverMap_equivariant s g v).symm)
      (B.map s.projection) ⊤
    have hπ : π.range = ⊤ := LinearMap.range_eq_top.mpr
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    simpa only [Submodule.map_top,hπ,map_id] using hh.symm
  have hcentral : (subgroupSpace U (U ⊓ center d.overgroup)).map π = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨v,hv,rfl⟩
    change π v=0
    have hh : v.toMul ∈ (coverProjection h e hz hn d).ker := by
      rw [coverProjection_kernel_center s]
      exact hv.2
    exact MonoidHom.mem_ker.mp hh
  have halign' : ⁅U,J⁆ ≤ ⁅U,A⁆ ⊔ (U ⊓ center d.overgroup) := by
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := mem_sup_of_normal_right.mp (halign hx)
    have hyU : y ∈ U := (commutator_le_left U A) hy
    have hzU : z ∈ U := by
      have hh := U.mul_mem (U.inv_mem hyU) ((commutator_le_left U J) hx)
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left hy) (mem_sup_right ⟨hzU,hz⟩)
  have hmove : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (J.map s.projection) ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection) := by
    rw [←hm J,←hm A]
    have hh : subgroupSpace U ⁅U,J⁆ ≤ subgroupSpace U (⁅U,A⁆ ⊔ (U ⊓ center d.overgroup)) :=
      fun v hv => halign' hv
    have hmap := Submodule.map_mono (f := π) hh
    rwa [subgroupSpace_sup U (commutator_le_left U A) inf_le_left,
      Submodule.map_sup,hcentral,sup_bot_eq] at hmap
  have him := small_image_le_of_moved_le (A.map s.projection) (J.map s.projection) hnA hnat hmove
  have hh := (le_comap_map s.projection J).trans (comap_mono him)
  rw [comap_map_eq,s.projection_kernel] at hh
  exact hh.trans_eq (sup_comm _ _)

include s in
/-- Alignment excludes simultaneous nonzero full-cover and fixed-kernel
movement, on both possible covers, without a three-pair-image assumption. -/
theorem cover_aligned_fixed_commutator_eq_bot (A J : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (halign : ⁅replacementMoved d,J⁆ ≤
      ⁅replacementMoved d,A⁆ ⊔ center d.overgroup) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),J⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact (cover_aligned_actor_le s A J hne hindex halign).trans (sup_le
    ((moved_centralizer s).ge.trans (centralizer_le inf_le_left))
    (le_centralizer_iff.mpr inf_le_right))

private theorem map_center_eq_range_inf_centralizer {M N : Type*} [Group M] [Group N]
    (i : M →* N) (hi : Function.Injective i) :
    (center M).map i = i.range ⊓ centralizer (i.range : Set N) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨⟨x,rfl⟩,?_⟩
    rintro y ⟨z,rfl⟩
    simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx) z)
  · rintro x ⟨⟨y,rfl⟩,hc⟩
    refine ⟨y,mem_center_iff.mpr ?_,rfl⟩
    intro z
    apply hi
    simpa only [map_mul] using hc (i z) ⟨z,rfl⟩

include s in
/-- Alignment with the original critical line and the full endpoint center
controls the actual actor in the endpoint stabilizer. -/
theorem small_critical_aligned_actor_le (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (J : Subgroup (FreeAmalgam d.radical)) (hJ : J ≤ stabilizer d.radical z)
    (halign : ⁅U d.radical z,J⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
      (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    J ≤ Q d.radical z ⊔ Z d.radical a := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc z p.end_color
  let A := (Z d.radical a).comap i
  let P := J.comap i
  have hA : Z d.radical a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hmA : A.map i = Z d.radical a := map_comap_eq_self hA
  have hmP : P.map i = J := map_comap_eq_self (hJ.trans_eq hir.symm)
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro he
    apply p.critical.2
    have hh := map_mono (f := i) he
    rwa [hmA,hiQ] at hh
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color
    (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hline : (⁅replacementMoved d,A⁆).map i = ⁅Z d.radical a,Z d.radical z⁆ := by
    rw [map_commutator,hiU,hmA,small_critical_moving_commutator_eq s hc q hs,
      commutator_comm]
  have hcenter : (center d.overgroup).map i = stabilizer d.radical z ⊓
      centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [map_center_eq_range_inf_centralizer i hi,hir]
  have ha : ⁅replacementMoved d,P⁆ ≤ ⁅replacementMoved d,A⁆ ⊔ center d.overgroup := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [Subgroup.map_sup,map_commutator,hiU,hmP,hline,hcenter]
  have hh := map_mono (f := i) (cover_aligned_actor_le s A P hnA hidx ha)
  rwa [Subgroup.map_sup,hmP,hiQ,hmA] at hh

include s in
/-- The full critical kernel is fixed by every aligned endpoint actor.
No fixed-kernel identification or removal of a central attachment is assumed. -/
theorem small_critical_aligned_kernel_commutator_eq_bot (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (J : Subgroup (FreeAmalgam d.radical)) (hJ : J ≤ stabilizer d.radical z)
    (halign : ⁅U d.radical z,J⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
      (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    ⁅Z d.radical z ⊓ Q d.radical a,J⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply (small_critical_aligned_actor_le s hc p hsmall J hJ halign).trans
  apply sup_le
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z p.end_color))).trans (centralizer_le inf_le_left)
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le inf_le_right)

include e hz hn in
/-- The original trapped-radius selector and the same residual rotation force
the selected line outside the original critical line times the endpoint
center. This discharges the model-exclusion half of MS93 (5.8); deriving the
opposite alignment from the selector remains the separate source obligation. -/
theorem nonsylow_trapped_radius_rotated_unaligned_line_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (htrapped : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ∃ delta, Adjacent d.radical delta (p.walk.getVert 1) ∧
      (¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        ∃ g ∈ stabilizer d.radical (alpha d.radical),
          act d.radical g (p.walk.getVert 1)=t ∧
          Adjacent d.radical (act d.radical g delta) t ∧
          ∃ x ∈ Ltilde d.radical (alpha d.radical),
            x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
            x^3 ∈ Q d.radical (alpha d.radical) ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
              ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
                (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
              (¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
                Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
              let H := ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆
              Nat.card H=2 ∧
              H ≤ Z d.radical (act d.radical g delta) ⊓ Z d.radical z ∧
              H ≤ Z d.radical t ⊓ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧
              H ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical (q.walk.getVert (q.walk.length-2)) ∧
              H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
              (¬ H ≤ centralizer (stabilizer d.radical (act d.radical g delta) : Set (FreeAmalgam d.radical))) ∧
              H ≤ centralizer (stabilizer d.radical (q.walk.getVert (q.walk.length-2)) : Set (FreeAmalgam d.radical)) ∧
              ∃ k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2)),
                act d.radical k (q.walk.getVert (q.walk.length-1))=q.walk.getVert (q.walk.length-3) ∧
                ∃ r : CriticalPath d.radical (replacementGeometry h d)
                    (act d.radical g delta) (act d.radical k z),
                  r.walk.getVert 1=t ∧
                  (∀ i ≤ q.walk.length-3, r.walk.getVert (i+2)=q.walk.getVert i) ∧
                  (Q d.radical (act d.radical k z)).relIndex (Z d.radical (act d.radical g delta))=2 ∧
                  (Q d.radical (act d.radical g delta)).relIndex (Z d.radical (act d.radical k z))=2 ∧
                  ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),
                    Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H ∧
                  ⁅Z d.radical z,Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H ∧
                  ⁅U d.radical z,Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H ∧
                  ¬ H ≤ ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ⊔
                    (stabilizer d.radical z ⊓
                      centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨delta,hdelta,hel,t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hnorm,
    hcard,hseed,hedge,hmiddle,hcent,hncent,hpre,k,hk,hkt,r,hrt,hover,hi,hj,hK,hZ,hU⟩ :=
      nonsylow_trapped_radius_rotated_line_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped
  refine ⟨delta,hdelta,hel,t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hnorm,
    hcard,hseed,hedge,hmiddle,hcent,hncent,hpre,k,hk,hkt,r,hrt,hover,hi,hj,hK,hZ,hU,?_⟩
  intro halign
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    have hh := nonsylow_trapped_radius_predecessor_kernels_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped q
    rw [hh.2.1]
    decide
  have hJ : Z d.radical (act d.radical k⁻¹ (act d.radical g delta)) ≤
      stabilizer d.radical z := by
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom)
      (Z_le_stabilizer_of_dist_le (act d.radical g delta) _ r.critical.1.le)
    have h1 := Z_act d.radical k⁻¹ (act d.radical g delta)
    have h2 := stabilizer_act d.radical k⁻¹ (act d.radical k z)
    rw [inv_inv] at h1 h2
    have hcancel : act d.radical k⁻¹ (act d.radical k z) = z := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rwa [←h1,←h2,hcancel] at hh
  have hz0 := small_critical_aligned_kernel_commutator_eq_bot s hc q hsmall
    (Z d.radical (act d.radical k⁻¹ (act d.radical g delta))) hJ (hU ▸ halign)
  rw [hK] at hz0
  rw [hz0,card_bot] at hcard
  omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
