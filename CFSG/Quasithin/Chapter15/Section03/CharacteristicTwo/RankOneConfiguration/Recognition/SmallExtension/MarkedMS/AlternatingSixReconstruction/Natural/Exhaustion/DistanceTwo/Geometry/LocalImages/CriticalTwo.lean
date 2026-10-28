module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.FourImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Cover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Source

/-!
# Excluding the order-four critical image on the original replacement

The whole augmentation cover surjects equivariantly onto the original moved
subgroup before orbit recognition. A larger centralizing image of a critical
four-group acts quadratically on that cover by FourImage. Transport through
the literal opposite-edge embedding then makes [Q_alpha,Z_c] central in
Q_alpha. Residual detection puts the entire graph core in its Frattini-plus-X
section, contrary to the source hypothesis. The previously proved order
dichotomy therefore leaves exactly two.

This discharges the image_two field of LocalImageData. The abelian radical
quotient remains a separate local obligation. No natural complement is used.
Source: MS93 (3.3)(ii)(1)--(2), (3.6), printed pp.866--871. The whole-core
consumer is Assembly/CriticalTwo/Source.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private theorem commutator_central_of_core_quotient
    {M : Type*} [Group M] (W : Subgroup M) [W.Normal] [IsElementaryAbelian 2 W]
    (q : M →* Equiv.Perm (Fin 6))
    (f : core (Fin 6) →ₗ[ZMod 2] Additive W) (hf : Function.Surjective f)
    (hact : ∀ g v, (f (coreRepresentation (Fin 6) (q g) v)).toMul =
      MulAut.conjNormal g (f v).toMul)
    (B : Subgroup M) (hq : IsQuadratic (coreRepresentation (Fin 6)) (B.map q)) :
    ⁅W,B⁆ ≤ centralizer (B : Set M) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb w hw y hy
  obtain ⟨v,hv⟩ := hf (Additive.ofMul (⟨w,hw⟩ : W))
  let δ := coreRepresentation (Fin 6) (q b) v - v
  have he : (f δ).toMul = MulAut.conjNormal b (f v).toMul * (f v).toMul⁻¹ := by
    dsimp only [δ]
    rw [map_sub]
    rw [toMul_sub,div_eq_mul_inv,hact]
  have hfixed : MulAut.conjNormal y (f δ).toMul = (f δ).toMul := by
    rw [←hact]
    change (f (coreRepresentation (Fin 6) (q y)
      (coreRepresentation (Fin 6) (q b) v-v))).toMul = _
    rw [hq _ (mem_map_of_mem q hy) _ (mem_map_of_mem q hb)]
  have heval : ((f δ).toMul : M) = ⁅b,w⁆ := by
    rw [he,hv]
    rfl
  have hh := congrArg Subtype.val hfixed
  change y*((f δ).toMul : M)*y⁻¹=((f δ).toMul : M) at hh
  rw [heval] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
theorem moved_commutator_central_of_quadratic_image (B : Subgroup d.overgroup)
    (hq : IsQuadratic (coreRepresentation (Fin 6))
      (B.map (Recognition.sourceProjection h e hz hn d))) :
    ⁅replacementMoved d,B⁆ ≤ centralizer (B : Set d.overgroup) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  obtain ⟨f,hf,hact⟩ := moved_cover_surjection h e hz hn d
  exact commutator_central_of_core_quotient _ _ f hf hact B hq

include h e hz hn in
/-- Quadraticity of the actual initial-kernel image would centralize its
whole opposite-layer displacement, forcing the forbidden Frattini bound. -/
theorem critical_image_nonquadratic
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)
    (Y : Subgroup d.overgroup) (i : d.overgroup →* FreeAmalgam d.radical)
    (hi : Function.Injective i)
    (hYm : Y.map i = Q d.radical (alpha d.radical))
    (hiW : (replacementMoved d).map i = U d.radical c)
    (hiS : (omegaCenter d.radical).map i = Z d.radical b) :
    ¬ IsQuadratic (coreRepresentation (Fin 6))
      (Y.map (Recognition.sourceProjection h e hz hn d)) := by
  intro hquad
  have hmove := moved_commutator_central_of_quadratic_image h e hz hn d Y hquad
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hZS : Z d.radical c = (replacementMoved d ⊔ omegaCenter d.radical).map i := by
    rw [Subgroup.map_sup,hiW,hiS]
    exact CentralLayer.Z_eq_moving_sup_edge_at h e hz d hc0 hcb
  have hYC : omegaCenter d.radical ≤ centralizer (Y : Set d.overgroup) := by
    intro u hu y hy
    apply hi
    rw [map_mul,map_mul]
    have huZ : i u ∈ Z d.radical b := hiS ▸ mem_map_of_mem i hu
    have hyQ : i y ∈ Q d.radical (alpha d.radical) := hYm ▸ mem_map_of_mem i hy
    have hb0 := DistanceTwo.NaturalCore.edge_color hab
    have hZb : Z d.radical b ≤ centralizer (Q d.radical b : Set (FreeAmalgam d.radical)) := by
      simp only [Z,hb0,Bool.true_eq_false,if_false,edgeOmega]
      exact fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
    exact hZb huZ _ (Q_le_adjacent_h d.radical hb0 hab hyQ)
  have hwhole : ⁅replacementMoved d ⊔ omegaCenter d.radical,Y⁆ ≤
      centralizer (Y : Set d.overgroup) := by
    let := replacementMoved_normal h d
    apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨w,hw,z,hz,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hzy : Commute z y := (hYC hz y hy).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzy.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact hmove (commutator_mem_commutator hw hy)
  have hcentral : ⁅Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
      centralizer (Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm,hZS,←hYm,←map_commutator]
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (map_mul i y x).symm.trans ((congrArg i (hwhole hx y hy)).trans (map_mul i x y))
  have hX : ⁅Q d.radical (alpha d.radical),Z d.radical c⁆ ≤ X d.radical (alpha d.radical) := by
    intro x hx
    apply mem_omegaCenter_iff.mpr
    exact ⟨DistanceTwo.NaturalCore.local_commutator_le_Q (replacementGeometry h d) hb hc hx,
      DistanceTwo.NaturalCore.local_commutator_pow_two (replacementGeometry h d) hb hc hab hcb hx,
      hcentral hx⟩
  exact hlarge (core_le_frattini_of_critical_commutator_le_of_normal_generation
    (replacementGeometry h d) (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) (replacement_edge_centralizer h e hz d)
    (replacement_normal_generation h e hz d) hb hc (hX.trans le_sup_right))

include h e hz hn in
/-- The original source hypotheses rule out the order-four alternative.
No point-core containment or paired-orbit calculation is an extra premise. -/
theorem critical_image_two
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) = 2 := by
  rcases critical_image_two_or_four h e hz hn d hb hlarge hc with ht | hf
  · exact ht
  exfalso
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,hproper,_,hfix,hindex,
      b,i,hi,hab,hcb,hYm,hiW,hiS⟩ :=
    critical_image_data_coordinates h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  let := hAc
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map _
  have hkernel : q.ker = pCore 2 d.overgroup := Recognition.sourceProjection_kernel h e hz hn d
  have hp : IsPGroup 2 (Y.map q) :=
    ((replacement_radical_isPGroup h d).of_injective (inclusion hYR) (inclusion_injective _)).map q
  have hcent : Y.map q ≤ centralizer (A.map q : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul q a y).symm.trans ((congrArg q (hYA hy a ha)).trans (map_mul q y a))
  have hquad := quadratic_core_of_four_image (A.map q) (Y.map q) (hindex.symm.trans hf)
    hp (map_mono hAY) (fun hle => hproper (by simpa only [hkernel] using map_le_map_iff.mp hle))
    hcent hfix
  exact critical_image_nonquadratic h e hz hn d hb hlarge hc hab hcb Y i hi hYm hiW hiS hquad

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
