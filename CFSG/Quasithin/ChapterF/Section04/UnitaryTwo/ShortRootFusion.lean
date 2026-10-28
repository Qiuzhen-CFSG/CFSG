module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootQuotient
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.FullPlainFusion
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.LongPlacement
public import Theory.GroupTheory.WeakClosurePairFusion

/-!
# The unique fixed long root in the actual short-root centralizer

The existing ordinary involution fusion reflects fusion on the full plane
endpoint by conjugating its involutions into the marked overlap Sylow.
The literal rank-one matrix calculation then places every long-root
conjugate in the plane radical. Burnside's simultaneous fusion correction
for this weakly closed abelian radical retains both the long and short
marks. It forces the fusion in C_G(t) to occur in X_t.

Together with the actual common-centralizer bound, this proves the unique
fixed coset needed in Aschbacher–Smith F.4.42, printed p.295. All marking,
normalizer and centralizer hypotheses are the original source hypotheses.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootFusion
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient
local notation "hn" => Nat.le_refl 1
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "P" => pointParabolic 1 hn

private theorem right_sylow_placement (a : R) (ha : a ^ 2 = 1) :
    ∃ r : R, ∃ b : B, b ∈ InvolutionFusion.S0 ∧
      r * a * r⁻¹ = (amalgam 1 hn).right b := by
  let T := (projectiveSylow 1 hn).subtype (projectiveSylow_le_parabolics 1 hn).2
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨r,hr⟩ := MulAction.exists_smul_eq R Q T
  have hb : r * a * r⁻¹ ∈ (T : Subgroup R) := by
    rw [← hr]
    exact ⟨a,hQ (mem_zpowers a),rfl⟩
  let b : B := ⟨(r * a * r⁻¹).val,upperProjective_le_overlap 1 hn hb⟩
  exact ⟨r,b,hb,rfl⟩

variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem right_involution_fusion_reflects
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (a b : R) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : IsConj (i (c.right a)) (i (c.right b))) : IsConj a.val b.val := by
  obtain ⟨r,x,hx,hxe⟩ := right_sylow_placement a ha
  obtain ⟨s,y,hy,hye⟩ := right_sylow_placement b hb
  have hx2 : x ^ 2 = 1 := by
    apply right_injective 1 hn
    rw [map_pow,map_one,← hxe]
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj r) ha
  have hy2 : y ^ 2 = 1 := by
    apply right_injective 1 hn
    rw [map_pow,map_one,← hye]
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj s) hb
  have hright (v : B) : i (c.middle v) = i (c.right ((amalgam 1 hn).right v)) :=
    congrArg i (DFunLike.congr_fun c.compatible v)
  have hax : IsConj (i (c.right a)) (i (c.middle x)) := by
    rw [hright]
    exact (i.comp c.right).map_isConj (isConj_iff.mpr ⟨r,hxe⟩)
  have hby : IsConj (i (c.right b)) (i (c.middle y)) := by
    rw [hright]
    exact (i.comp c.right).map_isConj (isConj_iff.mpr ⟨s,hye⟩)
  have hxy := FullPlainFusion.ambient_fusion_reflects c i hi longPoint longPoint_order
    longPoint_mem_root hc hnorm x y hx hy hx2 hy2 (hax.symm.trans (hab.trans hby))
  have haxM : IsConj a.val x.val := isConj_iff.mpr ⟨r.val,congrArg Subtype.val hxe⟩
  have hbyM : IsConj b.val y.val := isConj_iff.mpr ⟨s.val,congrArg Subtype.val hye⟩
  exact haxM.trans (hxy.trans hbyM.symm)



open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "X" => shortCentralizer F σ hσ

def matrixPlaneEquiv : L ≃* R :=
  (L2ProjectIso 1 hn).trans (MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local.symm)

omit [Finite G] in
theorem matrixPlaneEquiv_image (a : L) :
    i (c.right (matrixPlaneEquiv a)) = matrixPlaneEmbedding c i a := rfl

def modelLong : L := longLocal F σ hσ

private theorem longLocal_sq : modelLong ^ 2 = 1 :=
  congrArg (fun q : radical F σ hσ => q.val) (radical_sq F σ hσ
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))))

/-- Reflection of source fusion places every long-root conjugate in the
plane endpoint in its original radical. -/
theorem source_long_conjugate_mem_radical
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (a : L) (ha : IsConj (i (c.left longPoint)) (matrixPlaneEmbedding c i a)) :
    a ∈ radical F σ hσ := by
  have hzsq : (i (c.left longPoint)) ^ 2 = 1 := by
    have h : longPoint ^ 2 = 1 := by simpa only [longPoint_order] using pow_orderOf_eq_one longPoint
    simpa only [MonoidHom.comp_apply,map_pow,map_one] using congrArg (i.comp c.left) h
  have hasq : a ^ 2 = 1 := by
    apply matrixPlaneEmbedding_injective c i hi
    rw [map_pow,map_one]
    exact isConj_one_right.mp (hzsq ▸ ha.pow 2)
  have hzi : i (c.right (matrixPlaneEquiv modelLong)) = i (c.left longPoint) :=
    (matrixPlaneEquiv_image c i modelLong).trans (long_image c i)
  have hm := right_involution_fusion_reflects c i hi hc hnorm
    (matrixPlaneEquiv modelLong) (matrixPlaneEquiv a)
    (by rw [← map_pow,longLocal_sq,map_one]) (by rw [← map_pow,hasq,map_one])
    (by rw [hzi,matrixPlaneEquiv_image]; exact ha)
  let e : MatrixGroup 1 hn ≃* ProjectiveGroup 1 hn :=
    MulEquiv.ofBijective (projection 1 hn)
      ⟨projection_injective 1 hn,UnitaryFourFlag.project_surjective F (standardForm 1 hn)⟩
  have he1 : (matrixPlaneEquiv modelLong).val = e (longLocal F σ hσ).val := rfl
  have he2 : (matrixPlaneEquiv a).val = e a.val := rfl
  rw [he1,he2] at hm
  have hm' := e.symm.toMonoidHom.map_isConj hm
  change IsConj (e.symm (e modelLong.val)) (e.symm (e a.val)) at hm'
  rw [e.symm_apply_apply,e.symm_apply_apply] at hm'
  exact long_conjugate_in_plane_mem_radical F σ hσ a hm'

/-- The simultaneous Burnside correction retains both marks. -/
theorem source_plane_pair_fusion
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    {x y u v : G}
    (hx : x ∈ PlainFusion.planeImage c i) (hy : y ∈ PlainFusion.planeImage c i)
    (hu : u ∈ PlainFusion.planeImage c i) (hv : v ∈ PlainFusion.planeImage c i)
    (g : G) (hgx : MulAut.conj g x = u) (hgy : MulAut.conj g y = v) :
    ∃ p : R, MulAut.conj (i (c.right p)) x = u ∧ MulAut.conj (i (c.right p)) y = v := by
  obtain ⟨S,hS,hJ⟩ := PlainFusion.completion_thompson c i hi longPoint longPoint_order longPoint_mem_root hc
  let W := PlainFusion.planeImage c i
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (PlainFusion.planeEmbedding c i)
  have hWS : W ≤ (S : Subgroup G) := by
    change PlainFusion.planeImage c i ≤ (S : Subgroup G)
    rw [← hJ]
    exact sSup_le fun A hA => hA.1
  have hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      g ∈ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := Stellmacher.elementaryAbelianMaxJ_map_eq_of_le (S : Subgroup G) (MulAut.conj g)
      (by rwa [hJ])
    change (PlainFusion.planeImage c i).map (MulAut.conj g).toMonoidHom = PlainFusion.planeImage c i
    simpa only [hJ] using he
  obtain ⟨n,hnN,hnx,hny⟩ := Sylow.PointwiseFusion.pair_fusion S W hWS hweak
    (W.le_centralizer hx) (W.le_centralizer hy) (W.le_centralizer hu) (W.le_centralizer hv)
    g hgx hgy
  change n ∈ normalizer (PlainFusion.planeImage c i : Set G) at hnN
  rw [← PlainFusion.sourcePlaneRootImage_eq c i,hnorm] at hnN
  obtain ⟨p,hp⟩ := hnN
  change i (c.right p) = n at hp
  exact ⟨p,by rw [hp]; exact hnx,by rw [hp]; exact hny⟩



omit [Finite G] in
/-- The actual model centralizer maps onto precisely the elements of the
plane endpoint which centralize the selected short root. -/
theorem source_plane_short_centralizer
    (hi : Function.Injective i) (p : R)
    (hp : i (c.right p) ∈ centralizer ({sourceShort c i} : Set G)) :
    ∃ x : X, matrixPlaneEmbedding c i x.val = i (c.right p) := by
  let a := matrixPlaneEquiv.symm p
  have hea : matrixPlaneEmbedding c i a = i (c.right p) := by
    rw [← matrixPlaneEquiv_image, MulEquiv.apply_symm_apply]
  have ha : a ∈ X := by
    apply mem_centralizer_singleton_iff.mpr
    apply matrixPlaneEmbedding_injective c i hi
    have hh : matrixPlaneEmbedding c i a * matrixPlaneEmbedding c i modelShort =
        matrixPlaneEmbedding c i modelShort * matrixPlaneEmbedding c i a := by
      rw [hea]
      exact mem_centralizer_singleton_iff.mp hp
    exact (map_mul (matrixPlaneEmbedding c i) a modelShort).trans
      (hh.trans (map_mul (matrixPlaneEmbedding c i) modelShort a).symm)
  exact ⟨⟨a,ha⟩,hea⟩

/-- The long root considered inside the actual short-root centralizer. -/
def ambientLong : ambientShortCentralizer c i :=
  shortCentralizerEmbedding c i (radicalIntoCentralizer F σ hσ
    (Multiplicative.ofAdd (longParameter F σ)))

omit [Finite G] in
theorem ambientLong_val : (ambientLong c i).val = i (c.left longPoint) := long_image c i

omit [Finite G] in
private theorem long_in_plane : i (c.left longPoint) ∈ PlainFusion.planeImage c i := by
  rw [← long_image, ← radical_image]
  exact ⟨longLocal F σ hσ,
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).property,rfl⟩

omit [Finite G] in
private theorem short_in_plane : sourceShort c i ∈ PlainFusion.planeImage c i := by
  rw [← radical_image]
  exact ⟨modelShort,
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))).property,rfl⟩

/-- The original marked long root fixes exactly one coset of X_t in C_G(t).
Both common-centralizer containment and fusion are derived from the source
hypotheses and the actual matrix endpoints. -/
theorem source_long_unique_fixed
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    ∃! q : ambientShortCentralizer c i ⧸ (shortCentralizerEmbedding c i).range,
      ambientLong c i • q = q := by
  let M := (shortCentralizerEmbedding c i).range
  have hzM : ambientLong c i ∈ M := ⟨_,rfl⟩
  apply UniqueFixedCoset.unique_of_fusion_and_centralizer hzM
  · intro a ha
    have hza : a.val ∈ centralizer ({i (c.left longPoint)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun x : ambientShortCentralizer c i => x.val)
        (mem_centralizer_singleton_iff.mp ha)
      change a.val * (ambientLong c i).val = (ambientLong c i).val * a.val at he
      rwa [ambientLong_val] at he
    obtain ⟨x,hx,he⟩ := source_common_centralizer_le_short_image c i hi hc ⟨a.property,hza⟩
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  · intro g hg
    obtain ⟨a,ha⟩ := hg
    have he : g.val * i (c.left longPoint) * g.val⁻¹ = matrixPlaneEmbedding c i a.val := by
      have h := congrArg (fun x : ambientShortCentralizer c i => x.val) ha
      change matrixPlaneEmbedding c i a.val = g.val * (ambientLong c i).val * g.val⁻¹ at h
      rw [ambientLong_val] at h
      exact h.symm
    have har : a.val ∈ radical F σ hσ := source_long_conjugate_mem_radical c i hi hc hnorm a.val
      (isConj_iff.mpr ⟨g.val,he⟩)
    have haq : matrixPlaneEmbedding c i a.val ∈ PlainFusion.planeImage c i := by
      rw [← radical_image]
      exact ⟨a.val,har,rfl⟩
    have hgt : MulAut.conj g.val (sourceShort c i) = sourceShort c i :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
    obtain ⟨p,hpz,hpt⟩ := source_plane_pair_fusion c i hi hc hnorm
      (long_in_plane c i) (short_in_plane c i) haq (short_in_plane c i) g.val he hgt
    have hpc : i (c.right p) ∈ centralizer ({sourceShort c i} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hpt)
    obtain ⟨n,hne⟩ := source_plane_short_centralizer c i hi p hpc
    refine ⟨shortCentralizerEmbedding c i n,⟨n,rfl⟩,?_⟩
    apply Subtype.ext
    change g.val * (ambientLong c i).val * g.val⁻¹ =
      matrixPlaneEmbedding c i n.val * (ambientLong c i).val * (matrixPlaneEmbedding c i n.val)⁻¹
    rw [ambientLong_val,hne]
    exact he.trans hpz.symm

end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootFusion
