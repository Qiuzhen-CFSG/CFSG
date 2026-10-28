module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration

/-!
# The first element selected in MS93 (3.7)(6)

A plane-radical subgroup larger than the field contains an invertible shear.
The shear fixes exactly the radical's natural fixed plane. The original
central cover lifts that equality of fixed vectors, so one actual element
of the opposite critical Z-layer has the same centralizer on U as the full
midpoint radical. Adjoining the complete central midpoint supplement gives
C_Z(x) = Z_t. The midpoint index q squared also proves x lies outside the
endpoint core.

The source application constructs the plane marking and the large image
from the original saturated distance-two hypotheses. It retains the entire
cover kernel, both original Z-layers and the actual actor map.
This is the initial x-choice on printed p.876. The subsequent P-normalizer
choice, its induced common-radical automorphism, and the order-q critical-pair
contradiction are still required for (6); this theorem does not assert them.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(6), printed p.876. The invertible-shear existence is the existing
LargePlaneGeneration result, transported through the original full cover.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

private theorem shear_fixed_iff {E : Type*} [Field E]
    (B : Plane.symmetricMatrices E) (v : Vector E) :
    Plane.shearSp B • v=v ↔ B.val *ᵥ (fun i => v (.inr i))=0 := by
  simp only [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Plane.shearSp]
  constructor
  · intro h
    ext i
    have hi := congrFun h (.inl i)
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.fromBlocks] at hi ⊢ <;> linear_combination hi
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks] at h0 h1 ⊢
    · linear_combination h0
    · linear_combination h1

private theorem plane_regular_element {E : Type*} [Field E] [Finite E] [CharP E 2]
    (A T : Subgroup (Sp E)) (hAT : A ≤ T)
    (k : Sp E) (hk : T.map (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (hc : Nat.card E < Nat.card A) :
    ∃ a ∈ A, ∀ v : Vector E, a • v=v → ∀ t ∈ T, t • v=v := by
  have hAP : A.map (MulAut.conj k).toMonoidHom ≤ SymplecticConjugatePair.planeRadical :=
    (map_mono hAT).trans_eq hk
  obtain ⟨B,hB,hdet⟩ := LargePlaneGeneration.exists_invertible_shear
    (A.map (MulAut.conj k).toMonoidHom) hAP
    (by rw [card_map_of_injective (MulAut.conj k).injective]; exact hc)
  obtain ⟨a,ha,he⟩ := hB
  refine ⟨a,ha,?_⟩
  intro v hv t ht
  have hkv : Plane.shearSp B • (k • v)=k • v := by
    rw [←he]
    change (k*a*k⁻¹) • (k • v)=k • v
    rw [mul_smul,mul_smul,inv_smul_smul,hv]
  have hz : (fun i => (k • v) (.inr i))=0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)))
    rw [Matrix.mulVec_zero]
    exact (shear_fixed_iff B (k • v)).mp hkv
  obtain ⟨C,hC⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp
    (hk ▸ mem_map_of_mem (MulAut.conj k).toMonoidHom ht)
  have htf : ((MulAut.conj k) t) • (k • v)=k • v := by
    change Plane.shearSp C=(MulAut.conj k) t at hC
    rw [←hC]
    exact (shear_fixed_iff C (k • v)).mpr (by rw [hz,Matrix.mulVec_zero])
  apply (toLinear k).injective
  simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul,toLinear_apply] using htf

private theorem embedded_regular_element
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (U A T : Subgroup G) (hAT : A ≤ T)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := E))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (k : Sp E) (hk : ((commutator (Sp E)).subtype.comp β).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (hc : Nat.card E < Nat.card
      (((commutator (Sp E)).subtype.comp β).comp (inclusion hAT)).range) :
    ∃ x ∈ A, U ⊓ centralizer ({x} : Set G)=U ⊓ centralizer (T : Set G) := by
  let α := (commutator (Sp E)).subtype.comp β
  let αA := α.comp (inclusion hAT)
  have hsub : αA.range ≤ α.range := by rintro _ ⟨a,rfl⟩; exact ⟨inclusion hAT a,rfl⟩
  obtain ⟨b,⟨x,rfl⟩,hb⟩ := plane_regular_element αA.range α.range hsub k hk hc
  refine ⟨x.val,x.property,?_⟩
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr (hAT x.property))))
  rintro u ⟨hu,hux⟩
  refine ⟨hu,?_⟩
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
  have hxw : σ (β (inclusion hAT x)) w.toAdd=w.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact]
    change x.val*j w*x.val⁻¹=j w
    rw [(mem_centralizer_singleton_iff.mp hux).symm,mul_inv_cancel_right]
  have hxp : αA x • p w.toAdd=p w.toAdd := by
    change binaryNatural (β (inclusion hAT x)) (p w.toAdd)=_
    rw [←p.isIntertwining,hxw]
  intro t ht
  have htp := hb (p w.toAdd) hxp (α ⟨t,ht⟩) ⟨⟨t,ht⟩,rfl⟩
  have htw := cover_fixed_of_projection_fixed p hp (β ⟨t,ht⟩) w.toAdd htp
  have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) htw
  rw [hact,ofAdd_toAdd,mul_inv_eq_iff_eq_mul] at hh
  exact hh

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The initial element choice in source (6): in the large critical-image
branch, an actual opposite Z-element has exactly the midpoint as centralizer
on the full first Z-layer. -/
theorem source_six_exists_regular_element
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧ Z d.radical a ⊓
      centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t := by
  obtain ⟨⟨cv⟩,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hZaX := g.omega_bound a path.start_color
    (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)
  have hZzX := g.omega_bound z path.end_color
    (by rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)
  have hZaT := hZaX.trans ((omegaCenter_le _).trans c.core_le_edge)
  have hZzT := hZzX.trans ((omegaCenter_le _).trans c'.core_le_edge)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)
        z path.end_color path.critical }
  have hreverse : (2^n)^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    by_contra hn
    have hh := (replacement_critical_indices_eq_field_of_small h d rev (by omega)
      (lt_of_not_ge hn)).2
    rw [hh] at hcritical
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  have hcard : Nat.card cv.field.Carrier < Nat.card (α.comp (inclusion hZzT)).range := by
    rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf]
    change Nat.card cv.field.Carrier < (Q d.radical a).relIndex (Z d.radical z)
    rw [cv.field.card_eq,cv.degree]
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    exact lt_of_lt_of_le (by nlinarith : 2^n<(2^n)^2) hreverse
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨x,hx,hC⟩ := embedded_regular_element
    (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
    (U d.radical a) (Z d.radical z) (Q d.radical t) hZzT
    cv.embedding cv.injective cv.range_eq cv.actor cv.actor_conjugation k hk hcard
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcent : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  let := g.Z_elementary (by omega) a path.start_color
  have hnorm : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have heq : Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t := by
    apply le_antisymm
    · rintro y ⟨hy,hyx⟩
      have hy' : y ∈ Z d.radical a := hy
      rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat,
        ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hy'
      obtain ⟨u,hu,v,hv,rfl⟩ := hy'
      have hux : u ∈ centralizer ({x} : Set (FreeAmalgam d.radical)) := by
        apply mem_centralizer_singleton_iff.mpr
        have hvx := hcent hv x (hZzT hx)
        have hh := mem_centralizer_singleton_iff.mp hyx
        apply mul_right_cancel (b := v)
        calc
          u*x*v = u*(x*v) := mul_assoc _ _ _
          _ = u*(v*x) := by rw [hvx]
          _ = (u*v)*x := (mul_assoc _ _ _).symm
          _ = x*(u*v) := hh
          _ = x*u*v := (mul_assoc _ _ _).symm
      have huT := (hC.le ⟨hu,hux⟩).2
      rw [hZt]
      exact mem_omegaCenter_iff.mpr ⟨hZaT hy,(mem_omegaCenter_iff.mp (hZaX hy)).2.1,
        (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).mul_mem huT (hcent hv)⟩
    · exact le_inf (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
        (fun y hy => mem_centralizer_singleton_iff.mpr (hcent hy x (hZzT hx)).symm)
  refine ⟨x,hx,?_,heq⟩
  intro hxQ
  have hZa : Z d.radical a ≤ Z d.radical t := by
    rw [←heq]
    refine le_inf le_rfl ?_
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)
        hy x hxQ).symm
  have hh := (source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical).2.2.1
  rw [relIndex_eq_one.mpr hZa] at hh
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  nlinarith

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
