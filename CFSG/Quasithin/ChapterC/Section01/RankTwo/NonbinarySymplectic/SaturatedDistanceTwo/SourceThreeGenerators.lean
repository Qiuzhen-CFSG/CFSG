module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeOverlap

/-!
# The plane-radical contradiction in MS93 (3.7)(3)

On the complete orthogonal cover, the displacement of a plane radical on
any natural hyperplane generates its entire displacement. A vector outside
the fixed plane has nonzero lower coordinates; symmetric shears move it in
all upper directions. Comparing two scalar multiples of a shear recovers
the central direction as well, since the original field has more than two
elements. Conjugation and the universal cover quotient transport this
calculation without deleting the full central attachment.

For the actual noncontained-core configuration, the critical root has a
natural fixed hyperplane. Its embedded preimage is in Z′ ∩ Q, whose radical
displacement was proved to lie in D. Thus all radical displacement on U′,
and hence the critical commutator R, lies in D. But R has order q times the
order of its full fixed attachment U ∩ D, giving a contradiction.

This completes source (3)'s core containment, Q = U D, X = Z and both
field-sized overlap indices, with its original order-q critical-image
antecedent. Paired fixed-kernel equality, source (5)/(6) and the terminal
field restriction remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(3), printed p.874.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Matrix Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def topVector (u : Fin 2 → F) : Vector F := Sum.elim u 0

omit [Finite F] [CharP F 2] in
private theorem shear_displacement (B : Plane.symmetricMatrices F) (v : Vector F) :
    (Plane.shearSp B) • v-v=topVector (B.val *ᵥ (fun i => v (.inr i))) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Plane.shearSp,topVector,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

omit [Finite F] [CharP F 2] in
private theorem symmetric_evaluation_surjective (y : Fin 2 → F) (hy : y ≠ 0)
    (u : Fin 2 → F) : ∃ B : Plane.symmetricMatrices F, B.val *ᵥ y=u := by
  by_cases h0 : y 0=0
  · have h1 : y 1 ≠ 0 := by
      intro h1
      apply hy
      ext i
      fin_cases i <;> assumption
    refine ⟨⟨!![0,u 0/y 1;u 0/y 1,u 1/y 1],?_⟩,?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · ext i; fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,h0,h1]
  · refine ⟨⟨!![(u 0-(u 1/y 0)*y 1)/y 0,u 1/y 0;u 1/y 0,0],?_⟩,?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · ext i; fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,h0]

private theorem shear_correction_square (B : Plane.symmetricMatrices F) (v : Vector F) :
    correction (Plane.shearSp B) v ^ 2 =
      dotProduct (fun i => v (.inr i)) (B.val *ᵥ (fun i => v (.inr i))) := by
  have h := correction_square (Plane.shearSp B) v
  have he := shear_displacement B v
  have hv := sub_eq_iff_eq_add.mp he
  change (Plane.shearSp B).val *ᵥ v=topVector (B.val *ᵥ (fun i => v (.inr i)))+v at hv
  rw [hv] at h
  simp only [rowQuadratic,Pi.add_apply,topVector,Sum.elim_inl,Sum.elim_inr,
    Pi.zero_apply,zero_add] at h
  dsimp only [dotProduct]
  rw [Fin.sum_univ_two]
  linear_combination -h

/-- A single nonfixed natural direction, with all field multiples, generates
all plane-radical displacement in the complete orthogonal cover. -/
private theorem standard_plane_overlap (hF : 2 < Nat.card F)
    (D : AddSubgroup (Space (K := F))) (v : Vector F)
    (hv : (fun i => v (.inr i)) ≠ 0)
    (hD : ∀ (B : Plane.symmetricMatrices F) (t : F),
      fullAction (Plane.shearSp B) (t • (v,0)) - t • (v,0) ∈ D) :
    ∀ (u : Fin 2 → F) (z : F), (topVector u,z) ∈ D := by
  let y : Fin 2 → F := fun i => v (.inr i)
  have hpair (B : Plane.symmetricMatrices F) (t : F) :
      t • (topVector (B.val *ᵥ y),correction (Plane.shearSp B) v) ∈ D := by
    have hh := hD B t
    rw [map_smul,←smul_sub] at hh
    have he : fullAction (Plane.shearSp B) (v,0)-(v,0)=
        (topVector (B.val *ᵥ y),correction (Plane.shearSp B) v) := by
      apply Prod.ext
      · exact shear_displacement B v
      · simp [fullAction_apply]
    rwa [he] at hh
  obtain ⟨i,hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hn
    apply hv
    ext i
    exact not_ne_iff.mp (not_exists.mp hn i)
  let u : Fin 2 → F := Pi.single i (y i)⁻¹
  obtain ⟨B,hB⟩ := symmetric_evaluation_surjective y hv u
  have hBc : correction (Plane.shearSp B) v=1 := by
    apply CharTwo.sq_injective
    dsimp only
    rw [shear_correction_square,hB]
    change dotProduct y u=1^2
    simp only [u,dotProduct_single,one_pow,mul_inv_cancel₀ hi]
  obtain ⟨s,hs0,hs1⟩ : ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
    apply ENat.exists_ne_ne_of_three_le
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast (show 3 ≤ Nat.card F by omega)
  have hss : s-s^2 ≠ 0 := by
    intro he
    have hh : s*(1-s)=0 := by linear_combination he
    rcases mul_eq_zero.mp hh with hh | hh
    · exact hs0 hh
    · exact hs1 (sub_eq_zero.mp hh).symm
  let C : Plane.symmetricMatrices F := s^2 • B
  have hC : C.val *ᵥ y=s^2 • u := by
    change (s^2 • B.val) *ᵥ y=_
    rw [Matrix.smul_mulVec,hB]
  have hCc : correction (Plane.shearSp C) v=s := by
    apply CharTwo.sq_injective
    dsimp only
    rw [shear_correction_square,hC]
    change dotProduct y (s^2 • u)=s^2
    rw [dotProduct_smul]
    simp only [u,dotProduct_single,mul_inv_cancel₀ hi,smul_eq_mul,mul_one]
  have hz (z : F) : (0,z) ∈ D := by
    let t := z/(s-s^2)
    have h1 := hpair C t
    have h2 := hpair B (t*s^2)
    rw [hC,hCc] at h1
    rw [hB,hBc] at h2
    have hh := D.sub_mem h1 h2
    have he : t • (topVector (s^2 • u),s)-(t*s^2) • (topVector u,1)=(0,z) := by
      apply Prod.ext
      · ext j
        rcases j with j | j <;> simp [topVector,smul_eq_mul,mul_assoc]
      · change t*s-t*s^2*1=z
        rw [mul_one,←mul_sub,div_mul_cancel₀ _ hss]
    rwa [he] at hh
  intro w z
  obtain ⟨A,hA⟩ := symmetric_evaluation_surjective y hv w
  have hh := D.add_mem (hpair A 1) (hz (z-correction (Plane.shearSp A) v))
  simpa only [hA,one_smul,Prod.mk_add_mk,add_zero,add_sub_cancel] using hh


private theorem fullAction_conjugate (g a : Sp F) (w : Space (K := F)) :
    fullAction (g*a*g⁻¹) w-w=
      fullAction g (fullAction a (fullAction g⁻¹ w)-fullAction g⁻¹ w) := by
  simp only [map_sub,map_mul,Module.End.mul_apply,self_inv_apply]

private theorem plane_hyperplane_movement (hF : 2 < Nat.card F)
    (A : Subgroup (Sp F)) (g : Sp F)
    (hA : A.map (MulAut.conj g).toMonoidHom=planeRadicalAmbient)
    (E : Submodule F (Vector F)) (hE : 3 ≤ Module.finrank F E)
    (D : AddSubgroup (Space (K := F)))
    (hD : ∀ a ∈ A, ∀ w : Space (K := F), w.1 ∈ E → fullAction a w-w ∈ D) :
    ∀ a ∈ A, ∀ w : Space (K := F), fullAction a w-w ∈ D := by
  let E' := E.map (toLinear g).toLinearMap
  have hE' : 3 ≤ Module.finrank F E' := by
    rw [(toLinear g).finrank_map_eq E]
    exact hE
  have hnot : ¬ E' ≤ plane F := by
    intro hh
    have hd := Submodule.finrank_mono hh
    rw [finrank_plane] at hd
    omega
  obtain ⟨v,hv,hvp⟩ : ∃ v, v ∈ E' ∧ v ∉ plane F := by
    obtain ⟨v,hv⟩ := Set.not_subset.mp hnot
    exact ⟨v,hv.1,hv.2⟩
  let D' := D.comap (fullAction g⁻¹).toAddMonoidHom
  have hs (B : Plane.symmetricMatrices F) (t : F) :
      fullAction (Plane.shearSp B) (t • (v,0))-t • (v,0) ∈ D' := by
    have hg : Plane.shearSp B ∈ A.map (MulAut.conj g).toMonoidHom := by
      rw [hA]
      exact (SymplecticConjugatePair.mem_planeRadical_iff _).mpr ⟨B,rfl⟩
    obtain ⟨a,ha,he⟩ := hg
    change g*a*g⁻¹=Plane.shearSp B at he
    change fullAction g⁻¹ (fullAction (Plane.shearSp B) (t • (v,0))-t • (v,0)) ∈ D
    rw [←he,fullAction_conjugate,inv_self_apply]
    apply hD a ha
    have htv : t • v ∈ E' := E'.smul_mem t hv
    obtain ⟨u,hu,heu⟩ := htv
    change g⁻¹ • (t • v) ∈ E
    rw [←heu]
    change g⁻¹ • (g • u) ∈ E
    rw [inv_smul_smul]
    exact hu
  have hall := standard_plane_overlap hF D' v (by
    intro he
    apply hvp
    exact fun i => congrFun he i) hs
  intro a ha w
  have hag : g*a*g⁻¹ ∈ planeRadicalAmbient := by
    rw [←hA]
    exact mem_map_of_mem _ ha
  obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp hag
  let w' := fullAction g w
  have hw : fullAction (Plane.shearSp B) w'-w' ∈ D' := by
    have he : fullAction (Plane.shearSp B) w'-w'=
        (topVector (B.val *ᵥ (fun i => w'.1 (.inr i))),correction (Plane.shearSp B) w'.1) := by
      apply Prod.ext
      · exact shear_displacement B w'.1
      · simp [fullAction_apply]
    rw [he]
    exact hall _ _
  change fullAction g⁻¹ (fullAction (Plane.shearSp B) w'-w') ∈ D at hw
  rw [hB,fullAction_conjugate,inv_self_apply] at hw
  dsimp only [w'] at hw
  rwa [inv_self_apply] at hw


open scoped IsMulCommutative commutatorElement
private theorem embedded_plane_overlap
    [Algebra (ZMod 2) F] {W G : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (hF : 2 < Nat.card F) (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U T B D : Subgroup G) (hBT : B ≤ T)
    (j : Multiplicative W →* G) (hjr : j.range=U)
    (β : T →* L (K := F))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hplane : ∃ g : Sp F, (((commutator (Sp F)).subtype.comp β).range).map
      (MulAut.conj g).toMonoidHom=planeRadicalAmbient)
    (hdim : Module.finrank F (displacementSpace
      (((commutator (Sp F)).subtype.comp β).comp (inclusion hBT)).range)=1)
    (hD : ⁅U ⊓ centralizer (B : Set G),T⁆ ≤ D) : ⁅U,T⁆ ≤ D := by
  let α := (commutator (Sp F)).subtype.comp β
  let αB := α.comp (inclusion hBT)
  let E := TwoLocalCover.fixedSpace αB.range
  have hE : 3 ≤ Module.finrank F E := by
    have he := LinearMap.BilinForm.finrank_orthogonal
      (W := displacementSpace αB.range) TwoLocalCover.form_nondegenerate
    rw [orthogonal_displacementSpace,hdim] at he
    have hV : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hV] at he
    change 3 ≤ Module.finrank F (TwoLocalCover.fixedSpace αB.range)
    omega
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let D₀ := ((D.comap j).toAddSubgroup).comap f.toLinearMap.toAddMonoidHom
  have hmem (w : Space (K := F)) (hw : w.1 ∈ E) :
      j (Multiplicative.ofAdd (f w)) ∈ U ⊓ centralizer (B : Set G) := by
    refine ⟨hjr ▸ ⟨_,rfl⟩,?_⟩
    intro b hb
    have he : binaryNatural (β (inclusion hBT ⟨b,hb⟩)) (p (f w))=p (f w) := by
      rw [hpf]
      exact hw (αB ⟨b,hb⟩) ⟨⟨b,hb⟩,rfl⟩
    have he' := cover_fixed_of_projection_fixed p hp (β (inclusion hBT ⟨b,hb⟩)) (f w) he
    have hh := hact (inclusion hBT ⟨b,hb⟩) (f w)
    rw [he'] at hh
    have hh' := congrArg (fun x : G => x*b) hh
    change j (Multiplicative.ofAdd (f w))*b=(b*j (Multiplicative.ofAdd (f w))*b⁻¹)*b at hh'
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'.symm
  obtain ⟨r,hr⟩ := hplane
  have hfull := plane_hyperplane_movement hF α.range r hr E hE D₀ (by
    intro a ha w hw
    obtain ⟨x,rfl⟩ := ha
    change j (Multiplicative.ofAdd (f (fullAction (α x) w-w))) ∈ D
    have he : f (fullAction (α x) w)=σ (β x) (f w) :=
      LinearMap.congr_fun (f.isIntertwining' (β x)) w
    rw [map_sub,he,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    exact hD (commutator_comm T (U ⊓ centralizer (B : Set G)) ▸
      commutator_mem_commutator x.property (hmem w hw)))
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx u hu
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
  obtain ⟨v,hv⟩ := hf w.toAdd
  have hh := hfull (α ⟨x,hx⟩) ⟨⟨x,hx⟩,rfl⟩ v
  change j (Multiplicative.ofAdd (f (fullAction (α ⟨x,hx⟩) v-v))) ∈ D at hh
  have he : f (fullAction (α ⟨x,hx⟩) v)=σ (β ⟨x,hx⟩) (f v) :=
    LinearMap.congr_fun (f.isIntertwining' (β ⟨x,hx⟩)) v
  rw [map_sub,he,hv,ofAdd_sub,map_div,div_eq_mul_inv,hact] at hh
  exact hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The plane-radical generator contradiction excludes the remaining
noncontained-core branch of source (3.7)(3). -/
theorem source_three_core_containment
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z := by
  by_contra hnot
  let := replacementComponent_normal h d
  obtain ⟨⟨cv⟩,_,_⟩ :=
    source_three_noncontained_plane_cover h d g hb hsat path hat hzt c c' hcritical hnot
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  let s := replacementMovedSection h d
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans c.core_le_edge
  let βZ := β.comp (inclusion hZaT)
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTS
  let δ := κ.comp (inclusion hZaS)
  have hFc : Nat.card E.Carrier=2^n :=
    E.card_eq.trans (congrArg (2^·) hE)
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ
    (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZrange : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
    rw [MonoidHom.range_comp,hβZ]
  have hdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    rw [hZrange]
    exact hηdim
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (by have := h.nonbinary; omega)
  have hEF : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.nonbinary)
  have hC := MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hUC : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤
      Z d.radical z ⊓ Q d.radical a := by
    intro x hx
    refine ⟨U_le_Z z hx.1,?_⟩
    rw [←hC]
    exact ⟨hZA (U_le_Z z hx.1),hx.2⟩
  have hfull : ⁅U d.radical z,Q d.radical t⁆ ≤ fixedCore d.radical a := by
    apply embedded_plane_overlap hEF
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
      (U d.radical z) (Q d.radical t) (Z d.radical a) (fixedCore d.radical a)
      hZaT j hjr β hact hplane hdim
    exact (commutator_mono hUC le_rfl).trans
      (source_three_noncontained_overlap_displacement h d g hb hsat path hat hzt c c' hcritical hnot)
  have hpair := critical_paired_fixed_layers h d path hb hat hzt hcritical
  have hRD : ⁅Z d.radical a,Z d.radical z⁆ ≤ fixedCore d.radical a := by
    rw [hpair.1,commutator_comm]
    exact (commutator_mono le_rfl ((U_le_Z a).trans hZaT)).trans hfull
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  have hRA : ⁅Z d.radical a,Z d.radical z⁆ ≤ A :=
    le_inf (hpair.2.2.1.trans inf_le_left) (hRD.trans inf_le_right)
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a)))
    (inclusion_injective _)
  have hc := Nat.card_le_card_of_injective (inclusion hRA) (inclusion_injective _)
  rw [hpair.2.2.2.1] at hc
  have ha : 0 < Nat.card A := Nat.card_pos
  change 2^n*Nat.card A ≤ Nat.card A at hc
  nlinarith

/-- Source (3.7)(3), with the actual critical image of order q: the full
core is U D, the central omega layer is Z, and both overlap indices are q.
The complete fixed attachments and original quotient markings remain. -/
theorem source_three_of_field_critical
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      X d.radical a=Z d.radical a ∧
      (Z d.radical z).relIndex (Z d.radical a)=2^n ∧
      (Z d.radical a).relIndex (Z d.radical z)=2^n := by
  have hinside := source_three_core_containment h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨hQ,hX⟩ := source_three_contained_core h d path hb hat c hcritical hinside
  exact ⟨hinside,hQ,hX,source_three_contained_core_overlap h d path hb hat hzt hcritical hinside⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
