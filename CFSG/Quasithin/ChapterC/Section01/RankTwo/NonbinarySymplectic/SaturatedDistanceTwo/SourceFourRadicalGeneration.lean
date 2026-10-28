module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourSectionCentralizer

/-!
# Radical generation by a source (4) hyperplane

In the large critical-image branch of MS93 (3.7)(4), every full fixed
hyperplane X of field index q generates the whole common displacement:
[X,T] = [Z,Z′]. The actual plane-radical cover supplies this assertion
for any plane marking. A natural hyperplane contains a vector outside the
fixed plane; symmetric shears move it in every upper direction, and two
scalar multiples recover the full central covering direction. The midpoint
supplement centralizes T and so does not alter the movement.

The original cover projection also identifies the quotient of [Z,Z′] by
the complete fixed attachment with its natural displacement plane. Thus
its index is q squared and its order is q squared times the attachment
order. In the escaping unequal-attachment branch, both attachments have
order q, whereas [X,Z′] has order q squared. The resulting strict count
selects an actual individual commutator of X with T outside [X,Z′].

These are the full-radical generation and counting inputs for the complement
comparison on printed p.875. The comparison still requires the section
centralizer factorization; complement disjointness, selection of a root
element in the opposite centralizer, the remaining source (4)--(6) branches,
and the field restriction are not asserted here.

The private plane-generation calculation reuses SourceThreeGenerators;
the private projection-index transports adapt CriticalFixedLayers and
SourceFourEscape. All applications retain the full original covers and
quotient/action maps. The final exports have literal Chapter11 applications.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
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

private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]



private theorem cover_displacement_index
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (U A : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = U)
    (β : A →* L (K := E))
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    : (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅A,U⁆ =
      (centralizer (A : Set G)).relIndex U := by
  let C := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp E)).subtype.comp β
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection U A hAU σ
    (binaryNatural (K := E)) j hj hjr p.toLinearMap hp.1
    (fun x w => LinearMap.congr_fun (p.isIntertwining' x) w) β hact
  have hker : π.ker.map U.subtype = C := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      have huj : u.val ∈ j.range := by rw [hjr]; exact u.property
      obtain ⟨w,hw⟩ := huj
      have he : u = ⟨j w,by rw [←hjr]; exact MonoidHom.mem_range.mpr ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u = 1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπj w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,by rw [←hjr]; exact MonoidHom.mem_range.mpr ⟨w,rfl⟩⟩,?_,rfl⟩
      change π ⟨j w,_⟩ = 1
      exact (hπj w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  let B := (displacementSpace α.range).toAddSubgroup.toSubgroup
  let P := (B.comap π).map U.subtype
  have hMP : ⁅A,U⁆ ≤ P := by
    apply commutator_le.mpr
    intro a ha u hu
    let v : U := ⟨a*u*a⁻¹,(mem_normalizer_iff.mp (hAU ha) u).mp hu⟩ * ⟨u,hu⟩⁻¹
    refine ⟨v,?_,rfl⟩
    change (π v).toAdd ∈ displacementSpace α.range
    dsimp only [v]
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [hπact ⟨a,ha⟩ ⟨u,hu⟩]
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
      ⟨α ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ (π ⟨u,hu⟩).toAdd
  have hMU : ⁅A,U⁆ ≤ U := le_normalizer_iff_commutator_le_right.mp hAU
  have hmap : (⁅A,U⁆.subgroupOf U).map π = B := by
    apply le_antisymm
    · rintro v ⟨u,hu,rfl⟩
      obtain ⟨w,hw,he⟩ := hMP hu
      have he' : w=u := Subtype.ext he
      exact he' ▸ hw
    · intro v hv
      obtain ⟨w,hw,hwm⟩ := natural_displacement_lifts U A j hjr β σ hact p hp.1 v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩,hwm,?_⟩
      exact (hπj w).trans (congrArg Multiplicative.ofAdd hw)
  have hindex : C.relIndex ⁅A,U⁆ = Nat.card B := by
    rw [←hmap,←relIndex_ker]
    have hi := relIndex_subgroupOf (H := C) hMU
    rw [←hker,subgroupOf_map_subtype_eq] at hi
    rw [hker] at hi
    exact hi.symm
  have hBcard : Nat.card B = Nat.card E ^ Module.finrank E (displacementSpace α.range) := by
    let e : B ≃ displacementSpace α.range :=
      { toFun := fun x => ⟨x.val.toAdd,x.property⟩
        invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := E)]
  exact (hindex.trans hBcard).trans
    (cover_moving_index σ p hp U A j hj hjr β hact).symm

private theorem central_supplement_fixed_index {G : Type*} [Group G]
    (V C D A : Subgroup G) [Finite D] [IsMulCommutative D]
    (hVD : V ≤ D) (hCD : C ≤ D) (hgen : D=V ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex D=(centralizer (A : Set G)).relIndex V := by
  let X := D ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_inf hCD hCA
  have hVX : V ⊔ X=D := le_antisymm (sup_le hVD inf_le_left)
    (hgen.le.trans (sup_le le_sup_left (hCX.trans le_sup_right)))
  have hXU : X ≤ normalizer (V : Set G) :=
    (inf_le_left.trans (D.le_centralizer.trans (centralizer_le hVD))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : Finite X := Finite.of_injective (inclusion (show X ≤ D from inf_le_left))
    (inclusion_injective _)
  have he : X ⊓ V=V ⊓ centralizer (A : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨hVD hx.1,hx.2⟩,hx.1⟩⟩
  calc
    _ = X.relIndex D := (inf_relIndex_left _ _).symm
    _ = X.relIndex (V ⊔ X) := congrArg (X.relIndex ·) hVX.symm
    _ = X.relIndex V := relIndex_sup_of_normalizes V X hXU
    _ = _ := by rw [←inf_relIndex_right,he,inf_relIndex_left]

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
private theorem plane_cover_hyperplane_generation
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {z t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (cv : RadicalPlaneCover T s n z t) (hn : 2 < 2^n)
    (P : Subgroup (FreeAmalgam T)) (hP : P ≤ Q T t)
    (hi : (centralizer (P : Set (FreeAmalgam T))).relIndex (U T z)=2^n) :
    ⁅U T z,Q T t⁆ ≤ ⁅U T z ⊓ centralizer (P : Set (FreeAmalgam T)),Q T t⁆ := by
  let p := MovedSection.coverProjection s cv.equiv
  let σ := MovedSection.coverAction s cv.equiv
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hd : Module.finrank cv.field.Carrier (displacementSpace
      (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hP)).range)=1 := by
    have hh := cover_moving_index σ p cv.cover (U T z) P cv.embedding cv.injective cv.range_eq
      (cv.actor.comp (inclusion hP)) (fun x w => cv.actor_conjugation (inclusion hP x) w)
    apply Nat.pow_right_injective (Finite.one_lt_card : 1 < Nat.card cv.field.Carrier)
    exact hh.symm.trans (hi.trans (hFc.symm.trans (pow_one _).symm))
  exact embedded_plane_overlap (hFc ▸ hn) σ p cv.cover (U T z) (Q T t) P
    ⁅U T z ⊓ centralizer (P : Set (FreeAmalgam T)),Q T t⁆ hP
    cv.embedding cv.range_eq cv.actor cv.actor_conjugation cv.plane_image hd le_rfl

private theorem plane_cover_displacement_index
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {z t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (cv : RadicalPlaneCover T s n z t)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ Q T t) :
    (U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))).relIndex ⁅A,U T z⁆ =
      (centralizer (A : Set (FreeAmalgam T))).relIndex (U T z) := by
  let p := MovedSection.coverProjection s cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  rw [←hk]
  exact cover_displacement_index (U T z) A
    ((hA.trans cv.edge_le).trans (U_normalized z))
    (MovedSection.coverAction s cv.equiv) p cv.cover cv.embedding cv.injective cv.range_eq
    (cv.actor.comp (inclusion hA)) (fun a w => cv.actor_conjugation (inclusion hA a) w)

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A full hyperplane fixed by a subgroup of the common radical generates
its entire displacement. The original cover and arbitrary plane marking
are retained. -/
theorem source_four_large_hyperplane_full_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z)=2^n) :
    ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Q d.radical t⁆=
      ⁅Z d.radical a,Z d.radical z⁆ := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  let C := Z d.radical t
  let V := U d.radical z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show C=omegaCenter (Q d.radical t) by simp [C,Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  let := finite_Z d.radical z
  have hgen : Z d.radical z=V ⊔ C :=
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt
  have hiV : (centralizer (P : Set (FreeAmalgam d.radical))).relIndex V=2^n := by
    rw [←central_supplement_fixed_index V C (Z d.radical z) P (U_le_Z z) hCZ hgen
      (hCT.trans (centralizer_le hP)),←inf_relIndex_left]
    exact hi
  have hfull : ⁅V,Q d.radical t⁆ ≤ ⁅X₀,Q d.radical t⁆ :=
    plane_cover_hyperplane_generation cv
      (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary) P hP hiV
  have hTZV : V ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    (U_le_Z z).trans ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
        ((omegaCenter_le _).trans (c'.core_le_edge.trans (Q d.radical t).le_normalizer)))
  have hZVC : Z d.radical z ≤ V ⊔ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    hgen.le.trans (sup_le_sup_left hCT V)
  have hmove : ⁅Q d.radical t,Z d.radical z⁆ ≤ ⁅Q d.radical t,V⁆ :=
    commutator_le_moving_of_inner_mod_centralizer (Q d.radical t) V
      (Z d.radical z) hTZV hZVC
  have hfullZ : ⁅Z d.radical z,Q d.radical t⁆ ≤ ⁅X,Q d.radical t⁆ := by
    calc
      _ = ⁅Q d.radical t,Z d.radical z⁆ := commutator_comm _ _
      _ ≤ ⁅Q d.radical t,V⁆ := hmove
      _ = ⁅V,Q d.radical t⁆ := commutator_comm _ _
      _ ≤ ⁅X₀,Q d.radical t⁆ := hfull
      _ ≤ ⁅X,Q d.radical t⁆ := commutator_mono
        (inf_le_inf_right _ (U_le_Z z)) le_rfl
  apply le_antisymm
  · exact (commutator_mono (show X ≤ Z d.radical z from inf_le_left) le_rfl).trans_eq
      ((commutator_comm _ _).trans (source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical))
  · rw [←source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical,
      commutator_comm]
    exact hfullZ

/-- In the large critical-image branch, the full common displacement has
index q squared over the complete attachment, and the corresponding exact
order. No maximal-kernel assumption is needed. -/
theorem source_four_large_displacement_order
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let D := ⁅Z d.radical a,Z d.radical z⁆
    A ≤ D ∧ A.relIndex D=(2^n)^2 ∧ Nat.card D=(2^n)^2 * Nat.card A := by
  obtain ⟨⟨cv⟩,hi,_,hA⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let D := ⁅Z d.radical a,Z d.radical z⁆
  have he : D=⁅Z d.radical a,U d.radical z⁆ := by
    apply le_antisymm ?_ (commutator_mono le_rfl (U_le_Z z))
    rw [critical_displacement_eq_paired_moving h d path hb hat hzt]
    exact commutator_mono (U_le_Z a) le_rfl
  have hAT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hAD : A ≤ D := hA.trans_eq he.symm
  have hiD : A.relIndex D=(2^n)^2 := by
    rw [he]
    exact (plane_cover_displacement_index cv (Z d.radical a) hAT).trans hi
  refine ⟨hAD,hiD,?_⟩
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) A D bot_le hAD
  simpa only [relIndex_bot_left,hiD,mul_comm] using hh.symm

/-- In the escaping unequal-attachment branch the selected hyperplane has
radical movement of order q cubed, strictly larger than its opposite
movement of order q squared. In particular an actual individual radical
commutator escapes the opposite movement. -/
theorem source_four_large_unequal_radical_escape
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    Nat.card (⁅X,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))=(2^n)^3 ∧
      ∃ x ∈ X, ∃ b ∈ Q d.radical t, ⁅x,b⁆ ∉ ⁅X,Z d.radical a⁆ := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let M := ⁅X,Z d.radical a⁆
  have ha : Nat.card (U d.radical a ⊓ centralizer
      (Ltilde d.radical a : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical))=2^n := by
    by_contra hs
    exact hne (source_four_large_escaping_small_attachment_eq h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape hs)
  have hz : Nat.card (U d.radical z ⊓ centralizer
      (Ltilde d.radical z : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical))=2^n :=
    (source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical).symm.trans ha
  have hMcard : Nat.card M=(2^n)^2 := by
    have hh := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2
    simpa only [ha,pow_two] using hh
  have hDcard : Nat.card (⁅X,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))=(2^n)^3 := by
    rw [source_four_large_hyperplane_full_movement h d g hb hsat path hat hzt c c' hcritical P hP hi,
      (source_four_large_displacement_order h d g hb hsat path hat hzt c c' hcritical).2.2,hz]
    exact (pow_succ (2^n) 2).symm
  refine ⟨hDcard,?_⟩
  by_contra! hn
  have hle : ⁅X,Q d.radical t⁆ ≤ M := commutator_le.mpr hn
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hMcard]; positivity)
  have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
  rw [hDcard,hMcard] at hbound
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 3))) hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
