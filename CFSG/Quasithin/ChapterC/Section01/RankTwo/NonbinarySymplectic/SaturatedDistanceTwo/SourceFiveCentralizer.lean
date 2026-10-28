module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane

public import Theory.SpecificGroups.SymplecticFour.GeneratedRootMovement

/-!
# The plane-radical element-centralizer count in MS93 (3.7)(5)

Evaluation of symmetric two-by-two matrices at a nonzero vector is onto
and has a one-dimensional kernel. Hence the stabilizer of a vector outside
the fixed plane has order q and a displacement line. Conjugation retains
an arbitrary plane marking; fixed-vector lifting transports the calculation
through the entire original binary cover.

The full Z-layer is U times the midpoint omega-center. Removing that fixed
factor identifies the literal centralizer of every x in Z outside the
midpoint. Its image modulo the complete endpoint core has order q, and
its fixed indices on U and Z are both q.

The whole-core displacement theorem supplies the full-X clause as well.
Every displacement of X lies in U and in the natural displacement times D.
Their intersection is the natural displacement times the complete attachment
A = U intersect C(L). Thus the full-X displacement has index q over its
intersection with A, giving the second count on printed p.876. No fixed
attachment or quotient kernel is discarded.

The source applications construct the plane cover from the original saturated
large critical image. Comparing the two Z-layers in their common X using
these counts, source (6)'s critical-pair selection, and the degree-two/block
assembly remain separate obligations of this theorem family.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(5), printed pp.875--876. The private displacement/index transport
adapts CriticalReduction/TerminalIndices to distance two, using the existing
WholeSection and SourceThreeMovement full-core results.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
variable {F : Type*} [Field F]
private def symmetricCoordinates : Plane.symmetricMatrices F ≃ₗ[F] (F × F × F) where
  toFun B := (B.val 0 0,B.val 0 1,B.val 1 1)
  invFun v := ⟨!![v.1,v.2.1;v.2.1,v.2.2],by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    have hs : B.val 1 0=B.val 0 1 := congrFun (congrFun B.property 0) 1
    fin_cases i <;> fin_cases j <;> simp [hs]
  right_inv v := by rcases v with ⟨a,b,c⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def symmetricEvaluation (w : Fin 2 → F) : Plane.symmetricMatrices F →ₗ[F] (Fin 2 → F) where
  toFun B := B.val *ᵥ w
  map_add' _ _ := Matrix.add_mulVec _ _ _
  map_smul' _ _ := Matrix.smul_mulVec _ _ _

private theorem symmetricEvaluation_onto (w : Fin 2 → F) (hw : w ≠ 0) :
    Function.Surjective (symmetricEvaluation w) := by
  intro v
  by_cases h0 : w 0=0
  · have h1 : w 1≠0 := by
      intro h1
      apply hw
      ext i
      fin_cases i <;> assumption
    refine ⟨symmetricCoordinates.symm (0,v 0/w 1,v 1/w 1),?_⟩
    ext i
    fin_cases i <;> simp [symmetricEvaluation,symmetricCoordinates,h0,h1]
  · refine ⟨symmetricCoordinates.symm ((v 0-(v 1/w 0)*w 1)/w 0,v 1/w 0,0),?_⟩
    ext i
    fin_cases i <;> simp [symmetricEvaluation,symmetricCoordinates,h0]

private theorem shear_fixed_iff (B : Plane.symmetricMatrices F) (v : Vector F) :
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

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem plane_vector_stabilizer_card (v : Vector F) (hv : v ∉ plane F) :
    Nat.card (planeRadicalAmbient ⊓ MulAction.stabilizer (Sp F) v : Subgroup (Sp F))=Nat.card F := by
  let w : Fin 2 → F := fun i => v (.inr i)
  have hw : w≠0 := by
    intro he
    exact hv (fun i => congrFun he i)
  let E := symmetricEvaluation w
  have hs := symmetricEvaluation_onto w hw
  have hd := E.finrank_range_add_finrank_ker
  have hdom : Module.finrank F (Plane.symmetricMatrices F)=3 := by
    rw [symmetricCoordinates.finrank_eq]
    simp [Module.finrank_prod]
  rw [hdom,LinearMap.range_eq_top.mpr hs,finrank_top] at hd
  have hcod : Module.finrank F (Fin 2 → F)=2 := by simp
  rw [hcod] at hd
  have hk : Module.finrank F E.ker=1 := by omega
  let f : E.ker → (planeRadicalAmbient ⊓ MulAction.stabilizer (Sp F) v : Subgroup (Sp F)) :=
    fun B => ⟨Plane.shearSp B.val,⟨(SymplecticConjugatePair.mem_planeRadical_iff _).mpr ⟨_,rfl⟩,
      (shear_fixed_iff B.val v).mpr B.property⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro B C he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x => x.val.val.toBlocks₁₂) he
    · rintro ⟨x,hx,hfix⟩
      obtain ⟨B,rfl⟩ := (SymplecticConjugatePair.mem_planeRadical_iff x).mp hx
      exact ⟨⟨B,(shear_fixed_iff B v).mp hfix⟩,rfl⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Module.natCard_eq_pow_finrank (K := F),hk,pow_one]

omit [Finite F] [CharP F 2] in
private theorem plane_fixes (b : Sp F) (hb : b ∈ planeRadicalAmbient)
    (u : Vector F) (hu : u ∈ plane F) : b • u=u := by
  obtain ⟨B,rfl⟩ := (SymplecticConjugatePair.mem_planeRadical_iff b).mp hb
  apply (shear_fixed_iff B u).mpr
  rw [show (fun i => u (.inr i))=0 from funext hu,Matrix.mulVec_zero]

omit [Finite F] [CharP F 2] in
private theorem plane_vector_stabilizer_dimension (v : Vector F) (hv : v ∉ plane F) :
    Module.finrank F (displacementSpace
      (planeRadicalAmbient ⊓ MulAction.stabilizer (Sp F) v))=1 := by
  let A : Subgroup (Sp F) := planeRadicalAmbient ⊓ MulAction.stabilizer (Sp F) v
  let D := displacementSpace A
  let X := TwoLocalCover.fixedSpace A
  have hPX : plane F ≤ X := fun u hu b hb => plane_fixes b hb.1 u hu
  have hvX : v ∈ X := fun b hb => hb.2
  have hlt : plane F < X := lt_of_le_of_ne hPX (fun he => hv (he ▸ hvX))
  have hdimX := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_plane] at hdimX
  have hd := LinearMap.BilinForm.finrank_orthogonal
    (W := D) TwoLocalCover.form_nondegenerate
  rw [orthogonal_displacementSpace] at hd
  have hV : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hV] at hd
  change Module.finrank F X=4-Module.finrank F D at hd
  have hDle := D.finrank_le
  rw [hV] at hDle
  have hDpos : 0<Module.finrank F D := by
    by_contra hn
    have hDb : D=⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hAb : A=⊥ := by
      apply bot_unique
      intro a ha
      apply Subtype.ext
      ext i j
      have hh := Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype)
        ⟨a,ha⟩ (Pi.single j 1)
      change a • Pi.single j 1-Pi.single j 1 ∈ D at hh
      rw [hDb] at hh
      have he := congrFun (sub_eq_zero.mp hh) i
      simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,Matrix.one_apply,Pi.single_apply] using he
    have hc := plane_vector_stabilizer_card v hv
    change Nat.card A=Nat.card F at hc
    rw [hAb,Subgroup.card_bot] at hc
    have : Subsingleton F := (Nat.card_eq_one_iff_unique.mp hc.symm).1
    exact zero_ne_one (Subsingleton.elim (0 : F) 1)
  change Module.finrank F D=1
  omega

omit [Finite F] [CharP F 2] in
private theorem conjugate_plane_vector_stabilizer
    (A : Subgroup (Sp F)) (k : Sp F)
    (hk : A.map (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (v : Vector F) (hv : ∃ a ∈ A, a • v≠v) :
    Nat.card (A ⊓ MulAction.stabilizer (Sp F) v : Subgroup (Sp F))=Nat.card F ∧
      Module.finrank F (displacementSpace (A ⊓ MulAction.stabilizer (Sp F) v))=1 := by
  let C := A ⊓ MulAction.stabilizer (Sp F) v
  have hkv : k • v ∉ plane F := by
    intro hp
    obtain ⟨a,ha,hne⟩ := hv
    have he := plane_fixes ((MulAut.conj k) a) (hk ▸ mem_map_of_mem _ ha) (k • v) hp
    apply hne
    apply (toLinear k).injective
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul,toLinear_apply] using he
  have hC : C.map (MulAut.conj k).toMonoidHom=
      planeRadicalAmbient ⊓ MulAction.stabilizer (Sp F) (k • v) := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      refine ⟨hk ▸ mem_map_of_mem _ ha.1,?_⟩
      change (k*a*k⁻¹) • (k • v)=k • v
      rw [mul_smul,mul_smul,inv_smul_smul,show a • v=v from ha.2]
    · rintro b ⟨hb,hfix⟩
      obtain ⟨a,ha,rfl⟩ := hk.symm ▸ hb
      refine ⟨a,⟨ha,?_⟩,rfl⟩
      change (k*a*k⁻¹) • (k • v)=k • v at hfix
      apply (toLinear k).injective
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul,toLinear_apply] using hfix
  constructor
  · have hc := plane_vector_stabilizer_card (k • v) hkv
    rw [←hC,card_map_of_injective (MulAut.conj k).injective] at hc
    exact hc
  · have hd := plane_vector_stabilizer_dimension (k • v) hkv
    rw [←hC,displacementSpace_conjugate,(toLinear k).finrank_map_eq] at hd
    exact hd

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

private theorem embedded_plane_element_centralizer
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U T : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : T →* L (K := F))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (w : W) (hn : ∃ a : T, σ (β a) w≠w) :
    let C := T ⊓ centralizer ({j (Multiplicative.ofAdd w)} : Set G)
    Nat.card (((commutator (Sp F)).subtype.comp (β.comp (inclusion (show C ≤ T from inf_le_left)))).range)=Nat.card F ∧
      (centralizer (C : Set G)).relIndex U=Nat.card F := by
  let C := T ⊓ centralizer ({j (Multiplicative.ofAdd w)} : Set G)
  let α := (commutator (Sp F)).subtype.comp β
  let βC := β.comp (inclusion (show C ≤ T from inf_le_left))
  let αC := (commutator (Sp F)).subtype.comp βC
  have hfix (a : T) : a.val ∈ centralizer ({j (Multiplicative.ofAdd w)} : Set G) ↔
      α a • p w=p w := by
    constructor
    · intro ha
      have hw : σ (β a) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact,mem_centralizer_singleton_iff.mp ha,mul_inv_cancel_right]
      change binaryNatural (β a) (p w)=p w
      rw [←p.isIntertwining,hw]
    · intro ha
      have hw := cover_fixed_of_projection_fixed p hp (β a) w ha
      have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hw
      rw [hact,mul_inv_eq_iff_eq_mul] at he
      exact mem_centralizer_singleton_iff.mpr he
  have hr : αC.range=α.range ⊓ MulAction.stabilizer (Sp F) (p w) := by
    apply le_antisymm
    · rintro _ ⟨a,rfl⟩
      exact ⟨⟨inclusion inf_le_left a,rfl⟩,(hfix (inclusion inf_le_left a)).mp a.property.2⟩
    · rintro b ⟨⟨a,rfl⟩,ha⟩
      exact ⟨⟨a,⟨a.property,(hfix a).mpr ha⟩⟩,rfl⟩
  have hn' : ∃ a ∈ α.range, a • p w≠p w := by
    obtain ⟨a,ha⟩ := hn
    exact ⟨α a,⟨a,rfl⟩,fun he => ha (cover_fixed_of_projection_fixed p hp (β a) w he)⟩
  obtain ⟨hc,hd⟩ := conjugate_plane_vector_stabilizer α.range k hk (p w) hn'
  rw [←hr] at hc hd
  refine ⟨hc,?_⟩
  rw [cover_moving_index σ p hp U C j hj hjr βC (fun a v => hact (inclusion inf_le_left a) v)]
  change Nat.card F^Module.finrank F (displacementSpace αC.range)=Nat.card F
  rw [hd,pow_one]

private theorem embedded_plane_centralizer_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U T N : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : T →* L (K := F))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hker : ((commutator (Sp F)).subtype.comp β).ker=N.subgroupOf T)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (u : G) (hu : u ∈ U) (hnu : u ∉ centralizer (T : Set G)) :
    let C := T ⊓ centralizer ({u} : Set G)
    N.relIndex C=Nat.card F ∧ (centralizer (C : Set G)).relIndex U=Nat.card F := by
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
  have hn : ∃ b : T, σ (β b) w.toAdd≠w.toAdd := by
    by_contra hn
    push Not at hn
    apply hnu
    intro b hb
    have hh := congrArg (fun z => j (Multiplicative.ofAdd z)) (hn ⟨b,hb⟩)
    rw [hact,ofAdd_toAdd,mul_inv_eq_iff_eq_mul] at hh
    exact hh
  obtain ⟨hc,hi⟩ := embedded_plane_element_centralizer σ p hp U T j hj hjr β hact k hk w.toAdd hn
  refine ⟨?_,hi⟩
  let C := T ⊓ centralizer ({j w} : Set G)
  let α := (commutator (Sp F)).subtype.comp β
  have hr : (α.comp (inclusion (show C ≤ T from inf_le_left))).range=
      (C.subgroupOf T).map α := by rw [MonoidHom.range_comp,inclusion_range]
  change Nat.card (α.comp (inclusion (show C ≤ T from inf_le_left))).range=Nat.card F at hc
  rw [hr,←relIndex_ker,hker,relIndex_subgroupOf (show C ≤ T from inf_le_left)] at hc
  exact hc

private theorem embedded_commutator_central_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A C : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ C) :
    C.relIndex ⁅A,U⁆ = (centralizer (A : Set G)).relIndex U := by
  let α := (commutator (Sp F)).subtype.comp β
  let D := displacementSpace α.range
  let D₀ : Subgroup (Multiplicative (Vector F)) := AddSubgroup.toSubgroup' D.toAddSubgroup
  obtain ⟨π,hπ⟩ := exists_embedded_projection U j hj hjr p.toLinearMap
  have hAU : ⁅A,U⁆ ≤ U := by
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨v,rfl⟩ := hjr.symm ▸ hu
    have he : ⁅a,j v⁆=j (Multiplicative.ofAdd (σ (β ⟨a,ha⟩) v.toAdd-v.toAdd)) := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    rw [he]
    exact hjr ▸ ⟨_,rfl⟩
  have hk : π.ker=C.subgroupOf U := by
    ext u
    obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
    have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    subst u
    change π ⟨j w,_⟩=1 ↔ j w ∈ C
    have hπw := hπ w.toAdd
    change π ⟨j w,_⟩ = Multiplicative.ofAdd (p w.toAdd) at hπw
    rw [hπw]
    exact hker w.toAdd
  have hpre : ⁅A,U⁆ ≤ (D₀.comap π).map U.subtype := by
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨v,rfl⟩ := hjr.symm ▸ hu
    let w := σ (β ⟨a,ha⟩) v.toAdd-v.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd w),hjr ▸ ⟨_,rfl⟩⟩,?_,?_⟩
    · change π ⟨j (Multiplicative.ofAdd w),_⟩ ∈ D₀
      rw [hπ]
      change p w ∈ D
      dsimp only [w]
      rw [map_sub,p.isIntertwining]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp α.range.subtype)
        ⟨α ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ (p v.toAdd)
    · change j (Multiplicative.ofAdd w)=⁅a,j v⁆
      dsimp only [w]
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hm : (⁅A,U⁆.subgroupOf U).map π=D₀ := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hpre hx
      have he : y=x := Subtype.ext hyx
      exact he ▸ hy
    · intro v hv
      obtain ⟨w,hw,hwc⟩ := natural_displacement_lifts U A j hjr β σ hact p hp.1 v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),hAU hwc⟩,hwc,?_⟩
      rw [hπ]
      change Multiplicative.ofAdd (p w)=v
      rw [hw,ofAdd_toAdd]
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
  have hic : 2 ^ fixedCodim (binaryNatural (K := F)) β.range = Nat.card D := by
    change 2 ^ Module.finrank (ZMod 2) (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace α.range)).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    rw [hc,fixed_quotient_card]
    exact (Module.natCard_eq_pow_finrank (K := F) (V := D)).symm
  rw [←relIndex_subgroupOf hAU,←hk,relIndex_ker,hm,hi,hic]
  exact Nat.card_congr {
    toFun := fun x => ⟨x.val.toAdd,x.property⟩
    invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }


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
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H : Type*} [Group H] [Finite H]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private theorem moving_factor_not_central
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    ∃ u ∈ U d.radical a,
      Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=
        Q d.radical t ⊓ centralizer ({u} : Set (FreeAmalgam d.radical)) ∧
      u ∉ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (ha.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  have hZX : Z d.radical a ≤ X d.radical a :=
    g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b d.radical; omega)
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans (hZX.trans (omegaCenter_le _))
  have hUn : U d.radical a ≤ normalizer (Z d.radical t : Set (FreeAmalgam d.radical)) :=
    ((hUQ.trans c.core_le_edge).trans (le_centralizer_iff.mp hcentral)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hx' := hx
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb ha hat,←SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hUn] at hx'
  obtain ⟨u,hu,v,hv,rfl⟩ := hx'
  refine ⟨u,hu,?_,?_⟩
  · ext b
    simp only [mem_inf,mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hb,hbcomm⟩
      refine ⟨hb,?_⟩
      apply mul_right_cancel (b := v)
      calc
        b*u*v = b*(u*v) := mul_assoc _ _ _
        _ = u*v*b := hbcomm
        _ = u*b*v := by rw [mul_assoc,←hcentral hv b hb,←mul_assoc]
    · rintro ⟨hb,hbcomm⟩
      refine ⟨hb,?_⟩
      calc
        b*(u*v) = (b*u)*v := (mul_assoc _ _ _).symm
        _ = (u*b)*v := by rw [hbcomm]
        _ = (u*v)*b := by rw [mul_assoc,hcentral hv b hb,←mul_assoc]
  · intro hfix
    apply hne
    rw [hZt]
    exact mem_omegaCenter_iff.mpr ⟨c.core_le_edge (omegaCenter_le _ (hZX hx)),
      (mem_omegaCenter_iff.mp (hZX hx)).2.1,
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).mul_mem hfix (hcentral hv)⟩

/-- The actual element centralizer in a full plane radical has field order
modulo the entire endpoint core and moves exactly q cosets of U. -/
theorem plane_cover_element_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    (Q d.radical a).relIndex C=2^n ∧
      (centralizer (C : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=2^n := by
  obtain ⟨u,hu,hC,hnu⟩ := moving_factor_not_central h d g hb ha hat c x hx hne
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,⟨k,hk⟩⟩
  have hc := embedded_plane_centralizer_index
    (MovedSection.coverAction (replacementMovedSection h d) e)
    (MovedSection.coverProjection (replacementMovedSection h d) e) he
    (U d.radical a) (Q d.radical t) (Q d.radical a) j hj hjr β hact hαker k hk u hu hnu
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  dsimp only at hc ⊢
  rw [hEc] at hc
  rw [hC]
  exact hc

private theorem omega_displacement_attachment_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (c : EdgeMarking h d a t) (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t) :
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅X d.radical a,B⁆ =
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅U d.radical a,B⁆ := by
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let D := fixedCore d.radical a
  let M := ⁅U d.radical a,B⁆
  let N := ⁅X d.radical a,B⁆
  have hXQ : X d.radical a ≤ Q d.radical a := omegaCenter_le _
  have hZX := g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b d.radical; omega)
  have hUX : U d.radical a ≤ X d.radical a := (U_le_Z a).trans hZX
  have hMU : M ≤ U d.radical a := by
    change ⁅U d.radical a,B⁆ ≤ U d.radical a
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp ((hBT.trans c.edge_le).trans (U_normalized a))
  have hNU : N ≤ U d.radical a := by
    change ⁅X d.radical a,B⁆ ≤ U d.radical a
    rw [commutator_comm]
    apply (commutator_mono (hBT.trans c.edge_le) le_rfl).trans
    rw [←c.residual_sup_core g (by omega)]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Ltilde d.radical a) (Q d.radical a) (X d.radical a) (U d.radical a)
      (U_normalized a) (Ltilde_le_stabilizer _) (fun _ hx => hx.1)
    · rw [commutator_comm]
      exact (commutator_mono hXQ le_rfl).trans
        (replacement_core_eq_U_of_distance_two h d g hb ha).le
    · rw [commutator_comm]
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (show X d.radical a ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) from
          fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)).le.trans bot_le
  have hMN : M ≤ N := commutator_mono hUX le_rfl
  have hUD : U d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))).trans
      (centralizer_le inf_le_left)
  have hbound : N ≤ M ⊔ A := by
    intro x hx
    have hprod := ((commutator_mono hXQ le_rfl).trans
      (whole_core_displacement_le h d g hb ha B (hBT.trans c.edge_le))) hx
    change x ∈ M ⊔ D at hprod
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
      ((hMU.trans hUD).trans (Subgroup.centralizer_le_normalizer _))] at hprod
    obtain ⟨v,hv,w,hw,rfl⟩ := hprod
    have hwU : w ∈ U d.radical a := by
      have hh := (U d.radical a).mul_mem ((U d.radical a).inv_mem (hMU hv)) (hNU hx)
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨hwU,hw.2⟩)
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNU) (inclusion_injective _)
  let : Finite A := Finite.of_injective
    (inclusion (show A ≤ U d.radical a from inf_le_left)) (inclusion_injective _)
  let : Finite (M ⊔ A : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion (sup_le hMU (show A ≤ U d.radical a from inf_le_left))) (inclusion_injective _)
  let : IsElementaryAbelian 2 (U d.radical a) := replacement_vertex_moving_elementary h d ha
  have hAM : A ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
    ((show A ≤ U d.radical a from inf_le_left).trans
      ((U d.radical a).le_centralizer.trans (centralizer_le hMU))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact le_antisymm
    ((relIndex_le_of_le_right hbound index_ne_zero_of_finite).trans_eq
      (relIndex_sup_of_normalizes M A hAM))
    (relIndex_le_of_le_right hMN index_ne_zero_of_finite)

private theorem plane_cover_omega_displacement_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (c : EdgeMarking h d a t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t) :
    (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅X d.radical a,B⁆ = (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
  rw [omega_displacement_attachment_index h d g hb ha c B hBT,commutator_comm]
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  apply embedded_commutator_central_index
    (MovedSection.coverAction (replacementMovedSection h d) e)
    (MovedSection.coverProjection (replacementMovedSection h d) e) he
    (U d.radical a) B _ j hj hjr (β.comp (inclusion hBT))
    (fun b w => hact (inclusion hBT b) w)
  intro w
  exact (hker w).trans ⟨fun hc => ⟨hjr ▸ ⟨_,rfl⟩,hc⟩,fun hc => hc.2⟩

/-- The full central-omega movement in the plane branch of source (5).
The quotient is by the complete attachment, not just its natural image. -/
theorem source_five_large_omega_displacement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    (Q d.radical a).relIndex C=2^n ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
        ⁅X d.radical a,C⁆=2^n := by
  obtain ⟨⟨cv⟩,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hc := plane_cover_element_centralizer h d g hb path.start_color hat c cv x hx hne
  exact ⟨hc.1,(plane_cover_omega_displacement_index h d g hb path.start_color c cv
    (Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))) inf_le_left).trans hc.2⟩

/-- The actual Q₂ centralizer count in the large critical-image branch,
with the original plane cover constructed from saturation and source (2). -/
theorem source_five_large_element_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a) (hne : x ∉ Z d.radical t) :
    let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    (Q d.radical a).relIndex C=2^n ∧
      (centralizer (C : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=2^n ∧
      (centralizer (C : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=2^n := by
  obtain ⟨⟨cv⟩,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hc := plane_cover_element_centralizer h d g hb path.start_color hat c cv x hx hne
  refine ⟨hc.1,hc.2,?_⟩
  let C := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
  let := finite_Z d.radical a
  let := g.Z_elementary (by omega) a path.start_color
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hcentral : Z d.radical t ≤ centralizer (C : Set (FreeAmalgam d.radical)) := by
    intro v hv b hbq
    have hv' : v ∈ omegaCenter (Q d.radical t) := by simpa [Z,ht,edgeOmega] using hv
    exact (mem_omegaCenter_iff.mp hv').2.2 b hbq.1
  exact (central_supplement_fixed_index (U d.radical a) (Z d.radical t)
    (Z d.radical a) C (U_le_Z a) (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
    (Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat) hcentral).trans hc.2

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
