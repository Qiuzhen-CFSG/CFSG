module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourPlane
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# Hyperplanes and full attachments in the large critical-image branch

In plane-radical coordinates, the fixer of the hyperplane perpendicular to
its first point is the full long root. Its displacement H is the preimage
of that point in the original central cover. The subgroup centralizing the
hyperplane modulo H is the intersection with the point radical. Its movement
is the pure natural point: it has order q and is disjoint from the complete
cover kernel. Consequently H is the direct product of that movement and the
entire attachment. The proof descends from the universal orthogonal cover;
no splitting of the given cover is used.

Transport retains any specified plane marking. The source application uses
the genuinely saturated radical, adjoins the central midpoint supplement,
and constructs a full Z-hyperplane of index q containing the midpoint and
the common displacement. Both centralizers are characterized inside the
literal common radical, and H lies in the original critical commutator.

This establishes the hyperplane decomposition used at the start of the
large-image argument in MS93 (3.7)(4), printed p.875. Comparing the opposite
attachment through these hyperplanes, source (5)/(6), and the field-four
restriction remain open. Source: Meierfrankenfeld--Stellmacher, *Pushing up
weak BN-pairs of rank two* (1993). The private root and point transports
adapt the project's RootOverlap and SourceFourCommonOverlap calculations.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
section Model
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}
omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem point_radical_of_hyperplane_movement (g : Sp F)
    (hfix : g • e (F := F) 0=e 0)
    (hmove : ∀ v : Vector F, v (.inr 0)=0 → g • v-v ∈ point F) :
    g ∈ pointRadicalAmbient := by
  let g' : pointLocal (F := F) := ⟨g,(mem_pointLocal_iff_fixed g).mpr hfix⟩
  refine ⟨g',?_,rfl⟩
  change pointQuotient g'=1
  apply Subtype.ext
  ext i j
  have hj : (Pi.single (middleIndex j) (1:F) : Vector F) (.inr 0)=0 := by
    fin_cases j <;> simp [middleIndex]
  have hm := (mem_point_iff _).mp (hmove (Pi.single (middleIndex j) 1) hj)
  have he : ((g • (Pi.single (middleIndex j) (1:F) : Vector F)-Pi.single (middleIndex j) 1 : Vector F))
      (middleIndex i)=0 := by
    fin_cases i
    · exact hm.1
    · exact hm.2 1
  change pointQuotientMatrix g' i j=(1 : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simpa [pointQuotientMatrix,middleIndex,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
      g',sub_eq_zero] using he

private theorem standard_root_fixed_iff
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (hTY : T ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) ↔
      p w ∈ (form F).orthogonal (point F) := by
  rw [←PointRadicalAction.root_displacement,orthogonal_displacementSpace]
  constructor
  · intro hw a ha
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := hT.symm ▸ ha
    have he : σ (β (inclusion hTY t)) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact]
      change t.val*j (Multiplicative.ofAdd w)*t.val⁻¹=_
      rw [hw t.val t.property,mul_inv_cancel_right]
    have he' := congrArg p he
    rw [p.isIntertwining] at he'
    exact ht ▸ he'
  · intro hw t ht
    have hmem : (β (inclusion hTY ⟨t,ht⟩)).val ∈ RootSubgroup.group 0 :=
      hT ▸ mem_map_of_mem _ (show β (inclusion hTY ⟨t,ht⟩) ∈
        (β.comp (inclusion hTY)).range from ⟨_,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w))
      (cover_fixed_of_projection_fixed p hp (β (inclusion hTY ⟨t,ht⟩)) w (hw _ hmem))
    rw [hact,mul_inv_eq_iff_eq_mul] at he
    exact he

private theorem standard_root_preimage_displacement
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (Y T : Subgroup G) (hTY : T ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) (hw : p w ∈ point F) : j (Multiplicative.ofAdd w) ∈ ⁅T,j.range⁆ := by
  have hw' : w ∈ Coinvariants.ker (σ.comp Roots.group.subtype) :=
    (Roots.cover_root_geometry hF p hp).2.1 ▸ hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨a,v⟩,rfl⟩ := hw
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := (show a.val.val ∈
        (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype from hT.symm ▸ a.property)
    have he : β (inclusion hTY t)=a.val := Subtype.ext ht
    change j (Multiplicative.ofAdd (σ a.val v-v)) ∈ ⁅T,j.range⁆
    rw [ofAdd_sub,map_div,div_eq_mul_inv,←he,hact]
    exact commutator_mem_commutator t.property (show j (Multiplicative.ofAdd v) ∈ j.range from ⟨_,rfl⟩)
  | zero => simp only [ofAdd_zero,map_one,one_mem]
  | add x y _ _ hx hy =>
    rw [ofAdd_add,map_mul]
    exact (⁅T,j.range⁆).mul_mem hx hy
  | smul c v _ hv =>
    fin_cases c
    · change j (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simp only [zero_smul,ofAdd_zero,map_one,one_mem]
    · change j (Multiplicative.ofAdd ((1 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simpa only [one_smul] using hv


omit [Algebra (ZMod 2) F] in
private theorem point_correction (u v z : F) (x : Natural (K := F))
    (hx : x (.inr 0)=0) : correction (pointRadicalElement u v z).val x = 0 := by
  simp [correction, quadraticCocycle, transposeSp, pointRadicalElement, pointRadicalMatrix,
    rowQuadratic, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, hx]

private theorem point_hyperplane_displacement (g : L (K := F))
    (hg : g.val ∈ ((pointRadical (F := F)).map pointLocal.subtype)) (x : Space (K := F)) (hx : x.1 (.inr 0)=0) :
    ∃ t : F, binaryAction g x-x=(t • ClassicalOrthogonal.e 0,0) := by
  obtain ⟨b,hb,he⟩ := hg
  have hb' := pointRadical_eq_element b hb
  have he' : g.val=(pointRadicalElement
      (b.val.val (.inl 1) (.inr 0)) (b.val.val (.inr 1) (.inr 0))
      (b.val.val (.inl 0) (.inr 0))).val := he.symm.trans (congrArg Subtype.val hb')
  let u := b.val.val (.inl 1) (.inr 0)
  let v := b.val.val (.inr 1) (.inr 0)
  let z := b.val.val (.inl 0) (.inr 0)
  refine ⟨v*x.1 (.inl 1)+u*x.1 (.inr 1),?_⟩
  change action g x-x=_
  rw [action_apply]
  change (g.val.val *ᵥ x.1,x.2+correction g.val x.1)-x=_
  rw [he',point_correction u v z x.1 hx]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,hx,ClassicalOrthogonal.e,u,v,add_assoc]
  · simp


private theorem cover_plane_point_overlap (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p) :
    ∃ s : F →ₗ[ZMod 2] W,
      (∀ t, p (s t)=t • ClassicalOrthogonal.e 0) ∧
      (∀ (g : L (K := F)), g.val ∈ pointRadicalAmbient → ∀ w : W,
        (p w) (.inr 0)=0 → σ g w-w ∈ s.range) ∧
      (∀ t : F, ∃ (g : L (K := F)) (w : W),
        g.val ∈ planeRadicalAmbient ∧ g.val ∈ pointRadicalAmbient ∧
          (p w) (.inr 0)=0 ∧ σ g w-w=s t) := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let l : F →ₗ[F] Space (K := F) :=
    { toFun t := (t • ClassicalOrthogonal.e 0,0)
      map_add' a b := by simp [add_smul]
      map_smul' a b := by simp [mul_smul] }
  let s := f.toLinearMap.comp (l.restrictScalars (ZMod 2))
  refine ⟨s,fun t => hpf (t • ClassicalOrthogonal.e 0,0),?_,?_⟩
  · intro g hg w hw
    obtain ⟨x,rfl⟩ := hf w
    have hx : x.1 (.inr 0)=0 := by rw [hpf] at hw; exact hw
    obtain ⟨t,ht⟩ := point_hyperplane_displacement g hg x hx
    refine ⟨t,?_⟩
    change f (t • ClassicalOrthogonal.e 0,0)=σ g (f x)-f x
    rw [←f.isIntertwining,←map_sub,ht]
  · intro t
    let g : L (K := F) := ⟨(pointRadicalElement t 0 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    let x : Space (K := F) := (ClassicalOrthogonal.f 1,0)
    refine ⟨g,f x,?_,mem_map_of_mem _ (pointRadicalElement_mem t 0 0),?_,?_⟩
    · apply (SymplecticConjugatePair.mem_planeRadical_iff _).mpr
      refine ⟨⟨!![0,t;t,0],by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩,?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g,Plane.shearSp,pointRadicalElement,
        pointRadicalMatrix,Matrix.fromBlocks]
    · rw [hpf]
      change (ClassicalOrthogonal.f 1 : Natural (K := F)) (.inr 0)=0
      rfl
    · rw [←f.isIntertwining,←map_sub]
      apply congrArg f
      change action g x-x=(t • ClassicalOrthogonal.e 0,0)
      rw [action_apply]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [g,x,pointRadicalElement,pointRadicalMatrix,Matrix.fromBlocks,
          ClassicalOrthogonal.e,ClassicalOrthogonal.f]
      · change (0+correction (pointRadicalElement t 0 0).val (ClassicalOrthogonal.f 1))-0=0
        rw [point_correction t 0 0 (ClassicalOrthogonal.f 1) (by simp [ClassicalOrthogonal.f])]
        simp
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
private theorem standard_plane_hyperplane
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y : Subgroup G) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hY : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient) :
    ∃ P B : Subgroup G, P ≤ Y ∧ B ≤ Y ∧
      P=Y ⊓ centralizer (j.range ⊓ centralizer (P : Set G) : Set G) ∧
      (centralizer (P : Set G)).relIndex j.range=Nat.card F ∧
      (∀ w : W, j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
        (p w) (.inr 0)=0) ∧
      (∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j.range ⊓ centralizer (P : Set G),
        ⁅b,x⁆ ∈ ⁅P,j.range⁆) ∧
      Disjoint ⁅j.range ⊓ centralizer (P : Set G),B⁆
        (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) ∧
      Nat.card (⁅j.range ⊓ centralizer (P : Set G),B⁆ : Subgroup G)=Nat.card F ∧
      ⁅P,j.range⁆ = ⁅j.range ⊓ centralizer (P : Set G),B⁆ ⊔
        p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j := by
  let ψ := (commutator (Sp F)).subtype.comp β
  let P := ((RootSubgroup.group 0).comap ψ).map Y.subtype
  let B := ((pointRadicalAmbient (F := F)).comap ψ).map Y.subtype
  have hPY : P ≤ Y := map_subtype_le _
  have hBY : B ≤ Y := map_subtype_le _
  have hpm (y : Y) : y.val ∈ P ↔ ψ y ∈ RootSubgroup.group 0 :=
    mem_map_iff_mem Y.subtype_injective
  have hbm (y : Y) : y.val ∈ B ↔ ψ y ∈ pointRadicalAmbient :=
    mem_map_iff_mem Y.subtype_injective
  have hrY : RootSubgroup.group (F := F) 0 ≤ planeRadicalAmbient := by
    intro r hr
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 _).mp hr
    apply (SymplecticConjugatePair.mem_planeRadical_iff _).mpr
    refine ⟨⟨!![t,0;0,0],by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Plane.shearSp,rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single]
  have hP : (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype =
      RootSubgroup.group 0 := by
    apply le_antisymm
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      exact (hpm (inclusion hPY x)).mp x.property
    · intro x hx
      obtain ⟨y,hy⟩ := (show x ∈ ψ.range from hY.symm ▸ hrY hx)
      exact ⟨β y,⟨⟨y.val,(hpm y).mpr (hy ▸ hx)⟩,rfl⟩,hy⟩
  have hfix (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (p w) (.inr 0)=0 := by
    rw [standard_root_fixed_iff p hp j hj Y P hPY β hact hP]
    constructor
    · intro hw
      have he := hw (e 0) (Submodule.subset_span (Set.mem_singleton _))
      simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
    · intro hw v hv
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp [form_apply,Theory.SpecificGroups.SymplecticFour.e,hw]
  let X := j.range ⊓ centralizer (P : Set G)
  let A := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let N := (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hN : ⁅P,j.range⁆=N := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro b hb u hu
      obtain ⟨w,rfl⟩ := hu
      refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hPY hb⟩) w.toAdd-w.toAdd),?_,?_⟩
      · change p (σ (β ⟨b,hPY hb⟩) w.toAdd-w.toAdd) ∈ point F
        rw [map_sub,p.isIntertwining]
        obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp ((hpm ⟨b,hPY hb⟩).mp hb)
        change rootElement 0 t=(β ⟨b,hPY hb⟩).val at ht
        change (β ⟨b,hPY hb⟩).val.val *ᵥ p w.toAdd-p w.toAdd ∈ point F
        rw [←ht,Roots.natural_root,add_sub_cancel_left]
        exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
      · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
        rfl
    · rintro _ ⟨w,hw,rfl⟩
      exact standard_root_preimage_displacement hF p hp j Y P hPY β hact hP w.toAdd hw
  obtain ⟨s,hs,hsmove,hsurj⟩ := cover_plane_point_overlap hF p hp
  let f : Multiplicative F →* G := j.comp s.toAddMonoidHom.toMultiplicative
  have hfi : Function.Injective f := by
    intro x y he
    have hxy : s x.toAdd=s y.toAdd := congrArg Multiplicative.toAdd (hj he)
    have hh := congrArg (fun w => (p w) (.inl 0)) hxy
    exact Multiplicative.toAdd.injective (by simpa [hs,ClassicalOrthogonal.e] using hh)
  have hD : ⁅X,B⁆=f.range := by
    rw [commutator_comm]
    apply le_antisymm
    · apply commutator_le.mpr
      intro b hb u hu
      obtain ⟨w,rfl⟩ := hu.1
      obtain ⟨t,ht⟩ := hsmove (β ⟨b,hBY hb⟩) ((hbm ⟨b,hBY hb⟩).mp hb)
        w.toAdd ((hfix w.toAdd).mp hu.2)
      refine ⟨Multiplicative.ofAdd t,?_⟩
      change j (Multiplicative.ofAdd (s t))=⁅b,j w⁆
      rw [ht,ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    · rintro _ ⟨t,rfl⟩
      obtain ⟨b,w,hbY,hbP,hw,he⟩ := hsurj t.toAdd
      obtain ⟨y,hy⟩ := (show b.val ∈ ψ.range from hY.symm ▸ hbY)
      have hβ : β y=b := Subtype.ext hy
      have hyB : y.val ∈ B := (hbm y).mpr (hy ▸ hbP)
      have hcomm : ⁅y.val,j (Multiplicative.ofAdd w)⁆=f t := by
        have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) he
        rw [ofAdd_sub,map_div,div_eq_mul_inv,←hβ,hact] at hh
        exact hh
      rw [←hcomm]
      exact commutator_mem_commutator hyB ⟨⟨_,rfl⟩,(hfix w).mpr hw⟩
  have hDN : ⁅X,B⁆ ≤ N := by
    rw [hD]
    rintro _ ⟨t,rfl⟩
    refine ⟨Multiplicative.ofAdd (s t.toAdd),?_,rfl⟩
    change p (s t.toAdd) ∈ point F
    rw [hs]
    exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
  have hpointwise : P=Y ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · exact le_inf hPY (le_centralizer_iff.mp inf_le_right)
    · rintro b ⟨hb,hbc⟩
      apply (hpm ⟨b,hb⟩).mpr
      rw [←PointRadicalAction.hyperplane_fixer]
      apply (mem_fixingSubgroup_iff _).mpr
      intro v hv
      obtain ⟨w,rfl⟩ := hp.1 v
      have hv0 : (p w) (.inr 0)=0 := by
        have he := hv (e 0) (Submodule.subset_span (Set.mem_singleton _))
        simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
      have hw : j (Multiplicative.ofAdd w) ∈ X := ⟨⟨_,rfl⟩,(hfix w).mpr hv0⟩
      have he : σ (β ⟨b,hb⟩) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact,←hbc _ hw,mul_inv_cancel_right]
      have hh := congrArg p he
      rw [p.isIntertwining] at hh
      exact hh
  have hindex : (centralizer (P : Set G)).relIndex j.range=Nat.card F := by
    rw [cover_moving_index σ p hp j.range P j hj rfl (β.comp (inclusion hPY))
      (fun x w => hact (inclusion hPY x) w),MonoidHom.range_comp,hP,
      PointRadicalAction.root_displacement,finrank_point,pow_one]
  refine ⟨P,B,hPY,hBY,hpointwise,hindex,hfix,?_,?_,?_,?_⟩
  · intro b
    constructor
    · intro hb
      refine ⟨hBY hb,fun x hx => ?_⟩
      rw [hN]
      apply hDN
      rw [commutator_comm]
      exact commutator_mem_commutator hb hx
    · rintro ⟨hb,hm⟩
      apply (hbm ⟨b,hb⟩).mpr
      apply point_radical_of_hyperplane_movement
      · have hy : ψ ⟨b,hb⟩ ∈ planeRadicalAmbient := hY ▸ ⟨⟨b,hb⟩,rfl⟩
        obtain ⟨D,hD⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp hy
        change (β ⟨b,hb⟩).val • e 0=e 0
        change Plane.shearSp D=(β ⟨b,hb⟩).val at hD
        rw [←hD]
        ext i
        fin_cases i <;> simp [Plane.shearSp,Theory.SpecificGroups.SymplecticFour.e,
          Matrix.fromBlocks,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two]
      · intro v hv
        obtain ⟨w,rfl⟩ := hp.1 v
        have hx : j (Multiplicative.ofAdd w) ∈ X := ⟨⟨_,rfl⟩,(hfix w).mpr hv⟩
        obtain ⟨u,hu,he⟩ := hN ▸ hm _ hx
        have hu' : u=Multiplicative.ofAdd (σ (β ⟨b,hb⟩) w-w) := by
          apply hj
          rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
          exact he
        rw [hu'] at hu
        change p (σ (β ⟨b,hb⟩) w-w) ∈ point F at hu
        rwa [map_sub,p.isIntertwining] at hu
  · rw [hD,disjoint_iff_inf_le]
    rintro x ⟨⟨t,ht⟩,⟨w,hw,he⟩⟩
    have htw : s t.toAdd=w.toAdd := congrArg Multiplicative.toAdd (hj (ht.trans he.symm))
    have hz : t.toAdd=0 := by
      have hh := congrArg (fun v => (p v) (.inl 0)) htw
      simpa [hs,show p w.toAdd=0 from hw,ClassicalOrthogonal.e] using hh
    change x=1
    rw [←ht,show t=1 from Multiplicative.toAdd.injective hz,map_one]
  · rw [hD]
    exact (Nat.card_range_of_injective hfi).trans (Nat.card_congr Multiplicative.toAdd)
  · rw [hN]
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
      have hker : j (Multiplicative.ofAdd (w.toAdd-s t)) ∈ A := by
        refine ⟨_,?_,rfl⟩
        change p (w.toAdd-s t)=0
        rw [map_sub,hs]
        change p w.toAdd-t • Theory.SpecificGroups.SymplecticFour.e 0=0
        exact sub_eq_zero.mpr ht.symm
      have hline : j (Multiplicative.ofAdd (s t)) ∈ ⁅X,B⁆ := hD.symm ▸ ⟨Multiplicative.ofAdd t,rfl⟩
      have hh := (⁅X,B⁆ ⊔ A).mul_mem (mem_sup_left hline) (mem_sup_right hker)
      rw [←map_mul,←ofAdd_add,show s t+(w.toAdd-s t)=w.toAdd by abel] at hh
      exact hh
    · apply sup_le hDN
      rintro _ ⟨w,hw,rfl⟩
      refine ⟨w,?_,rfl⟩
      change p w.toAdd ∈ point F
      rw [show p w.toAdd=0 from hw]
      exact zero_mem _
private theorem plane_hyperplane
    (hlarge : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j₀ : Multiplicative W →* G) (hj₀ : Function.Injective j₀)
    (Y : Subgroup G) (β₀ : Y →* L (K := F))
    (hact₀ : ∀ (y : Y) (w : W), j₀ (Multiplicative.ofAdd (σ (β₀ y) w)) =
      y.val*j₀ (Multiplicative.ofAdd w)*y.val⁻¹)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β₀).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient) :
    ∃ P B : Subgroup G, P ≤ Y ∧ B ≤ Y ∧
      P=Y ⊓ centralizer (j₀.range ⊓ centralizer (P : Set G) : Set G) ∧
      (centralizer (P : Set G)).relIndex j₀.range=Nat.card F ∧
      (∀ w : W, j₀ (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
        (k • p w) (.inr 0)=0) ∧
      (∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j₀.range ⊓ centralizer (P : Set G),
        ⁅b,x⁆ ∈ ⁅P,j₀.range⁆) ∧
      Disjoint ⁅j₀.range ⊓ centralizer (P : Set G),B⁆
        (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀) ∧
      Nat.card (⁅j₀.range ⊓ centralizer (P : Set G),B⁆ : Subgroup G)=Nat.card F ∧
      ⁅P,j₀.range⁆ = ⁅j₀.range ⊓ centralizer (P : Set G),B⁆ ⊔
        p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀ := by
  let kl : L (K := F) := ⟨k,by rw [LargeField.commutator_eq_top hlarge]; trivial⟩
  let β := (MulAut.conj kl).toMonoidHom.comp β₀
  let j := j₀.comp (σ kl⁻¹).toAddMonoidHom.toMultiplicative
  have hj : Function.Injective j := hj₀.comp
    (fun x y hxy => Multiplicative.toAdd.injective
      ((σ.apply_bijective kl⁻¹).1 (congrArg Multiplicative.toAdd hxy)))
  have hjr : j.range=j₀.range := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact ⟨_,rfl⟩
    · intro u hu
      obtain ⟨w,rfl⟩ := hu
      obtain ⟨v,hv⟩ := (σ.apply_bijective kl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j₀ (congrArg Multiplicative.ofAdd hv)⟩
  have hact (x : Y) (w : W) :
      j (Multiplicative.ofAdd (σ (β x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j₀ (Multiplicative.ofAdd (σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)))=_
    have he : σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)=σ (β₀ x) (σ kl⁻¹ w) := by
      simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    rw [he]
    exact hact₀ x (σ kl⁻¹ w)
  have hβ : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient := by
    have he : (commutator (Sp F)).subtype.comp β=
        (MulAut.conj k).toMonoidHom.comp ((commutator (Sp F)).subtype.comp β₀) := by
      ext x
      rfl
    rw [he,MonoidHom.range_comp]
    exact hk
  have hzero (w : W) : p (σ kl⁻¹ w)=0 ↔ p w=0 := by
    rw [p.isIntertwining]
    exact ⟨fun hh => (binaryNatural.apply_bijective kl⁻¹).1 (hh.trans (map_zero _).symm),
      fun hh => by rw [hh,map_zero]⟩
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀ := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨Multiplicative.ofAdd (σ kl⁻¹ w.toAdd),(hzero _).mpr hw,rfl⟩
    · rintro x ⟨w,hw,rfl⟩
      obtain ⟨v,hv⟩ := (σ.apply_bijective kl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,(hzero _).mp (hv.symm ▸ hw),
        congrArg j₀ (congrArg Multiplicative.ofAdd hv)⟩
  obtain ⟨P,B,hP,hB,hpoint,hindex,hfix,hmem,hdis,hcard,hjoin⟩ :=
    standard_plane_hyperplane hlarge p hp j hj Y β hact hβ
  rw [hk] at hdis hjoin
  rw [hjr] at hpoint hindex hmem hdis hcard hjoin
  refine ⟨P,B,hP,hB,hpoint,hindex,?_,hmem,hdis,hcard,hjoin⟩
  intro w
  have hf := hfix (σ kl w)
  have hjw : j (Multiplicative.ofAdd (σ kl w))=j₀ (Multiplicative.ofAdd w) := by
    change j₀ (Multiplicative.ofAdd (σ kl⁻¹ (σ kl w)))=_
    rw [inv_self_apply]
  rw [hjw,p.isIntertwining] at hf
  exact hf

end Model
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- For each supplied plane marking, the corresponding natural hyperplane's
section centralizer moves it in a field-sized complement to the whole attachment.
The coordinate criterion uses the original projection and the specified marking. -/
theorem plane_cover_hyperplane_attachment
    {z t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient) :
    ∃ P B : Subgroup (FreeAmalgam d.radical), P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer
        (U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      (centralizer (P : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)=2^n ∧
      (∀ w : (replacementMovedSection h d).space.toSubmodule,
        cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam d.radical)) ↔
          (k • MovedSection.coverProjection (replacementMovedSection h d) cv.equiv w) (.inr 0)=0) ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
        ∀ x ∈ U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
          ⁅b,x⁆ ∈ ⁅P,U d.radical z⁆) ∧
      Disjoint ⁅U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆
        (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ∧
      Nat.card (⁅U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆ :
        Subgroup (FreeAmalgam d.radical))=2^n ∧
      ⁅P,U d.radical z⁆ =
        ⁅U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆ ⊔
          (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) := by
  have hEc : Nat.card cv.field.Carrier=2^n :=
    cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hEc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  have hker : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  simpa only [cv.range_eq,hEc,hker] using
    plane_hyperplane hlarge p cv.cover cv.embedding cv.injective
      (Q d.radical t) cv.actor cv.actor_conjugation k hk

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu

/-- The full Z-hyperplane decomposition in the large critical-image branch
of MS93 (3.7)(4). Both centralizers are literal subgroups of the common radical;
the field-sized displacement complements the complete fixed attachment. -/
theorem source_four_large_hyperplane_attachment
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨P,B,hP,hB,hpoint,hindex,_,hmem,hdis,hcard,hjoin⟩ :=
    plane_cover_hyperplane_attachment h d cv k hk
  let C := Z d.radical t
  let V := U d.radical z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X₁ := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Q d.radical t
  have hgen : Z d.radical z=V ⊔ C :=
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hC : C=omegaCenter Y := by simp [C,Y,Z,ht,edgeOmega]
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [hC]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hCU : C ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam d.radical)) := hCY.trans (centralizer_le hP)
  have hX : X₁=X₀ ⊔ C := by
    dsimp only [X₁,X₀]
    rw [hgen,sup_comm V C,inf_centralizer_sup_of_centralizing C V P hCU hCP,sup_comm]
  have hHZ : ⁅Z d.radical z,P⁆=⁅P,V⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement V C Y P hCU hCY hP
  have hXB : ⁅X₁,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C Y B hCX hCY hB,
      commutator_comm]
  have hpointZ : P=Y ⊓ centralizer (X₁ : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
    · exact (inf_le_inf_left Y (centralizer_le
        (show X₀ ≤ X₁ from hX ▸ le_sup_left))).trans hpoint.ge
  have hQ : Q d.radical z ≤ P := by
    rw [hpointZ]
    apply le_inf c'.core_le_edge
    exact le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color)))
  have hi : X₁.relIndex (Z d.radical z)=2^n := by
    let := finite_Z d.radical z
    let : Finite X₁ := Finite.of_injective (inclusion (show X₁ ≤ Z d.radical z from inf_le_left))
      (inclusion_injective _)
    have hVX : V ⊔ X₁=Z d.radical z := by
      rw [hX,←sup_assoc,sup_eq_left.mpr (show X₀ ≤ V from inf_le_left),←hgen]
    have hXU : X₁ ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [←hVX,relIndex_sup_of_normalizes V X₁ hXU]
    have hInf : X₁ ⊓ V=X₀ := by
      ext x
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨U_le_Z z hx.1,hx.2⟩,hx.1⟩⟩
    rw [←inf_relIndex_right,hInf,inf_relIndex_left]
    exact hindex
  have hCX₁ : C ≤ X₁ := le_inf hCZ hCP
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hcommon : ⁅Z d.radical a,Z d.radical z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  refine ⟨P,B,hQ,hP,hB,hpointZ,hi,hCX₁,hcommon.trans hCX₁,?_,?_,?_,?_,?_⟩
  · intro b
    rw [hmem]
    constructor
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      change x ∈ X₁ at hx
      rw [hX,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
      obtain ⟨u,hu,v,hv,rfl⟩ := hx
      have hbv : Commute b v := hCY hv b hb
      rw [hHZ,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hbv]
      simpa only [mul_one,mul_inv_cancel_right] using hm u hu
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      rw [←hHZ]
      apply hm x
      change x ∈ X₁
      rw [hX]
      exact mem_sup_left hx
  · rw [hXB]
    exact hdis
  · rw [hXB]
    exact hcard
  · rw [hHZ,hXB]
    exact hjoin
  · rw [commutator_comm]
    exact (commutator_mono hP le_rfl).trans_eq
      (source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
