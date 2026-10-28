module
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.GroupTheory.PCoreImage

/-!
# Point-radical displacement of the root-fixed hyperplane

On the universal orthogonal cover, a point-radical matrix acts on the
hyperplane perpendicular to its point with zero central correction. Its
full displacement there is the pure natural point. Passing through the
universal cover quotient preserves that line and its disjointness from
the entire fixed kernel, even when the kernel is only a binary subspace.

The embedded result uses the literal root centralizer and the full two-core
of its normalizer. Conjugation transports both through the same natural
marking. The distance-two application uses the original odd-index radical;
this is the additional overlap action in the fixed-kernel comparison of
MS93 (3.7)(4), printed p.875. No fixed kernel is factored out or discarded.
-/

public noncomputable section
open Matrix
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour hiding e
namespace Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

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

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}

/-- The full point radical moves the root-fixed hyperplane in a complement
of the complete fixed kernel, also for arbitrary binary central quotients. -/
theorem cover_point_overlap (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p) :
    ∃ s : F →ₗ[ZMod 2] W,
      (∀ t, p (s t)=t • ClassicalOrthogonal.e 0) ∧
      (∀ (g : L (K := F)), g.val ∈ ((pointRadical (F := F)).map pointLocal.subtype) → ∀ w : W,
        (p w) (.inr 0)=0 → σ g w-w ∈ s.range) ∧
      (∀ t : F, ∃ (g : L (K := F)) (w : W),
        g.val ∈ ((pointRadical (F := F)).map pointLocal.subtype) ∧ (p w) (.inr 0)=0 ∧ σ g w-w=s t) := by
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
    let g : L (K := F) := ⟨(pointRadicalElement 0 t 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    let x : Space (K := F) := (ClassicalOrthogonal.e 1,0)
    refine ⟨g,f x,mem_map_of_mem _ (pointRadicalElement_mem 0 t 0),?_,?_⟩
    · rw [hpf]; change (ClassicalOrthogonal.e 1 : Natural (K := F)) (.inr 0)=0; rfl
    · rw [←f.isIntertwining,←map_sub]
      apply congrArg f
      change action g x-x=(t • ClassicalOrthogonal.e 0,0)
      rw [action_apply]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [g,x,pointRadicalElement,pointRadicalMatrix,Matrix.fromBlocks,ClassicalOrthogonal.e]
      · change (0+correction (pointRadicalElement 0 t 0).val (ClassicalOrthogonal.e 1))-0=0
        rw [point_correction 0 t 0 (ClassicalOrthogonal.e 1) (by simp [ClassicalOrthogonal.e])]
        simp

variable {G : Type*} [Group G]
open scoped commutatorElement

/-- In the literal embedded group, the original point radical moves the
root centralizer in a field-sized subgroup disjoint from the full fixed kernel. -/
theorem embedded_point_overlap (hF : 2 < Nat.card F)
    (U T P : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (hT : T.map ((commutator (Sp F)).subtype.comp γ)=RootSubgroup.group 0)
    (hP : P.map ((commutator (Sp F)).subtype.comp γ)=pointRadicalAmbient) :
    Disjoint (⁅U ⊓ centralizer (T : Set G),P⁆)
        (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) ∧
      Nat.card (⁅U ⊓ centralizer (T : Set G),P⁆ : Subgroup G) = Nat.card F ∧
      ⁅U ⊓ centralizer (T : Set G),P⁆ ≤ ⁅U,T⁆ := by
  let ψ := (commutator (Sp F)).subtype.comp γ
  have hfix (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) ↔
      (p w) (.inr 0)=0 := by
    constructor
    · intro hw
      have hr : rootElement (K := F) 0 1 ∈ T.map ψ :=
        hT.symm ▸ (RootSubgroup.mem_group_iff 0 _).mpr ⟨1,rfl⟩
      obtain ⟨t,ht,he⟩ := hr
      have hf : σ (γ t) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact,hw t ht,mul_inv_cancel_right]
      have hv := congrArg p hf
      rw [p.isIntertwining] at hv
      change (γ t).val.val *ᵥ p w=p w at hv
      change (γ t).val=rootElement 0 1 at he
      rw [he,Roots.natural_root] at hv
      have he0 := congrFun hv (.inl 0)
      simpa [ClassicalOrthogonal.e] using he0
    · intro hw t ht
      have ht' : ψ t ∈ RootSubgroup.group 0 := hT ▸ mem_map_of_mem ψ ht
      obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 0 _).mp ht'
      have hf : σ (γ t) w=w := by
        apply cover_fixed_of_projection_fixed p hp
        change (γ t).val.val *ᵥ p w=p w
        change rootElement 0 a=(γ t).val at ha
        rw [←ha,Roots.natural_root,hw,mul_zero,zero_smul,add_zero]
      have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
      rw [hact,mul_inv_eq_iff_eq_mul] at he
      exact he
  obtain ⟨s,hs,hm,hsurj⟩ := cover_point_overlap hF p hp
  let f : Multiplicative F →* G := j.comp s.toAddMonoidHom.toMultiplicative
  have hfi : Function.Injective f := by
    intro x y he
    have hsxy : s x.toAdd=s y.toAdd := congrArg Multiplicative.toAdd (hj he)
    have hh := congrArg (fun v => (p v) (.inl 0)) hsxy
    simpa [hs,ClassicalOrthogonal.e] using hh
  have hD : ⁅U ⊓ centralizer (T : Set G),P⁆=f.range := by
    rw [commutator_comm]
    apply le_antisymm
    · apply commutator_le.mpr
      intro b hb u hu
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hu.1
      obtain ⟨t,ht⟩ := hm (γ b) (show ψ b ∈ pointRadicalAmbient from hP ▸ mem_map_of_mem ψ hb) w.toAdd ((hfix w.toAdd).mp hu.2)
      refine ⟨Multiplicative.ofAdd t,?_⟩
      change j (Multiplicative.ofAdd (s t))=⁅b,j w⁆
      rw [ht,ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
      rfl
    · rintro _ ⟨t,rfl⟩
      obtain ⟨b,w,hb,hw,he⟩ := hsurj t.toAdd
      obtain ⟨x,hx,hxb⟩ := (show b.val ∈ P.map ψ from hP.symm ▸ hb)
      have hxγ : γ x=b := Subtype.ext hxb
      have hcomm : ⁅x,j (Multiplicative.ofAdd w)⁆=f t := by
        have he' := congrArg (fun v => j (Multiplicative.ofAdd v)) he
        rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,←hxγ,hact] at he'
        exact he'
      rw [←hcomm]
      exact commutator_mem_commutator hx ⟨hjr ▸ ⟨_,rfl⟩,(hfix w).mpr hw⟩
  have hroot (w : W) (hw : p w ∈ firstLine) : j (Multiplicative.ofAdd w) ∈ ⁅U,T⁆ := by
    have hw' : w ∈ Coinvariants.ker (σ.comp Roots.group.subtype) :=
      (Roots.cover_root_geometry hF p hp).2.1 ▸ hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨a,v⟩,rfl⟩ := hw
      have ha : a.val.val ∈ T.map ψ := hT.symm ▸ a.property
      obtain ⟨x,hx,hxa⟩ := ha
      have hxγ : γ x=a.val := Subtype.ext hxa
      change j (Multiplicative.ofAdd (σ a.val v-v)) ∈ _
      rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,←hxγ,hact]
      rw [commutator_comm U T]
      exact commutator_mem_commutator hx (hjr ▸ ⟨_,rfl⟩)
    | zero => simpa only [ofAdd_zero,map_one] using (⁅U,T⁆ : Subgroup G).one_mem
    | add x y _ _ hx hy =>
      rw [ofAdd_add,map_mul]
      exact mul_mem hx hy
    | smul c v _ hv =>
      fin_cases c
      · change j (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ _
        simp only [zero_smul,ofAdd_zero,map_one,one_mem]
      · change j (Multiplicative.ofAdd ((1 : ZMod 2) • v)) ∈ _
        simpa only [one_smul] using hv
  refine ⟨?_,?_,?_⟩
  · rw [hD,disjoint_iff_inf_le]
    rintro x ⟨⟨t,ht⟩,⟨w,hw,hwx⟩⟩
    have he : s t.toAdd=w.toAdd := congrArg Multiplicative.toAdd (hj (ht.trans hwx.symm))
    have hz : t.toAdd=0 := by
      have hh := congrArg (fun v => (p v) (.inl 0)) he
      simpa [hs,show p w.toAdd=0 from hw,ClassicalOrthogonal.e] using hh
    change x=1
    rw [←ht,show t=1 from Multiplicative.toAdd.injective hz,map_one]
  · rw [hD]
    exact (Nat.card_range_of_injective hfi).trans
      (Nat.card_congr Multiplicative.toAdd)
  · rw [hD]
    rintro _ ⟨t,rfl⟩
    apply hroot
    change p (s t.toAdd) ∈ firstLine
    rw [hs]
    exact Submodule.mem_span_singleton.mpr ⟨t.toAdd,rfl⟩


open Theory.GroupTheory
/-- The construction is intrinsic to a marked root and the full two-core
of its normalizer; no splitting or removal of the covering kernel is used. -/
theorem embedded_root_normalizer_overlap [Finite G]
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (U T : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (honto : Function.Surjective γ) (hk : IsPGroup 2 γ.ker) (hkT : γ.ker ≤ T)
    (hc : Nat.card (T.map γ)=Nat.card F)
    (hd : Module.finrank F (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype))=1)
    (hq : ∀ x ∈ (T.map γ).map (commutator (Sp F)).subtype,
      ∀ y ∈ (T.map γ).map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    Disjoint (⁅U ⊓ centralizer (T : Set G),(normalizer (T : Set G)).pCoreIn 2⁆)
        (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) ∧
      Nat.card (⁅U ⊓ centralizer (T : Set G),(normalizer (T : Set G)).pCoreIn 2⁆ :
        Subgroup G) = Nat.card F ∧
      ⁅U ⊓ centralizer (T : Set G),(normalizer (T : Set G)).pCoreIn 2⁆ ≤ ⁅U,T⁆ := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1<2) hn
  have hcard : Nat.card ((T.map γ).map (commutator (Sp F)).subtype)=Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hcard hd hq
  let gl : L (K := F) := ⟨g,by rw [LargeField.commutator_eq_top hlarge]; trivial⟩
  let γ' := (MulAut.conj gl).toMonoidHom.comp γ
  let ψ := (commutator (Sp F)).subtype.comp γ'
  let j' := j.comp (σ gl⁻¹).toAddMonoidHom.toMultiplicative
  have hj'i : Function.Injective j' := by
    intro x y he
    exact Multiplicative.toAdd.injective ((σ.apply_bijective gl⁻¹).1
      (congrArg Multiplicative.toAdd (hj he)))
  have hj'r : j'.range=U := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact hjr ▸ ⟨_,rfl⟩
    · intro u hu
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
      obtain ⟨v,hv⟩ := (σ.apply_bijective gl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
  have hj'act (x : G) (w : W) : j' (Multiplicative.ofAdd (σ (γ' x) w))=
      x*j' (Multiplicative.ofAdd w)*x⁻¹ := by
    change j (Multiplicative.ofAdd (σ gl⁻¹ (σ (gl*γ x*gl⁻¹) w)))=_
    have he : σ gl⁻¹ (σ (gl*γ x*gl⁻¹) w)=σ (γ x) (σ gl⁻¹ w) := by
      simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    rw [he,hact]
    rfl
  have hψker : ψ.ker=γ.ker := by
    ext x
    change ((MulAut.conj gl) (γ x)).val=1 ↔ γ x=1
    exact (show ((MulAut.conj gl) (γ x)).val=1 ↔ (MulAut.conj gl) (γ x)=1 from
      ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩).trans
        (MulAut.conj gl).map_eq_one_iff
  have hψonto : Function.Surjective ψ := by
    intro x
    have hx : x ∈ commutator (Sp F) := by rw [LargeField.commutator_eq_top hlarge]; trivial
    obtain ⟨y,hy⟩ := honto ((MulAut.conj gl).symm ⟨x,hx⟩)
    exact ⟨y,congrArg Subtype.val (congrArg (MulAut.conj gl) hy |>.trans
      ((MulAut.conj gl).apply_symm_apply _))⟩
  have hψT : T.map ψ=RootSubgroup.group 0 := by
    change T.map (((commutator (Sp F)).subtype.comp (MulAut.conj gl).toMonoidHom).comp γ)=_
    rw [←Subgroup.map_map]
    have he : (commutator (Sp F)).subtype.comp (MulAut.conj gl).toMonoidHom=
        (MulAut.conj g).toMonoidHom.comp (commutator (Sp F)).subtype := by ext; rfl
    rw [he,←Subgroup.map_map]
    exact hg
  have hψP : ((normalizer (T : Set G)).pCoreIn 2).map ψ=pointRadicalAmbient := by
    have hN : (normalizer (T : Set G)).map ψ=normalizer (T.map ψ : Set (Sp F)) := by
      have he : (normalizer (T.map ψ : Set (Sp F))).comap ψ=normalizer (T : Set G) := by
        rw [comap_normalizer_eq_of_surjective _ hψonto,
          comap_map_eq_self (hψker.trans_le hkT)]
      rw [←he,map_comap_eq_self_of_surjective hψonto]
    rw [map_pCoreIn_of_ker_isPGroup ψ (hψker ▸ hk),hN,hψT,
      RootNormalizerResidual.normalizer_zero_eq]
    exact pointParabolic_core_map_eq_radical hF hn
  have hkernel : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j'=
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j := by
    have he (v : Multiplicative W) (hv : v ∈ p.toLinearMap.ker.toAddSubgroup.toSubgroup) :
        j' v=j v := by
      change j (Multiplicative.ofAdd (σ gl⁻¹ v.toAdd))=j v
      rw [hp.2.1 (show v.toAdd ∈ p.toLinearMap.ker from hv) gl⁻¹]
      rfl
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩; exact ⟨v,hv,(he v hv).symm⟩
    · rintro _ ⟨v,hv,rfl⟩; exact ⟨v,hv,he v hv⟩
  have hh := embedded_point_overlap hlarge U T ((normalizer (T : Set G)).pCoreIn 2)
    p hp j' hj'i hj'r γ' hj'act hψT hψP
  rwa [hkernel] at hh

end Representation.SymplecticFourOrthogonalCover
