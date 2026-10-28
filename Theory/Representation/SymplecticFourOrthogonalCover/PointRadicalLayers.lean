module
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap


/-!
# The full displacement of a point radical on an orthogonal cover

The original point radical moves the natural quotient onto the hyperplane
fixed by its central long root. The central covering kernel is also moved:
the long-root displacement already contains its entire preimage of the point.
Two explicit middle-coordinate displacements supply the rest of the hyperplane.
Thus [U,P] = C_U(T), before factoring out any fixed attachment. The intrinsic
version uses the two-core of the root normalizer and the same quotient marking.

Source: Meierfrankenfeld--Stellmacher (1993), the original-radical operations
in (3.7), printed pp.872--877, and the orthogonal cover of Aschbacher--Smith
I.2.3. The distance-two consumer identifies the second original-radical
displacement with the selected overlap on the whole replacement center.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour hiding e
namespace Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal Representation.OneCohomology.SymplecticFour
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}
variable {G : Type*} [Group G]

private theorem point_middle_displacement (hF : 2 < Nat.card F) (c : F) :
    let g₁ : L (K := F) := ⟨(pointRadicalElement 1 0 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    let g₂ : L (K := F) := ⟨(pointRadicalElement 0 1 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    binaryAction g₁ (c • ClassicalOrthogonal.f 0,0)-(c • ClassicalOrthogonal.f 0,0)=
      (c • ClassicalOrthogonal.e 1,0) ∧
    binaryAction g₂ (c • ClassicalOrthogonal.f 0,0)-(c • ClassicalOrthogonal.f 0,0)=
      (c • ClassicalOrthogonal.f 1,0) := by
  dsimp only
  constructor <;> (change action _ _-_=_; rw [action_apply]; apply Prod.ext)
  · ext i
    fin_cases i <;> simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,ClassicalOrthogonal.e,ClassicalOrthogonal.f]
  · simp [correction,quadraticCocycle,transposeSp,pointRadicalElement,pointRadicalMatrix,
      rowQuadratic,Matrix.transpose_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,ClassicalOrthogonal.f]
  · ext i
    fin_cases i <;> simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,ClassicalOrthogonal.f]
  · simp [correction,quadraticCocycle,transposeSp,pointRadicalElement,pointRadicalMatrix,
      rowQuadratic,Matrix.transpose_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,ClassicalOrthogonal.f]

/-- The complete point-radical displacement fills the whole root-fixed cover,
including every vector of its central kernel. -/
theorem embedded_point_displacement_eq_root_centralizer
    (hF : 2 < Nat.card F) (U T P : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (hT : T.map ((commutator (Sp F)).subtype.comp γ)=RootSubgroup.group 0)
    (hP : P.map ((commutator (Sp F)).subtype.comp γ)=pointRadicalAmbient) :
    ⁅U,P⁆=U ⊓ centralizer (T : Set G) := by
  let ψ := (commutator (Sp F)).subtype.comp γ
  have hfix (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) ↔
      (p w) (.inr 0)=0 := by
    constructor
    · intro hw
      obtain ⟨t,ht,he⟩ := (show rootElement (K := F) 0 1 ∈ T.map ψ from
        hT.symm ▸ (RootSubgroup.mem_group_iff 0 _).mpr ⟨1,rfl⟩)
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
      obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 0 _).mp
        (show ψ t ∈ RootSubgroup.group 0 from hT ▸ mem_map_of_mem ψ ht)
      have hf : σ (γ t) w=w := by
        apply cover_fixed_of_projection_fixed p hp
        change (γ t).val.val *ᵥ p w=p w
        change rootElement 0 a=(γ t).val at ha
        rw [←ha,Roots.natural_root,hw,mul_zero,zero_smul,add_zero]
      have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
      rw [hact,mul_inv_eq_iff_eq_mul] at he
      exact he
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let k := j.comp f.toAddMonoidHom.toMultiplicative
  have hdisp (b : L (K := F)) (hb : b.val ∈ pointRadicalAmbient) (v : Space (K := F)) :
      k (Multiplicative.ofAdd (binaryAction b v-v)) ∈ ⁅U,P⁆ := by
    obtain ⟨x,hx,hxb⟩ := (show b.val ∈ P.map ψ from hP.symm ▸ hb)
    have hxγ : γ x=b := Subtype.ext hxb
    change j (Multiplicative.ofAdd (f (binaryAction b v-v))) ∈ _
    rw [map_sub,f.isIntertwining,←hxγ,ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    change ⁅x,j (Multiplicative.ofAdd (f v))⁆ ∈ _
    rw [commutator_comm]
    exact commutator_mem_commutator hx (hjr ▸ ⟨_,rfl⟩)
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
    have hd : ⁅b,j w⁆=j (Multiplicative.ofAdd (σ (γ b) w.toAdd-w.toAdd)) := by
      rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
      rfl
    rw [hd]
    refine ⟨hjr ▸ ⟨_,rfl⟩,(hfix _).mpr ?_⟩
    rw [map_sub,p.isIntertwining]
    obtain ⟨b₀,hb₀,he⟩ := (show ψ b ∈ pointRadicalAmbient from hP ▸ mem_map_of_mem ψ hb)
    have hcoords := pointRadical_eq_element b₀ hb₀
    have hγb : (γ b).val=(pointRadicalElement
      (b₀.val.val (.inl 1) (.inr 0)) (b₀.val.val (.inr 1) (.inr 0))
      (b₀.val.val (.inl 0) (.inr 0))).val :=
      he.symm.trans (congrArg Subtype.val hcoords)
    change ((γ b).val.val *ᵥ p w.toAdd-p w.toAdd) (.inr 0)=0
    rw [hγb]
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]
  · rintro u ⟨hu,huc⟩
    obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
    obtain ⟨v,hv⟩ := hf w.toAdd
    have hv0 : v.1 (.inr 0)=0 := by
      have hh := (hfix w.toAdd).mp huc
      rw [←hv,hpf] at hh
      exact hh
    have hroot (v : Space (K := F)) (hv : v ∈ Roots.firstPreimage) :
        k (Multiplicative.ofAdd v) ∈ ⁅U,P⁆ := by
      obtain ⟨t,u,w,he⟩ := Roots.firstPreimage_displacements hF v hv
      rw [he,ofAdd_add,map_mul]
      apply mul_mem
      · apply hdisp
        change rootElement 0 1 ∈ pointRadicalAmbient
        have he : rootElement (K := F) 0 1=(pointRadicalElement 0 0 1).val := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [rootElement,rootMatrix,pointRadicalElement,pointRadicalMatrix,
              Matrix.fromBlocks,Matrix.single]
        rw [he]; exact mem_map_of_mem _ (pointRadicalElement_mem 0 0 1)
      · apply hdisp
        change rootElement 0 t ∈ pointRadicalAmbient
        have he : rootElement (K := F) 0 t=(pointRadicalElement 0 0 t).val := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [rootElement,rootMatrix,pointRadicalElement,pointRadicalMatrix,
              Matrix.fromBlocks,Matrix.single]
        rw [he]; exact mem_map_of_mem _ (pointRadicalElement_mem 0 0 t)
    let g₁ : L (K := F) := ⟨(pointRadicalElement 1 0 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    let g₂ : L (K := F) := ⟨(pointRadicalElement 0 1 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    have he : v=(v.1 (.inl 0) • ClassicalOrthogonal.e 0,v.2)+
        (v.1 (.inl 1) • ClassicalOrthogonal.e 1,0)+(v.1 (.inr 1) • ClassicalOrthogonal.f 1,0) := by
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [ClassicalOrthogonal.e,ClassicalOrthogonal.f,hv0]
      · simp
    have hresult : k (Multiplicative.ofAdd v) ∈ ⁅U,P⁆ := by
      rw [he,ofAdd_add,ofAdd_add,map_mul,map_mul]
      apply mul_mem
      · apply mul_mem
        · exact hroot _ ((Roots.mem_firstPreimage _).mpr ⟨_,rfl⟩)
        · rw [←(point_middle_displacement hF (v.1 (.inl 1))).1]
          exact hdisp g₁ (mem_map_of_mem _ (pointRadicalElement_mem 1 0 0)) _
      · rw [←(point_middle_displacement hF (v.1 (.inr 1))).2]
        exact hdisp g₂ (mem_map_of_mem _ (pointRadicalElement_mem 0 1 0)) _
    change j (Multiplicative.ofAdd (f v)) ∈ _ at hresult
    rwa [hv] at hresult

open Theory.GroupTheory
/-- The construction is intrinsic to a marked root and the full two-core
of its normalizer; no splitting or removal of the covering kernel is used. -/
theorem embedded_root_normalizer_displacement_eq [Finite G]
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
    ⁅U,(normalizer (T : Set G)).pCoreIn 2⁆ = U ⊓ centralizer (T : Set G) := by
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
  exact embedded_point_displacement_eq_root_centralizer hlarge U T
    ((normalizer (T : Set G)).pCoreIn 2) p hp j' hj'i hj'r γ' hj'act hψT hψP

end Representation.SymplecticFourOrthogonalCover
