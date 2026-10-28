module
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap

/-!
# Individual root values and the original normalizer overlap

A vector in the long-root displacement outside the full fixed kernel has
coordinates (a e₀,b) with a nonzero. If b is nonzero, it is one root
commutator; if b is zero, it is a displacement of the point radical on the
root-fixed hyperplane. The universal cover quotient preserves this alternative
without discarding any binary fixed layer. Conjugation and the literal
normalizer two-core give the corresponding embedded-group statement.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the kernel comparison in (3.7)(4), printed p.875. The distance-two
consumer uses this to identify an unequal opposite fixed kernel with the
original-normalizer overlap, rather than assuming that the kernels agree.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour hiding e
namespace Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
private theorem root_value (hF : 2 < Nat.card F) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : F, ∃ v : Space (K := F),
      binaryAction (Roots.element hF t) v-v = (a • e 0,b) := by
  refine ⟨(a/b)^2, ((b^2/a) • ClassicalOrthogonal.f 0,0),?_⟩
  change action (Roots.element hF ((a/b)^2)) _ - _ = _
  rw [Roots.displacement]
  have hs : Roots.sqrt ((a/b)^2) = a/b :=
    (frobeniusEquiv F 2).symm_apply_apply (a/b)
  apply Prod.ext
  · change (_ : F) • ((a/b)^2 • e 0) = _
    simp only [ClassicalOrthogonal.f,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,
      smul_smul]
    congr 1
    field_simp
  · change (_ : F) * Roots.sqrt ((a/b)^2) = b
    rw [hs]
    simp only [ClassicalOrthogonal.f,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one]
    field_simp

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}

private theorem cover_point_value_or_overlap
    (hF : 2 < Nat.card F) (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (hp : IsCover p) (w : W) (hw : p w ∈ firstLine) (hn : p w ≠ 0) :
    (∃ t : F, ∃ v : W, σ (Roots.element hF t) v-v=w) ∨
      ∃ (g : L (K := F)) (v : W), g.val ∈ pointRadicalAmbient ∧
        (p v) (.inr 0)=0 ∧ σ g v-v=w := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  obtain ⟨v,rfl⟩ := hf w
  rw [hpf] at hw hn
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hw
  change a • e 0=v.1 at ha
  change v.1 ≠ 0 at hn
  have ha0 : a ≠ 0 := by
    intro he
    apply hn
    rw [←ha,he,zero_smul]
  by_cases hv : v.2=0
  · right
    let b : L (K := F) := ⟨(pointRadicalElement 0 a 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    let u : Space (K := F) := (e 1,0)
    refine ⟨b,f u,mem_map_of_mem _ (pointRadicalElement_mem 0 a 0),?_,?_⟩
    · rw [hpf]
      change (e 1 : Natural (K := F)) (.inr 0)=0
      rfl
    · rw [←f.isIntertwining,←map_sub]
      apply congrArg f
      change action b u-u=v
      rw [show v=(a • e 0,0) from Prod.ext ha.symm hv,action_apply]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [b,u,pointRadicalElement,pointRadicalMatrix,Matrix.fromBlocks,ClassicalOrthogonal.e]
      · simp [b,u,correction,quadraticCocycle,transposeSp,pointRadicalElement,
          pointRadicalMatrix,rowQuadratic,Matrix.transpose_apply,Fintype.sum_sum_type,
          Fin.sum_univ_two,Matrix.fromBlocks,ClassicalOrthogonal.e]
  · left
    obtain ⟨t,u,hu⟩ := root_value hF a v.2 ha0 hv
    refine ⟨t,f u,?_⟩
    rw [←f.isIntertwining,←map_sub,hu]
    exact congrArg f (Prod.ext ha rfl)

variable {G : Type*} [Group G]
open scoped commutatorElement

private theorem embedded_point_value_or_overlap
    (hF : 2 < Nat.card F) (U T P : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (hT : T.map ((commutator (Sp F)).subtype.comp γ)=RootSubgroup.group 0)
    (hP : P.map ((commutator (Sp F)).subtype.comp γ)=pointRadicalAmbient)
    (x : G) (hx : x ∈ ⁅U,T⁆)
    (hn : x ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) :
    x ∈ ⁅U ⊓ centralizer (T : Set G),P⁆ ∨
      ∃ b ∈ T, ∃ u ∈ U, ⁅b,u⁆=x := by
  let ψ := (commutator (Sp F)).subtype.comp γ
  let M := (((firstLine (K := F)).restrictScalars (ZMod 2)).comap
    p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hM : ⁅T,U⁆ ≤ M := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨v,rfl⟩ := (hjr.symm ▸ hu : u ∈ j.range)
    refine ⟨Multiplicative.ofAdd (σ (γ b) v.toAdd-v.toAdd),?_,?_⟩
    · change p (σ (γ b) v.toAdd-v.toAdd) ∈ firstLine
      rw [map_sub,p.isIntertwining]
      obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp
        (show ψ b ∈ RootSubgroup.group 0 from hT ▸ mem_map_of_mem ψ hb)
      change rootElement 0 t=(γ b).val at ht
      change (γ b).val.val *ᵥ p v.toAdd-p v.toAdd ∈ firstLine
      rw [←ht,Roots.natural_root,add_sub_cancel_left]
      exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
    · rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
      rfl
  rw [commutator_comm] at hx
  obtain ⟨w,hw,he⟩ := hM hx
  have hpn : p w.toAdd ≠ 0 := fun hz => hn ⟨w,hz,he⟩
  rcases cover_point_value_or_overlap hF p hp w.toAdd hw hpn with hv | hv
  · obtain ⟨t,v,hv⟩ := hv
    have ht : rootElement 0 t ∈ T.map ψ :=
      hT.symm ▸ (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
    obtain ⟨b,hb,hbγ⟩ := ht
    have hγ : γ b=Roots.element hF t := Subtype.ext hbγ
    refine Or.inr ⟨b,hb,j (Multiplicative.ofAdd v),hjr ▸ ⟨_,rfl⟩,?_⟩
    have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) hv
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,←hγ,hact] at hh
    exact hh.trans he
  · obtain ⟨b,v,hb,hv,hh⟩ := hv
    obtain ⟨c,hc,hcγ⟩ := (show b.val ∈ P.map ψ from hP.symm ▸ hb)
    have hγ : γ c=b := Subtype.ext hcγ
    have hfix : j (Multiplicative.ofAdd v) ∈ centralizer (T : Set G) := by
      intro t ht
      obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 0 _).mp
        (show ψ t ∈ RootSubgroup.group 0 from hT ▸ mem_map_of_mem ψ ht)
      have hf : σ (γ t) v=v := by
        apply cover_fixed_of_projection_fixed p hp
        change (γ t).val.val *ᵥ p v=p v
        change rootElement 0 a=(γ t).val at ha
        rw [←ha,Roots.natural_root,hv,mul_zero,zero_smul,add_zero]
      have ht' := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
      rw [hact,mul_inv_eq_iff_eq_mul] at ht'
      exact ht'
    have hcomm : ⁅c,j (Multiplicative.ofAdd v)⁆=x := by
      have hv' := congrArg (fun v => j (Multiplicative.ofAdd v)) hh
      rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,←hγ,hact] at hv'
      exact hv'.trans he
    left
    rw [←hcomm,commutator_comm]
    exact commutator_mem_commutator hc ⟨hjr ▸ ⟨_,rfl⟩,hfix⟩

open Theory.GroupTheory
/-- Outside the full fixed kernel, each root displacement is either in
the original normalizer overlap or is an individual commutator. -/
theorem embedded_root_normalizer_value_or_overlap [Finite G]
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (U T : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (honto : Function.Surjective γ) (hk : IsPGroup 2 γ.ker) (hkT : γ.ker ≤ T)
    (hc : Nat.card (T.map γ)=Nat.card F)
    (hd : Module.finrank F (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype))=1)
    (hq : ∀ x ∈ (T.map γ).map (commutator (Sp F)).subtype,
      ∀ y ∈ (T.map γ).map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (x : G) (hx : x ∈ ⁅U,T⁆)
    (hnk : x ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) :
    x ∈ ⁅U ⊓ centralizer (T : Set G),(normalizer (T : Set G)).pCoreIn 2⁆ ∨
      ∃ b ∈ T, ∃ u ∈ U, ⁅b,u⁆=x := by
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
  exact embedded_point_value_or_overlap hlarge U T ((normalizer (T : Set G)).pCoreIn 2)
    p hp j' hj'r γ' hj'act hψT hψP x hx (by rwa [hkernel])

end Representation.SymplecticFourOrthogonalCover
