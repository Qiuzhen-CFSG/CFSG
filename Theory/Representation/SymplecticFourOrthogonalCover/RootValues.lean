module
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
/-!
# Individual commutator values in symplectic central covers

On the universal odd-orthogonal cover a long-root displacement is
`(t y e₀, √t y)`. Every vector on the two-dimensional root preimage with
both coordinates nonzero is such a displacement. If the central quotient
has a nonzero kernel, a lift can be shifted in that kernel to make its
second coordinate nonzero. Thus, below the full orthogonal kernel, every
moved vector outside the fixed kernel is an individual commutator value.
The result is transported through the original root marking and injective
ambient embedding. The binary kernel is not assumed to be a field subspace.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the commutator-value comparison in (3.7)(4), printed p.875.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
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
  have hs : Roots.sqrt ((a/b)^2) = a/b := by
    exact (frobeniusEquiv F 2).symm_apply_apply (a/b)
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

omit [FiniteDimensional (ZMod 2) W] in
private theorem noninjective_root_value (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (f : binaryAction.IntertwiningMap σ) (hf : Function.Surjective f)
    (hpf : ∀ v, p (f v) = binaryProjection v) (hni : ¬ Function.Injective f)
    (w : W) (hw : p w ∈ firstLine) (hn : p w ≠ 0) :
    ∃ t : F, ∃ v : W, σ (Roots.element hF t) v-v=w := by
  have hker : f.toLinearMap.ker ≠ ⊥ := by
    intro he
    exact hni (LinearMap.ker_eq_bot.mp he)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hx1 : x.1=0 := by
    have he := hpf x
    rw [show f x=0 from hx,map_zero] at he
    exact he.symm
  have hx2 : x.2 ≠ 0 := by
    intro he
    exact hx0 (Prod.ext hx1 he)
  obtain ⟨v,rfl⟩ := hf w
  rw [hpf] at hw hn
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hw
  change a • e 0 = v.1 at ha
  change v.1 ≠ 0 at hn
  have ha0 : a ≠ 0 := by
    intro he
    apply hn
    rw [←ha,he,zero_smul]
  have hval : ∀ y : Space (K := F), y.1 = a • e 0 → y.2 ≠ 0 →
      ∃ t : F, ∃ u : W, σ (Roots.element hF t) u-u=f y := by
    intro y hy hy0
    obtain ⟨t,z,hz⟩ := root_value hF a y.2 ha0 hy0
    refine ⟨t,f z,?_⟩
    rw [←f.isIntertwining,←map_sub,hz]
    exact congrArg f (Prod.ext hy.symm rfl)
  by_cases hv : v.2=0
  · have h := hval (v+x) (by simpa only [Prod.fst_add,hx1,add_zero] using ha.symm)
      (by simpa only [Prod.snd_add,hv,zero_add] using hx2)
    simpa only [map_add,show f x=0 from hx,add_zero] using h
  · exact hval v ha.symm hv

omit [FiniteDimensional (ZMod 2) W] in
private theorem cover_kernel_card_of_injective_quotient
    (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (f : binaryAction.IntertwiningMap σ) (hf : Function.Bijective f)
    (hpf : ∀ v, p (f v) = binaryProjection v) :
    Nat.card p.toLinearMap.ker = Nat.card F := by
  let k : F → p.toLinearMap.ker := fun t => ⟨f (0,t),by
    change p (f (0,t))=0
    exact hpf (0,t)⟩
  have hi : Function.Injective k := by
    intro a b he
    exact congrArg Prod.snd (hf.1 (congrArg Subtype.val he))
  have hs : Function.Surjective k := by
    intro w
    obtain ⟨v,hv⟩ := hf.2 w.val
    have hv1 : v.1=0 := (hpf v).symm.trans (by rw [hv]; exact w.property)
    refine ⟨v.2,Subtype.ext ?_⟩
    change f (0,v.2)=w.val
    rw [show (0,v.2)=v from Prod.ext hv1.symm rfl,hv]
  exact (Nat.card_congr (Equiv.ofBijective k ⟨hi,hs⟩)).symm

/-- Below the full orthogonal kernel, every moved vector outside the fixed
kernel is one individual root displacement. -/
theorem cover_root_value_of_kernel_card_ne
    (hF : 2 < Nat.card F) (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (hp : IsCover p) (hsmall : Nat.card p.toLinearMap.ker ≠ Nat.card F)
    (A : Subgroup (L (K := F))) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (w : W) (hw : p w ∈ displacementSpace (A.map (commutator (Sp F)).subtype))
    (hn : p w ≠ 0) : ∃ a ∈ A, ∃ v : W, σ a v-v=w := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  have hni : ¬ Function.Injective f := fun hi =>
    hsmall (cover_kernel_card_of_injective_quotient p f ⟨hi,hf⟩ hpf)
  have hAc : Nat.card (A.map (commutator (Sp F)).subtype) = Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hAc hd hq
  let gl : L (K := F) := ⟨g,by rw [OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF]; trivial⟩
  have hmove : p (σ gl w) ∈ firstLine := by
    rw [p.isIntertwining]
    change g • p w ∈ point F
    rw [←PointRadicalAction.root_displacement,←hg,PointRadicalAction.displacement_conjugate]
    exact ⟨p w,hw,rfl⟩
  have hnon : p (σ gl w) ≠ 0 := by
    rw [p.isIntertwining]
    exact fun he => hn (((binaryNatural (K := F)).apply_bijective gl).1 (he.trans (map_zero _).symm))
  obtain ⟨t,v,hv⟩ := noninjective_root_value hF p f hf hpf hni (σ gl w) hmove hnon
  have hmem : rootElement 0 t ∈ (A.map (commutator (Sp F)).subtype).map
      (MulAut.conj g).toMonoidHom := hg.symm ▸ (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
  obtain ⟨_,⟨a,ha,rfl⟩,he⟩ := hmem
  have hel : gl*a*gl⁻¹=Roots.element hF t := Subtype.ext he
  refine ⟨a,ha,σ gl⁻¹ v,?_⟩
  apply ((σ.apply_bijective gl).1)
  rw [map_sub,self_inv_apply]
  have heact : σ gl (σ a (σ gl⁻¹ v))=σ (Roots.element hF t) v := by
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hel]
  rw [heact,hv]

variable {G : Type*} [Group G]
open scoped commutatorElement

omit [FiniteDimensional (ZMod 2) W] [Finite F] [CharP F 2] in
/-- The kernel order is unchanged by the literal injective embedding. -/
theorem embedded_cover_kernel_card
    (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (j : Multiplicative W →* G) (hj : Function.Injective j) :
    Nat.card (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) = Nat.card p.toLinearMap.ker := by
  rw [card_map_of_injective hj]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.val.toAdd,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- An individual displacement in the entire embedded fixed kernel is trivial. -/
theorem embedded_cover_value_in_kernel_eq_one
    (U B : Subgroup G) (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : B →* L (K := F))
    (hact : ∀ b : B, ∀ v : W, j (Multiplicative.ofAdd (σ (β b) v)) =
      b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (b : G) (hb : b ∈ B) (u : G) (hu : u ∈ U)
    (hc : ⁅b,u⁆ ∈ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) : ⁅b,u⁆=1 := by
  obtain ⟨v,rfl⟩ := (hjr.symm ▸ hu : u ∈ j.range)
  have he : j (Multiplicative.ofAdd (σ (β ⟨b,hb⟩) v.toAdd-v.toAdd)) = ⁅b,j v⁆ := by
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  obtain ⟨k,hk,hke⟩ := hc
  have hk' : σ (β ⟨b,hb⟩) v.toAdd-v.toAdd=k.toAdd :=
    congrArg Multiplicative.toAdd (hj (he.trans hke.symm))
  have hz : σ (β ⟨b,hb⟩) v.toAdd-v.toAdd ∈ fixed σ := by
    rw [cover_fixed_kernel p hp,hk']
    exact hk
  rw [←he,cover_displacement_fixed p hp _ _ hz,sub_self]
  exact map_one _

/-- An embedded root commutator outside a proper fixed kernel is an actual
commutator of two elements, rather than only a product of such commutators. -/
theorem embedded_root_value_of_kernel_card_ne
    (hF : 2 < Nat.card F) (U B : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hjr : j.range=U)
    (β : B →* L (K := F))
    (hact : ∀ b : B, ∀ v : W, j (Multiplicative.ofAdd (σ (β b) v)) =
      b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (hc : Nat.card β.range = Nat.card F)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ β.range.map (commutator (Sp F)).subtype,
      ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hsmall : Nat.card p.toLinearMap.ker ≠ Nat.card F)
    (x : G) (hx : x ∈ ⁅B,U⁆)
    (hn : x ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) :
    ∃ b ∈ B, ∃ u ∈ U, ⁅b,u⁆=x := by
  let D := displacementSpace (β.range.map (commutator (Sp F)).subtype)
  let M := ((D.restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hM : ⁅B,U⁆ ≤ M := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨v,rfl⟩ := (hjr.symm ▸ hu : u ∈ j.range)
    refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hb⟩) v.toAdd-v.toAdd),?_,?_⟩
    · change p (σ (β ⟨b,hb⟩) v.toAdd-v.toAdd) ∈ D
      rw [map_sub,p.isIntertwining]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp (β.range.map (commutator (Sp F)).subtype).subtype)
        ⟨(β ⟨b,hb⟩).val,⟨β ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩,rfl⟩⟩ (p v.toAdd)
    · rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
      rfl
  obtain ⟨w,hw,he⟩ := hM hx
  have hpn : p w.toAdd ≠ 0 := by
    intro hz
    exact hn ⟨w,hz,he⟩
  obtain ⟨a,ha,v,hv⟩ := cover_root_value_of_kernel_card_ne hF p hp hsmall
    β.range hc hd hq w.toAdd hw hpn
  obtain ⟨b,rfl⟩ := ha
  refine ⟨b.val,b.property,j (Multiplicative.ofAdd v),hjr ▸ ⟨_,rfl⟩,?_⟩
  have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) hv
  rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact] at hh
  exact hh.trans he

end Representation.SymplecticFourOrthogonalCover
