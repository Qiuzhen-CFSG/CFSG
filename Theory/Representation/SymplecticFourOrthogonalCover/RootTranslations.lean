module
public import Theory.Representation.SymplecticFourOrthogonalCover.RootValues
/-!
# Fixed-kernel translates of individual root commutators

In the universal orthogonal cover a root value has coordinates
`(t y e₀, √t y)`. If a vector outside the fixed kernel is not such a
value, adding any nonzero fixed-kernel vector makes it one. The proof
lifts through the universal cover, transports the marked root by conjugation,
and then uses the original ambient embedding. It allows the full orthogonal
kernel and arbitrary binary central quotients.

The distance-two critical-pair consumer applies this to both endpoints:
a nontrivial intersection of their complete fixed kernels forces equality.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the root-value comparison in (3.7)(4), printed p.875.
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

private theorem first_root_value_or_add_kernel
    (hF : 2 < Nat.card F) (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (hp : IsCover p) (w k : W) (hw : p w ∈ firstLine) (hn : p w ≠ 0)
    (hk : p k=0) (hk0 : k ≠ 0) :
    ∃ t : F, ∃ v : W, σ (Roots.element hF t) v-v=w ∨
      σ (Roots.element hF t) v-v=w+k := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  obtain ⟨v,rfl⟩ := hf w
  obtain ⟨z,hz⟩ := hf k
  have hz1 : z.1=0 := (hpf z).symm.trans (by rw [hz,hk])
  have hz2 : z.2 ≠ 0 := by
    intro he
    apply hk0
    rw [←hz,show z=0 from Prod.ext hz1 he,map_zero]
  rw [hpf] at hw hn
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hw
  change a • e 0 = v.1 at ha
  change v.1 ≠ 0 at hn
  have ha0 : a ≠ 0 := by
    intro he
    apply hn
    rw [←ha,he,zero_smul]
  have hval : ∀ y : Space (K := F), y.1=a • e 0 → y.2 ≠ 0 →
      ∃ t : F, ∃ u : W, σ (Roots.element hF t) u-u=f y := by
    intro y hy hy0
    obtain ⟨t,x,hx⟩ := root_value hF a y.2 ha0 hy0
    refine ⟨t,f x,?_⟩
    rw [←f.isIntertwining,←map_sub,hx]
    exact congrArg f (Prod.ext hy.symm rfl)
  by_cases hv : v.2=0
  · obtain ⟨t,u,hu⟩ := hval (v+z)
      (by simpa only [Prod.fst_add,hz1,add_zero] using ha.symm)
      (by simpa only [Prod.snd_add,hv,zero_add] using hz2)
    exact ⟨t,u,Or.inr (by simpa only [map_add,hz] using hu)⟩
  · obtain ⟨t,u,hu⟩ := hval v ha.symm hv
    exact ⟨t,u,Or.inl hu⟩

/-- Translating by a nonzero element of the full fixed kernel makes at least
one of the two vectors an individual root displacement. -/
theorem cover_root_value_or_add_kernel
    (hF : 2 < Nat.card F) (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (hp : IsCover p) (A : Subgroup (L (K := F))) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (w k : W) (hw : p w ∈ displacementSpace (A.map (commutator (Sp F)).subtype))
    (hn : p w ≠ 0) (hk : p k=0) (hk0 : k ≠ 0) :
    ∃ a ∈ A, ∃ v : W, σ a v-v=w ∨ σ a v-v=w+k := by
  have hAc : Nat.card (A.map (commutator (Sp F)).subtype) = Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hAc hd hq
  let gl : L (K := F) := ⟨g,by rw [LargeField.commutator_eq_top hF]; trivial⟩
  have hmove : p (σ gl w) ∈ firstLine := by
    rw [p.isIntertwining]
    change g • p w ∈ point F
    rw [←PointRadicalAction.root_displacement,←hg,PointRadicalAction.displacement_conjugate]
    exact ⟨p w,hw,rfl⟩
  have hnon : p (σ gl w) ≠ 0 := by
    rw [p.isIntertwining]
    exact fun he => hn (((binaryNatural (K := F)).apply_bijective gl).1
      (he.trans (map_zero _).symm))
  have hk' : p (σ gl k)=0 := by rw [p.isIntertwining,hk,map_zero]
  have hk0' : σ gl k ≠ 0 := fun he => hk0 ((σ.apply_bijective gl).1
    (he.trans (map_zero _).symm))
  obtain ⟨t,v,hv⟩ := first_root_value_or_add_kernel hF p hp (σ gl w) (σ gl k)
    hmove hnon hk' hk0'
  have hmem : rootElement 0 t ∈ (A.map (commutator (Sp F)).subtype).map
      (MulAut.conj g).toMonoidHom := hg.symm ▸ (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
  obtain ⟨_,⟨a,ha,rfl⟩,he⟩ := hmem
  have hel : gl*a*gl⁻¹=Roots.element hF t := Subtype.ext he
  have heact : σ gl (σ a (σ gl⁻¹ v)-σ gl⁻¹ v)=σ (Roots.element hF t) v-v := by
    rw [map_sub,self_inv_apply]
    congr 1
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,hel]
  refine ⟨a,ha,σ gl⁻¹ v,?_⟩
  rcases hv with hv | hv
  · exact Or.inl ((σ.apply_bijective gl).1 (heact.trans hv))
  · exact Or.inr ((σ.apply_bijective gl).1 (heact.trans (hv.trans (map_add _ _ _).symm)))

variable {G : Type*} [Group G]
open scoped commutatorElement

/-- A nonidentity translation in the complete embedded fixed kernel makes
one of two displacement elements a single commutator. -/
theorem embedded_root_value_or_mul_kernel
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
    (x k : G) (hx : x ∈ ⁅B,U⁆)
    (hn : x ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j)
    (hk : k ∈ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) (hk0 : k ≠ 1) :
    ∃ b ∈ B, ∃ u ∈ U, ⁅b,u⁆=x ∨ ⁅b,u⁆=x*k := by
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
  obtain ⟨v,hv,hvk⟩ := hk
  have hpn : p w.toAdd ≠ 0 := fun hz => hn ⟨w,hz,he⟩
  have hv0 : v.toAdd ≠ 0 := by
    intro hz
    apply hk0
    rw [←hvk,show v=1 from Multiplicative.toAdd.injective hz,map_one]
  obtain ⟨a,ha,u,hu⟩ := cover_root_value_or_add_kernel hF p hp
    β.range hc hd hq w.toAdd v.toAdd hw hpn hv hv0
  obtain ⟨b,rfl⟩ := ha
  refine ⟨b.val,b.property,j (Multiplicative.ofAdd u),hjr ▸ ⟨_,rfl⟩,?_⟩
  have ht (y : W) (hy : σ (β b) u-u=y) :
      ⁅b.val,j (Multiplicative.ofAdd u)⁆=j (Multiplicative.ofAdd y) := by
    have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) hy
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact] at hh
    exact hh
  rcases hu with hu | hu
  · exact Or.inl ((ht _ hu).trans he)
  · exact Or.inr ((ht _ hu).trans (by simp only [ofAdd_add,map_mul,ofAdd_toAdd,he,hvk]))
end Representation.SymplecticFourOrthogonalCover
