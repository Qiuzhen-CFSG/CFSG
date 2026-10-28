module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSRootCoordinates
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# The central kernel of a G₂ natural cover at an offender

In trace-zero octonion coordinates an A--B--C displacement has four entries:
the three natural entries and the scalar entry c*z. If its natural entries
vanish, the scalar entry vanishes too. Conversely every vector with nonzero
natural projection in this four-space is a single displacement. Differences
of such displacements also generate the entire scalar radical.

The universal orthogonal cover transports these facts to every perfect central
binary cover over the original natural projection. Conjugating the actor
preserves its moved space and the set of single displacements. Thus every
natural offender moves the whole central kernel, whose nonzero elements are
exactly the moved vectors that are not single displacements. No splitting or
field structure on the target cover's central kernel is assumed.

MSMovingKernel applies this to the original central-omega moved section.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.5)(iv), p.843, and (3.2), pp.865--866. Coordinates use the existing
attributed octonion model; see LICENSES/ATLAS.txt. The critical-vertex kernel
and field comparisons remain with qt-d-1222-natural-line-action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative Pointwise
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
variable {F : Type*} [Field F] [CharP F 2]

def coverDisplacement (p v : Fin 3 → F) : Fin 4 → F :=
  ![rootDisplacement p v 0,rootDisplacement p v 1,rootDisplacement p v 2,p 2 * v 2]

private theorem rootDisplacement_zero_central (p v : Fin 3 → F)
    (h : rootDisplacement p v = 0) : p 2 * v 2 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [rootDisplacement, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Pi.zero_apply] at h0 h1 h2
  by_cases hz : v 2 = 0
  · rw [hz,mul_zero]
  have h1' : p 0 * v 2 = p 2 * v 0 := by
    exact (eq_neg_of_add_eq_zero_left h1).trans (CharTwo.neg_eq _)
  have h2' : p 1 * v 2 = p 2 * v 1 := by
    exact (eq_neg_of_add_eq_zero_left h2).trans (CharTwo.neg_eq _)
  have hh : (p 2)^2 * (v 2)^2 = 0 := by
    calc
      (p 2)^2 * (v 2)^2 =
          (p 0 * v 1 + p 1 * v 0 + (p 2)^2 * v 2) * v 2 := by
        have hcancel : p 0 * v 1 * v 2 + p 1 * v 0 * v 2 = 0 := by
          calc
            _ = (p 0*v 2)*v 1 + (p 1*v 2)*v 0 := by ring
            _ = 0 := by rw [h1',h2']; rw [mul_right_comm (p 2) (v 0) (v 1)]; exact CharTwo.add_self_eq_zero _
        linear_combination -hcancel
      _ = 0 := by rw [h0,zero_mul]
  have : (p 2*v 2)^2 = 0 := by simpa only [mul_pow] using hh
  exact eq_zero_of_pow_eq_zero this

/-- The short-root central coordinate cannot survive with zero natural displacement. -/
theorem coverDisplacement_natural_zero (p v : Fin 3 → F)
    (h : rootDisplacement p v = 0) : coverDisplacement p v = 0 := by
  ext i
  fin_cases i <;> simp [coverDisplacement,h,rootDisplacement_zero_central p v h]

/-- Every lift of a nonzero natural displacement is a single marked commutator. -/
theorem coverDisplacement_surjective_off_scalar (w : Fin 4 → F)
    (hw : ![w 0,w 1,w 2] ≠ (0 : Fin 3 → F)) :
    ∃ p v, coverDisplacement p v = w := by
  have hex : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    ext i
    fin_cases i <;> simp [h]
  by_cases hk : w 3 = 0
  · by_cases hs : w 1 = 0
    · by_cases ht : w 2 = 0
      · refine ⟨![1,0,0],![0,w 0,0],?_⟩
        ext i
        fin_cases i <;> simp [coverDisplacement,rootDisplacement,hs,ht,hk]
      · refine ⟨![0,w 2,0],![w 0/w 2,0,1],?_⟩
        ext i
        fin_cases i <;> simp [coverDisplacement,rootDisplacement,hs,hk]
        field_simp
    · refine ⟨![w 1,w 2,0],![0,w 0/w 1,1],?_⟩
      ext i
      fin_cases i <;> simp [coverDisplacement,rootDisplacement,hk]
      field_simp
  · by_cases hs : w 1 = 0
    · by_cases ht : w 2 = 0
      · have hr : w 0 ≠ 0 := by tauto
        refine ⟨![0,0,w 0/w 3],![0,0,(w 3)^2/w 0],?_⟩
        ext i
        fin_cases i <;> simp [coverDisplacement,rootDisplacement,hs,ht] <;> field_simp
      · refine ⟨![(w 3*(w 0+w 3)/w 2)/w 3,w 2/w 3,1],
          ![w 3*(w 0+w 3)/w 2,0,w 3],?_⟩
        ext i
        fin_cases i <;> simp [coverDisplacement,rootDisplacement,hs] <;>
          field_simp <;> ring_nf <;> simp only [CharTwo.two_eq_zero,mul_zero,add_zero]
    · refine ⟨![w 1/w 3,(w 2+w 3*(w 0+w 3)/w 1)/w 3,1],
        ![0,w 3*(w 0+w 3)/w 1,w 3],?_⟩
      ext i
      fin_cases i <;> simp [coverDisplacement,rootDisplacement] <;>
        field_simp <;> ring_nf <;> simp only [CharTwo.two_eq_zero,mul_zero,add_zero]


/-- The four-dimensional commutator space in the trace-zero cover. -/
def commutatorLift : (Fin 4 → F) →ₗ[F] Natural.TraceZero F where
  toFun w := ⟨![w 0,w 1,w 2,w 3,w 3,0,0,0],by simp [Natural.mem_traceZero,trace,CharTwo.add_self_eq_zero]⟩
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- The literal natural projection kills exactly the scalar coordinate of this space. -/
theorem commutatorLift_natural_zero (w : Fin 4 → F) :
    Natural.mk F (commutatorLift w) = 0 ↔ ![w 0,w 1,w 2] = (0 : Fin 3 → F) := by
  rw [←(Restricted.NaturalCoordinates.equiv F).map_eq_zero_iff]
  change ![w 0,w 1,w 2,0,0,0] = (0 : Fin 6 → F) ↔ _
  constructor
  · intro h
    ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    ext i
    fin_cases i <;> simp_all

/-- The three root parameters act on the original seven-space with the
additional central coordinate c*z. -/
theorem elementary_cover_displacement (p : Multiplicative (Fin 3 → F))
    (x : Natural.TraceZero F) :
    Natural.traceZeroAction F (EvenTwoRank.elementaryEmbedding F p) x - x =
      commutatorLift (coverDisplacement p.toAdd ![x.val 5,x.val 6,x.val 7]) := by
  have he : EvenTwoRank.elementaryEmbedding F p =
      rootA (p.toAdd 0) * (rootB (p.toAdd 1) * rootC (p.toAdd 2)) := by
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,
      unipotentProduct,mul_assoc]
  have hx : x.val 4 = x.val 3 := by
    have ht : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right ht
  rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply]
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [Natural.traceZeroAction_val,rootA,rootAEquiv,rootALinear,rootAApply,
      rootB,rootBEquiv,rootBLinear,rootBApply,rootC,rootCEquiv,rootCLinear,rootCApply,
      commutatorLift,coverDisplacement,rootDisplacement,hx] <;> ring_nf <;> simp [CharTwo.sub_eq_add,CharTwo.neg_eq]

private def lowerLift (v : Fin 3 → F) : Natural.TraceZero F :=
  ⟨![0,0,0,0,0,v 0,v 1,v 2],by simp [Natural.mem_traceZero,trace]⟩

variable [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (Model F) W)
  (q : W →ₗ[ZMod 2] Natural.Space F)
  (f : Natural.TraceZero F →ₗ[ZMod 2] W)
  (hf : Function.Surjective f)
  (hover : ∀ x, q (f x) = Natural.mk F x)
  (hact : ∀ g x, f (Natural.traceZeroAction F g x) = σ g (f x))

include hover hact in
/-- In any quotient over the original natural projection, a single
commutator in the central kernel is zero. -/
theorem elementary_quotient_displacement_zero
    (p : Multiplicative (Fin 3 → F)) (x : Natural.TraceZero F)
    (h : q (σ (EvenTwoRank.elementaryEmbedding F p) (f x) - f x) = 0) :
    σ (EvenTwoRank.elementaryEmbedding F p) (f x) - f x = 0 := by
  have he : σ (EvenTwoRank.elementaryEmbedding F p) (f x) - f x =
      f (commutatorLift (coverDisplacement p.toAdd ![x.val 5,x.val 6,x.val 7])) := by
    rw [←elementary_cover_displacement,map_sub,hact]
  rw [he,hover,commutatorLift_natural_zero] at h
  have h' : rootDisplacement p.toAdd ![x.val 5,x.val 6,x.val 7] = 0 := by
    ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
  rw [he,coverDisplacement_natural_zero _ _ h',map_zero,map_zero]

include hf hact in
private theorem quotient_moved_le_lift :
    Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)) ≤
      (f.comp ((commutatorLift (F := F)).restrictScalars (ZMod 2))).range := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨p,w⟩,rfl⟩
  obtain ⟨x,rfl⟩ := hf w
  refine ⟨coverDisplacement p.toAdd ![x.val 5,x.val 6,x.val 7],?_⟩
  change f (commutatorLift _) = σ (EvenTwoRank.elementaryEmbedding F p) (f x) - f x
  rw [←elementary_cover_displacement,map_sub,hact]

include hf hover hact in
/-- The central kernel in the actual moved space is characterized by the
failure to be a single commutator, rather than by its order. -/
theorem quotient_moved_kernel_iff
    (w : W) (hw : w ∈ Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)))
    (hne : w ≠ 0) :
    q w = 0 ↔ ¬ ∃ p v, σ (EvenTwoRank.elementaryEmbedding F p) v - v = w := by
  constructor
  · intro h ⟨p,v,hv⟩
    obtain ⟨x,rfl⟩ := hf v
    exact hne (hv.symm.trans (elementary_quotient_displacement_zero σ q f hover hact p x (hv.symm ▸ h)))
  · intro h
    by_contra hq
    obtain ⟨y,hy⟩ := quotient_moved_le_lift σ f hf hact hw
    change f (commutatorLift y) = w at hy
    have hn : ![y 0,y 1,y 2] ≠ (0 : Fin 3 → F) := by
      intro hz
      apply hq
      rw [←hy,hover,commutatorLift_natural_zero]
      exact hz
    obtain ⟨p,v,hpv⟩ := coverDisplacement_surjective_off_scalar y hn
    apply h
    refine ⟨Multiplicative.ofAdd p,f (lowerLift v),?_⟩
    rw [←hact,←map_sub,elementary_cover_displacement]
    change f (commutatorLift (coverDisplacement p ![v 0,v 1,v 2])) = w
    have hv : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    rw [hv,hpv,hy]



include hact in
private theorem quotient_noncentral_lift_mem (y : Fin 4 → F)
    (hy : ![y 0,y 1,y 2] ≠ (0 : Fin 3 → F)) :
    f (commutatorLift y) ∈ Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)) := by
  obtain ⟨p,v,hpv⟩ := coverDisplacement_surjective_off_scalar y hy
  have hm := Coinvariants.sub_mem_ker (ρ := σ.comp (EvenTwoRank.elementaryEmbedding F))
    (Multiplicative.ofAdd p) (f (lowerLift v))
  change σ (EvenTwoRank.elementaryEmbedding F (Multiplicative.ofAdd p)) (f (lowerLift v)) -
    f (lowerLift v) ∈ _ at hm
  rw [←hact,←map_sub,elementary_cover_displacement] at hm
  change f (commutatorLift (coverDisplacement p ![v 0,v 1,v 2])) ∈ _ at hm
  have hv : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
  rwa [hv,hpv] at hm

include hact in
private theorem quotient_lift_mem (y : Fin 4 → F) :
    f (commutatorLift y) ∈ Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)) := by
  by_cases hy : ![y 0,y 1,y 2] = (0 : Fin 3 → F)
  · have h0 : y 0 = 0 := congrFun hy 0
    have h1 : y 1 = 0 := congrFun hy 1
    have h2 : y 2 = 0 := congrFun hy 2
    let u : Fin 4 → F := ![1,0,0,y 3]
    let v : Fin 4 → F := ![1,0,0,0]
    have hu : ![u 0,u 1,u 2] ≠ (0 : Fin 3 → F) := by
      intro h
      exact one_ne_zero (congrFun h 0)
    have hv : ![v 0,v 1,v 2] ≠ (0 : Fin 3 → F) := by
      intro h
      exact one_ne_zero (congrFun h 0)
    have he : y = u-v := by
      ext i
      fin_cases i <;> simp [u,v,h0,h1,h2]
    rw [he,map_sub,map_sub]
    exact Submodule.sub_mem _ (quotient_noncentral_lift_mem σ f hact u hu)
      (quotient_noncentral_lift_mem σ f hact v hv)
  · exact quotient_noncentral_lift_mem σ f hact y hy

include hf hover hact in
/-- The whole original central kernel lies in the elementary actor's moved
space, including any proper binary quotient of the scalar radical. -/
theorem quotient_kernel_le_moved :
    q.ker ≤ Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)) := by
  intro w hw
  obtain ⟨x,rfl⟩ := hf w
  have hx : Natural.mk F x = 0 := (hover x).symm.trans hw
  obtain ⟨a,ha⟩ := (Natural.mk_eq_zero_iff F x).mp hx
  have he : x = commutatorLift ![0,0,0,a] := by
    apply Subtype.ext
    rw [←ha]
    ext i
    fin_cases i <;> simp [unit,commutatorLift]
  rw [he]
  exact quotient_lift_mem σ f hact _

omit q f hf hover hact in
omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem moved_comp_eq_of_range {A B : Type*} [Group A] [Group B]
    (α : A →* Model F) (β : B →* Model F) (h : α.range = β.range) :
    Coinvariants.ker (σ.comp α) = Coinvariants.ker (σ.comp β) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    obtain ⟨b,hb⟩ := (show α a ∈ β.range from h ▸ ⟨a,rfl⟩)
    change σ (α a) v - v ∈ _
    rw [←hb]
    exact Coinvariants.sub_mem_ker (ρ := σ.comp β) b v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨b,v⟩,rfl⟩
    obtain ⟨a,ha⟩ := (show β b ∈ α.range from h.symm ▸ ⟨b,rfl⟩)
    change σ (β b) v - v ∈ _
    rw [←ha]
    exact Coinvariants.sub_mem_ker (ρ := σ.comp α) a v

variable [Finite F] [FiniteDimensional (ZMod 2) W]

omit q f hf hover hact in
/-- Every cover of the full nonbinary G₂ natural module is a quotient of the
orthogonal cover through the literal natural projection. -/
theorem full_cover_orthogonal_quotient (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) :
    ∃ f : Natural.TraceZero F →ₗ[ZMod 2] W, Function.Surjective f ∧
      (∀ x, p (f x) = Natural.mk F x) ∧
      ∀ g x, f (Natural.traceZeroAction F g x) = σ g (f x) := by
  have hperfect := (Atlas.G2.isPerfect (F := F) hF).commutator_eq_top
  let pd : Representation.IntertwiningMap (σ.comp (commutator (Model F)).subtype)
      (Natural.OrthogonalCover.binaryNatural F) :=
    p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g x => LinearMap.congr_fun (p.isIntertwining' g.val) x)
  have hpd : IsCover pd := by
    refine ⟨hp.1,fun x hx g => hp.2.1 hx g.val,?_⟩
    have he := moved_comp_eq_of_range σ (commutator (Model F)).subtype
      (MonoidHom.id (Model F)) (by rw [range_subtype,hperfect]; exact (MonoidHom.range_eq_top_of_surjective (MonoidHom.id _) Function.surjective_id).symm)
    simpa using he.trans hp.2.2
  obtain ⟨f,hf,ho⟩ := Natural.OrthogonalCover.exists_quotient F pd hpd
  refine ⟨f.toLinearMap,hf,ho,?_⟩
  intro g x
  let gd : commutator (Model F) := ⟨g,by rw [hperfect]; trivial⟩
  exact LinearMap.congr_fun (f.isIntertwining' gd) x

omit q f hf hover hact in
/-- The kernel criterion holds for every perfect central cover on the
literal A--B--C actor, without assuming a split cover. -/
theorem full_cover_elementary_kernel (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) (w : W)
    (hw : w ∈ Coinvariants.ker (σ.comp (EvenTwoRank.elementaryEmbedding F)))
    (hne : w ≠ 0) :
    p w = 0 ↔ ¬ ∃ a v, σ (EvenTwoRank.elementaryEmbedding F a) v - v = w := by
  obtain ⟨f,hf,ho,ha⟩ := full_cover_orthogonal_quotient σ hF p hp
  exact quotient_moved_kernel_iff σ p.toLinearMap f hf ho ha w hw hne




private theorem conjugate_displacement
    {k J W₁ : Type*} [Field k] [Group J] [AddCommGroup W₁] [Module k W₁]
    (σ₁ : Representation k J W₁) (g h : J) (v : W₁) :
    σ₁ g⁻¹ (σ₁ (g*h*g⁻¹) v - v) = σ₁ h (σ₁ g⁻¹ v) - σ₁ g⁻¹ v := by
  rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
  have he : g⁻¹*(g*h*g⁻¹) = h*g⁻¹ := by group
  rw [he]

private theorem moved_conjugate_mem
    {k J A W₁ : Type*} [Field k] [Group J] [Group A]
    [AddCommGroup W₁] [Module k W₁]
    (σ₁ : Representation k J W₁) (α : A →* J) (g : J) (w : W₁)
    (hw : w ∈ Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α))) :
    σ₁ g⁻¹ w ∈ Coinvariants.ker (σ₁.comp α) := by
  have hle : Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α)) ≤
      (Coinvariants.ker (σ₁.comp α)).comap (σ₁ g⁻¹) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    change σ₁ g⁻¹ (σ₁ (g*α a*g⁻¹) v - v) ∈ Coinvariants.ker (σ₁.comp α)
    rw [conjugate_displacement]
    exact Coinvariants.sub_mem_ker (ρ := σ₁.comp α) a _
  exact hle hw

private theorem kernel_criterion_conjugate
    {k J A W₁ : Type*} [Field k] [Group J] [Group A]
    [AddCommGroup W₁] [Module k W₁]
    (σ₁ : Representation k J W₁) (α : A →* J)
    (P : Submodule k W₁) (hP : P ≤ fixed σ₁)
    (hcrit : ∀ w ∈ Coinvariants.ker (σ₁.comp α), w ≠ 0 →
      (w ∈ P ↔ ¬ ∃ a v, σ₁ (α a) v - v = w))
    (g : J) (w : W₁)
    (hw : w ∈ Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α)))
    (hne : w ≠ 0) :
    w ∈ P ↔ ¬ ∃ a v, σ₁ (g*α a*g⁻¹) v - v = w := by
  have hne' : σ₁ g⁻¹ w ≠ 0 := by
    intro h
    exact hne ((σ₁.apply_bijective g⁻¹).1 (h.trans (map_zero _).symm))
  have hP' : σ₁ g⁻¹ w ∈ P ↔ w ∈ P := by
    constructor
    · intro h
      have he : w = σ₁ g⁻¹ w := (σ₁.self_inv_apply g w).symm.trans (hP h g)
      rwa [he]
    · intro h
      rwa [hP h g⁻¹]
  rw [←hP',hcrit _ (moved_conjugate_mem σ₁ α g w hw) hne']
  apply not_congr
  constructor
  · rintro ⟨a,v,hv⟩
    refine ⟨a,σ₁ g v,?_⟩
    apply (σ₁.apply_bijective g⁻¹).1
    rw [conjugate_displacement,σ₁.inv_self_apply,hv]
  · rintro ⟨a,v,hv⟩
    exact ⟨a,σ₁ g⁻¹ v,(conjugate_displacement σ₁ g (α a) v).symm.trans (congrArg (σ₁ g⁻¹) hv)⟩

private theorem kernel_le_moved_conjugate
    {k J A W₁ : Type*} [Field k] [Group J] [Group A]
    [AddCommGroup W₁] [Module k W₁]
    (σ₁ : Representation k J W₁) (α : A →* J)
    (P : Submodule k W₁) (hP : P ≤ fixed σ₁)
    (hle : P ≤ Coinvariants.ker (σ₁.comp α)) (g : J) :
    P ≤ Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α)) := by
  have hm : Coinvariants.ker (σ₁.comp α) ≤
      (Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α))).comap (σ₁ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    have he : σ₁ g (σ₁ (α a) v-v) = σ₁ (g*α a*g⁻¹) (σ₁ g v) - σ₁ g v := by
      apply (σ₁.apply_bijective g⁻¹).1
      rw [σ₁.inv_self_apply,conjugate_displacement,σ₁.inv_self_apply]
    change σ₁ g (σ₁ (α a) v-v) ∈ Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α))
    rw [he]
    exact Coinvariants.sub_mem_ker (ρ := σ₁.comp ((MulAut.conj g).toMonoidHom.comp α)) a _
  intro w hw
  have hh := hm (hle hw)
  change σ₁ g w ∈ Coinvariants.ker (σ₁.comp ((MulAut.conj g).toMonoidHom.comp α)) at hh
  rwa [hP hw g] at hh

omit q f hf hover hact in
/-- Conjugating the elementary actor preserves the kernel criterion on the
original cover. The same conjugator is used for the actor and cover map. -/
theorem full_cover_conjugate_elementary_kernel (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) (g : Model F) (w : W)
    (hw : w ∈ Coinvariants.ker (σ.comp
      ((MulAut.conj g).toMonoidHom.comp (EvenTwoRank.elementaryEmbedding F))))
    (hne : w ≠ 0) :
    p w = 0 ↔ ¬ ∃ a v,
      σ (g * EvenTwoRank.elementaryEmbedding F a * g⁻¹) v - v = w := by
  exact kernel_criterion_conjugate σ (EvenTwoRank.elementaryEmbedding F)
    p.toLinearMap.ker hp.2.1
    (fun w hw hne => full_cover_elementary_kernel σ hF p hp w hw hne) g w hw hne

omit q f hf hover hact in
/-- For every genuine natural offender, the fixed kernel in its moved space
is exactly the nonzero elements that are not single commutators. -/
theorem full_cover_offender_kernel {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) (A : Subgroup (Model F))
    (hA : Representation.BinaryOffender.IsOffender
      (NaturalOffenders.binaryNatural (F := F)) A)
    (w : W) (hw : w ∈ Coinvariants.ker (σ.comp A.subtype)) (hne : w ≠ 0) :
    p w = 0 ↔ ¬ ∃ a ∈ A, ∃ v, σ a v - v = w := by
  obtain ⟨g,hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary hF (by omega) A hA
  let α := (MulAut.conj g).toMonoidHom.comp (EvenTwoRank.elementaryEmbedding F)
  have hr : α.range = A := by rw [MonoidHom.range_comp]; exact hg.symm
  have hm : Coinvariants.ker (σ.comp α) = Coinvariants.ker (σ.comp A.subtype) :=
    moved_comp_eq_of_range σ α A.subtype (by rw [hr,range_subtype])
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  rw [full_cover_conjugate_elementary_kernel σ hcard p hp g w (hm.symm ▸ hw) hne]
  apply not_congr
  constructor
  · rintro ⟨a,v,he⟩
    exact ⟨α a,hr ▸ (show α a ∈ α.range from ⟨a,rfl⟩),v,he⟩
  · rintro ⟨a,ha,v,he⟩
    obtain ⟨b,rfl⟩ := (show a ∈ α.range from hr.symm ▸ ha)
    exact ⟨b,v,he⟩



omit q f hf hover hact in
/-- The full central kernel is moved by every conjugate of the root actor. -/
theorem full_cover_conjugate_kernel_le_moved (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) (g : Model F) :
    p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp
      ((MulAut.conj g).toMonoidHom.comp (EvenTwoRank.elementaryEmbedding F))) := by
  obtain ⟨f,hf,ho,ha⟩ := full_cover_orthogonal_quotient σ hF p hp
  exact kernel_le_moved_conjugate σ (EvenTwoRank.elementaryEmbedding F)
    p.toLinearMap.ker hp.2.1 (quotient_kernel_le_moved σ p.toLinearMap f hf ho ha) g

omit q f hf hover hact in
/-- Every natural offender moves a subspace containing the original central
kernel; the acting subgroup and cover projection are retained. -/
theorem full_cover_offender_kernel_le_moved {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (p : σ.IntertwiningMap (restrictScalars (k := ZMod 2) (Natural.action F)))
    (hp : IsCover p) (A : Subgroup (Model F))
    (hA : Representation.BinaryOffender.IsOffender
      (NaturalOffenders.binaryNatural (F := F)) A) :
    p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp A.subtype) := by
  obtain ⟨g,hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary hF (by omega) A hA
  let α := (MulAut.conj g).toMonoidHom.comp (EvenTwoRank.elementaryEmbedding F)
  have hr : α.range = A := by rw [MonoidHom.range_comp]; exact hg.symm
  have hm : Coinvariants.ker (σ.comp α) = Coinvariants.ker (σ.comp A.subtype) :=
    moved_comp_eq_of_range σ α A.subtype (by rw [hr,range_subtype])
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  rw [←hm]
  exact full_cover_conjugate_kernel_le_moved σ hcard p hp g


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
