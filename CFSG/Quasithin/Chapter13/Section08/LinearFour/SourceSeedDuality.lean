module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Covered
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry

/-!
# The original seed plane and its quotient have the same action kernel

The original natural-six action, including the covered A₆ case, preserves
its nondegenerate alternating pairing. Sylow conjugacy and uniqueness of
the invariant plane show that the actual V₂ is Lagrangian. The same
argument identifies V₃ with the perpendicular of V₁. Thus an element of
LT outside N(V₁) moves V₃, retaining the source conjugator.

The pairing identifies pointwise fixation of V₂ with fixation of V/V₂.
The final theorem states this for actual ambient commutators and the literal
centralizer, so the original I₂ centralizer kernel can construct the seed
quotient action without an ordinary-A₆ hypothesis.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
§B.3,13.5.3--4 and13.8.29(3), printed pp.83--85,916,964.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing Representation.BinaryOffender

private theorem quotient_fixed_iff_plane_fixed
    (P : Submodule (ZMod 2) (natural (Fin 6))) (hP : form.orthogonal P = P)
    (g : Equiv.Perm (Fin 6)) :
    (∀ v, naturalRepresentation (Fin 6) g v - v ∈ P) ↔
      ∀ v ∈ P, naturalRepresentation (Fin 6) g v = v := by
  constructor
  · intro h v hv
    apply sub_eq_zero.mp
    apply form_nondegenerate.1
    intro w
    have hw : naturalRepresentation (Fin 6) g⁻¹ w - w ∈ P := by
      have hh := P.neg_mem (h (naturalRepresentation (Fin 6) g⁻¹ w))
      simpa only [Representation.self_inv_apply, neg_sub] using hh
    have hz := (hP.symm ▸ hw : _ ∈ form.orthogonal P) v hv
    have he := form_invariant g v (naturalRepresentation (Fin 6) g⁻¹ w)
    rw [Representation.self_inv_apply] at he
    simpa only [map_sub, LinearMap.sub_apply, he] using hz
  · intro h v
    rw [← hP]
    intro w hw
    change form w (naturalRepresentation (Fin 6) g v - v) = 0
    rw [map_sub, ← h w hw, form_invariant, h w hw, sub_self]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

private theorem original_flag_stable
    (f : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hf : ∀ (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (d.coordinate (V.normalizerMonoidHom ⟨a,d.normalizes_V a.property⟩ v)).toAdd =
        naturalRepresentation (Fin 6) (f a) (d.coordinate v).toAdd)
    (B : Subgroup G)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (ha : (a:G) ∈ normalizer (B:Set G)) :
    f a ∈ subspaceStabilizer (naturalRepresentation (Fin 6)) (local_flag_image d B) := by
  intro w
  obtain ⟨v,rfl⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
  change naturalRepresentation (Fin 6) (f a) (d.coordinate v).toAdd ∈ _ ↔ (d.coordinate v).toAdd ∈ _
  rw [← hf]
  have hm (x : V) : (d.coordinate x).toAdd ∈ local_flag_image d B ↔ (x:G) ∈ B := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hh : y = x := d.coordinate.injective he
      exact hh ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  rw [hm,hm]
  exact ((mem_normalizer_iff.mp ha) v).symm

private theorem original_flag_normalized
    (f : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hf : ∀ (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (d.coordinate (V.normalizerMonoidHom ⟨a,d.normalizes_V a.property⟩ v)).toAdd =
        naturalRepresentation (Fin 6) (f a) (d.coordinate v).toAdd)
    (B : Subgroup G) (hBV : B ≤ V)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G))
    (ha : f a ∈ subspaceStabilizer (naturalRepresentation (Fin 6)) (local_flag_image d B)) :
    (a:G) ∈ normalizer (B:Set G) := by
  have hm (x : V) : (d.coordinate x).toAdd ∈ local_flag_image d B ↔ (x:G) ∈ B := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact (show y = x from d.coordinate.injective he) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    let v : V := ⟨x,hBV hx⟩
    have hh := (ha (d.coordinate v).toAdd).mpr ((hm v).mpr hx)
    rw [← hf,hm] at hh
    exact hh
  · intro hx
    have hxV := (mem_normalizer_iff.mp (d.normalizes_V a.property) x).mpr (hBV hx)
    let v : V := ⟨x,hxV⟩
    have hh : (d.coordinate (V.normalizerMonoidHom ⟨a,d.normalizes_V a.property⟩ v)).toAdd ∈
        local_flag_image d B := (hm _).mpr hx
    rw [hf] at hh
    exact (hm v).mp ((ha _).mp hh)

/-- The literal Sylow-stable plane is Lagrangian, also in the covered case. -/
theorem source_seed_plane_perp : form.orthogonal (local_flag_image d V₂) = local_flag_image d V₂ := by
  obtain ⟨f,hfL,hf⟩ := local_permutation_extension d
  have hA : alternatingGroup (Fin 6) ≤ f.range := by
    intro a ha
    obtain ⟨x,hx⟩ := d.local_quotient.surjective ⟨a,ha⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) x
    exact ⟨inclusion le_sup_left l,(hfL l).trans (congrArg Subtype.val hx)⟩
  let Q := (T.subtype (show (T:Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ : (Q:Subgroup f.range).map f.range.subtype = (T.subgroupOf (L ⊔ T)).map f := by
    rw [Sylow.coe_mapSurjective,map_map,Sylow.coe_subtype]
    rfl
  let P := local_flag_image d V₂
  have hdim : Module.finrank (ZMod 2) P = 2 :=
    local_flag_image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 (by simpa using d.plane_card)
  have hP : (Q:Subgroup f.range).map f.range.subtype ≤ subspaceStabilizer (naturalRepresentation (Fin 6)) P := by
    rw [hQ]
    rintro _ ⟨a,ha,rfl⟩
    exact original_flag_stable d f hf V₂ a (d.plane_stable ha)
  have hperp := hP.trans (stabilizer_le_orthogonal_stabilizer P)
  obtain ⟨g,hg⟩ := TransvectionParabolic.EarlierCore.PlaneGeometry.exists_conjugate_T0_le f.range hA Q
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom g.val⁻¹)
  have hleft : (form.orthogonal P).map e.toLinearMap = canonicalPlane := by
    apply canonicalPlane_unique
    · rw [e.finrank_map_eq,LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
        finrank_natural_even (Fin 6) (by decide),hdim]
      rfl
    · exact TransvectionParabolic.EarlierCore.PlaneGeometry.aligned_invariant f.range Q g hg _ hperp
  have hright : P.map e.toLinearMap = canonicalPlane :=
    canonicalPlane_unique _ ((e.finrank_map_eq P).trans hdim)
      (TransvectionParabolic.EarlierCore.PlaneGeometry.aligned_invariant f.range Q g hg P hP)
  exact (Submodule.map_injective_of_injective e.injective) (hleft.trans hright.symm)

/-- The literal seed hyperplane is perpendicular to the original point. -/
theorem source_seed_hyperplane_perp :
    local_flag_image d V₃ = form.orthogonal (local_flag_image d V₁) := by
  obtain ⟨f,hfL,hf⟩ := local_permutation_extension d
  have hA : alternatingGroup (Fin 6) ≤ f.range := by
    intro a ha
    obtain ⟨x,hx⟩ := d.local_quotient.surjective ⟨a,ha⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) x
    exact ⟨inclusion le_sup_left l,(hfL l).trans (congrArg Subtype.val hx)⟩
  let Q := (T.subtype (show (T:Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ : (Q:Subgroup f.range).map f.range.subtype = (T.subgroupOf (L ⊔ T)).map f := by
    rw [Sylow.coe_mapSurjective,map_map,Sylow.coe_subtype]
    rfl
  apply NaturalHyperplanes.sylow_invariant_hyperplane_eq_orthogonal f.range hA Q
  · exact local_flag_image_dim d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 (by simpa using d.line_card)
  · exact local_flag_image_dim d V₃ d.seed_le 3 (by simpa using d.seed_card)
  · rw [hQ]
    rintro _ ⟨a,ha,rfl⟩
    exact original_flag_stable d f hf V₁ a (d.line_stable ha)
  · rw [hQ]
    rintro _ ⟨a,ha,rfl⟩
    exact original_flag_stable d f hf V₃ a (d.seed_stable ha)

include d in
/-- The source conjugator outside the point normalizer also moves the seed. -/
theorem source_seed_moved_of_point_moved
    (a : (L ⊔ (T:Subgroup G) : Subgroup G))
    (ha : (a:G) ∉ normalizer (V₁:Set G)) : (a:G) ∉ normalizer (V₃:Set G) := by
  intro hh
  obtain ⟨f,hfL,hf⟩ := local_permutation_extension d
  have h := (stabilizer_le_orthogonal_stabilizer (local_flag_image d V₃))
    (original_flag_stable d f hf V₃ a hh)
  rw [source_seed_hyperplane_perp d,
    LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at h
  exact ha (original_flag_normalized d f hf V₁
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) a h)

include d in
/-- On the actual natural module, fixing V/V₂ is equivalent to centralizing V₂. -/
theorem source_seed_kernel_iff
    (a : (L ⊔ (T:Subgroup G) : Subgroup G)) :
    (∀ v ∈ V, ⁅(a:G),v⁆ ∈ V₂) ↔ (a:G) ∈ centralizer (V₂:Set G) := by
  obtain ⟨f,hfL,hf⟩ := local_permutation_extension d
  have he := quotient_fixed_iff_plane_fixed (local_flag_image d V₂) (source_seed_plane_perp d) (f a)
  have h2V := d.plane_le_seed.trans d.seed_le
  have hm (x : V) : (d.coordinate x).toAdd ∈ local_flag_image d V₂ ↔ (x:G) ∈ V₂ := by
    constructor
    · rintro ⟨y,hy,hyx⟩
      exact (show y = x from d.coordinate.injective hyx) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hdisp (v : V) : naturalRepresentation (Fin 6) (f a) (d.coordinate v).toAdd -
      (d.coordinate v).toAdd =
      (d.coordinate (V.normalizerMonoidHom ⟨a,d.normalizes_V a.property⟩ v * v⁻¹)).toAdd := by
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hf,sub_eq_add_neg]
  constructor
  · intro h
    have hfix := he.mp (by
      intro w
      obtain ⟨v,rfl⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
      change naturalRepresentation (Fin 6) (f a) (d.coordinate v).toAdd - (d.coordinate v).toAdd ∈ _
      rw [hdisp,hm]
      exact h v v.property)
    apply mem_centralizer_iff.mpr
    intro v hv
    let x : V := ⟨v,h2V hv⟩
    have hx := hfix (d.coordinate x).toAdd ((hm x).mpr hv)
    rw [← hf] at hx
    have hh := congrArg Subtype.val (d.coordinate.injective hx)
    change (a:G)*v*(a:G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro h v hv
    let x : V := ⟨v,hv⟩
    have hfix : ∀ w ∈ local_flag_image d V₂, naturalRepresentation (Fin 6) (f a) w = w := by
      rintro w ⟨y,hy,rfl⟩
      change naturalRepresentation (Fin 6) (f a) (d.coordinate y).toAdd = (d.coordinate y).toAdd
      rw [← hf]
      apply congrArg (fun z : V => (d.coordinate z).toAdd)
      apply Subtype.ext
      change (a:G)*(y:G)*(a:G)⁻¹ = y
      rw [← (mem_centralizer_iff.mp h) y hy,mul_inv_cancel_right]
    have hh := he.mpr hfix (d.coordinate x).toAdd
    rw [hdisp,hm] at hh
    exact hh

end CFSG.Quasithin.Chapter13.Section08.LinearFour
