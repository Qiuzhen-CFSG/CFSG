module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoreGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerKernel

/-!
# Full cubic-normalizer equivariance of the core comparison

The same native H/Q marking makes the perfect six-cover comparison
intertwine any matching pair of normalizer actors. The discrepancy of
their actions on Q is trivial on Q/Z(Q). It commutes with the cubic
scalar action because both actors conjugate that action in the same way.
Cubic fixed-point freeness then kills the discrepancy. This includes
actors inverting the cubic subgroup, with no assumed normalizer map.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
Matching actors still differ by the original central involution; this
argument does not assume or assert their square-one lifting equation.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

omit [IsExtraspecial 2 (core z)] in
include h in
private theorem cover_core_ker_central :
    ((QuotientGroup.mk' (core z)).comp (cubicCentralizerInH e X).subtype).ker ≤
      center (cubicCentralizerInH e X) := by
  intro c hc
  have hQ : c.val ∈ core z := (QuotientGroup.eq_one_iff _).mp hc
  have hz : c.val ∈ center (centralizer z) := by
    rw [←core_center_eq_centralizer_center h]
    exact mem_map_of_mem (core z).subtype
      ((core_cubic_centralizer h e X).le (show
        (⟨c.val,hQ⟩ : core z) ∈ (cubicCentralizerInH e X).subgroupOf (core z) from c.property))
  exact mem_center_iff.mpr (fun d => Subtype.ext (mem_center_iff.mp hz d.val))

/-- Matching the actual H/Q actors makes the marked cover comparison equivariant. -/
theorem cubicNativeEquiv_intertwines
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X')
    (hn : cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n))
    (c : cubicCentralizerInH e X) :
    φ (cubicNormalizerAction e X n c) = cubicNormalizerAction e' X' n' (φ c) := by
  let := hp
  have he : φ.toMonoidHom.comp (cubicNormalizerAction e X n).toMonoidHom =
      (cubicNormalizerAction e' X' n').toMonoidHom.comp φ.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq
      ((QuotientGroup.mk' (core z')).comp (cubicCentralizerInH e' X').subtype)
      (cover_core_ker_central h' e' X')
    apply MonoidHom.ext
    intro x
    change QuotientGroup.mk' (core z') (φ (cubicNormalizerAction e X n x)).val =
      QuotientGroup.mk' (core z') (n'.val * (φ x).val * n'.val⁻¹)
    rw [cubicNativeComparison_core h e X h' e' X' φ hφ]
    change coreQuotientComparison h e X h' e' X'
      (QuotientGroup.mk' (core z) (n.val*x.val*n.val⁻¹)) = _
    simp only [map_mul,map_inv]
    rw [cubicNativeComparison_core h e X h' e' X' φ hφ]
    change _ = cubicNormalizerToCore e' X' n' * _ * (cubicNormalizerToCore e' X' n')⁻¹
    rw [hn]
    rfl
  exact DFunLike.congr_fun he c

private theorem coreEquiv_matching_actor_quotient
    (ψ : core z ≃* core z')
    (hψ : ∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
      coreSpaceComparison h e X h' e' X'
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))
    (n : centralizer z) (n' : centralizer z')
    (hn : QuotientGroup.mk' (core z') n' =
      coreQuotientComparison h e X h' e' X' (QuotientGroup.mk' (core z) n)) :
    quotientAut (center (core z')) (MulAut.congr ψ (MulAut.conjNormal n)) =
      quotientAut (center (core z')) (MulAut.conjNormal n') := by
  apply MulEquiv.ext
  intro v
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (core z')) v
  obtain ⟨q,rfl⟩ := ψ.surjective q
  rw [quotientAut_apply_mk,quotientAut_apply_mk]
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
  apply Additive.ofMul.injective
  rw [hψ]
  have hh := coreSpaceComparison_intertwines h e X h' e' X'
    (QuotientGroup.mk' (core z) n)
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))
  rw [←hn,←hψ q] at hh
  simpa only [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk] using hh

omit [IsExtraspecial 2 (core z')] in
include h' in
private theorem core_fixedFree
    (v : core z' ⧸ center (core z'))
    (hv : ∀ a : cubicScalars e' X',
      quotientAut (center (core z')) (MulAut.conjNormal a.val.val) v = v) : v = 1 := by
  apply (cubicAction_fixed_iff h' e' X' v).mp
  intro x
  have hx : (x.val : centralizer z') ∈ cubicSylowImage e' X' :=
    mem_map_of_mem (CubicLift.subgroup e').subtype x.property
  let c : cubicCentralizerInH e' X' := ⟨x.val,cubicSylowImage_le_centralizer h' e' X' hx⟩
  have hh := hv ⟨c,hx⟩
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center (core z')) v
  rw [cubicAction_mk]
  exact (quotientAut_apply_mk _ _ _).symm.trans hh

/-- Cubic fixed-point freeness removes the discrepancy for the full normalizer,
including its actors which invert the cubic subgroup. -/
theorem coreEquiv_intertwines_normalizer
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (ψ : core z ≃* core z')
    (hψ : ∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
      coreSpaceComparison h e X h' e' X'
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))
    (hψc : ∀ c : cubicCentralizerInH e X, ∀ q : core z,
      ψ (MulAut.conjNormal c.val q) = MulAut.conjNormal (φ c).val (ψ q))
    (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X')
    (hn : cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n))
    (q : core z) :
    ψ (MulAut.conjNormal n.val q) = MulAut.conjNormal n'.val (ψ q) := by
  let ρ : centralizer z →* MulAut (core z) := MulAut.conjNormal
  let σ : centralizer z' →* MulAut (core z') := MulAut.conjNormal
  let α := MulAut.congr ψ (ρ n.val)
  let β := σ n'.val
  have hc (c : cubicCentralizerInH e X) : MulAut.congr ψ (ρ c.val) = σ (φ c).val := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x,rfl⟩ := ψ.surjective x
    simpa only [ρ,σ,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      using hψc c x
  have hconj (c : cubicCentralizerInH e X) :
      α * σ (φ c).val * α⁻¹ = β * σ (φ c).val * β⁻¹ := by
    have he := congrArg (fun c : cubicCentralizerInH e' X' => σ c.val)
      (cubicNativeEquiv_intertwines h e X h' e' X' hp φ hφ n n' hn c)
    rw [←hc] at he
    change MulAut.congr ψ (ρ (n.val*c.val*n.val⁻¹)) =
      σ (n'.val*(φ c).val*n'.val⁻¹) at he
    simpa only [map_mul,map_inv,hc,α,β] using he
  have hd : quotientAut (center (core z')) (β⁻¹*α) = 1 := by
    have he := coreEquiv_matching_actor_quotient h e X h' e' X' ψ hψ n.val n'.val hn
    change quotientAut (center (core z')) α = quotientAut (center (core z')) β at he
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hcomm (a : cubicScalars e' X') : Commute (β⁻¹*α) (σ a.val.val) := by
    obtain ⟨c,hc'⟩ := φ.surjective a.val
    have he := hconj c
    rw [hc'] at he
    change (β⁻¹*α) * σ a.val.val = σ a.val.val * (β⁻¹*α)
    calc
      _ = β⁻¹ * (α * σ a.val.val * α⁻¹) * α := by group
      _ = β⁻¹ * (β * σ a.val.val * β⁻¹) * α := by rw [he]
      _ = _ := by group
  have h1 := QuadraticLift.quotient_trivial_of_commute_fixedFree
    (fun a : cubicScalars e' X' => σ a.val.val)
    (core_fixedFree h' e' X') (β⁻¹*α) hd hcomm
  have he : α = β := (inv_mul_eq_one.mp h1).symm
  have hh := MulEquiv.congr_fun he (ψ q)
  simpa only [α,β,ρ,σ,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh

/-- Construct the cover and core maps with equivariance under every matching
normalizer actor, retaining the literal H/Q marking. -/
theorem exists_cubic_coreGroup_equiv_normalizer
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X')) :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (ψ : core z ≃* core z'),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
        coreSpaceComparison h e X h' e' X'
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ∧
      ψ (coreMarker h) = coreMarker h' ∧
      (∀ c : cubicCentralizerInH e X, ∀ q : core z,
        ψ (MulAut.conjNormal c.val q) = MulAut.conjNormal (φ c).val (ψ q)) ∧
      ∀ (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X'),
        cubicNormalizerToCore e' X' n' =
          coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n) →
        (∀ c, φ (cubicNormalizerAction e X n c) = cubicNormalizerAction e' X' n' (φ c)) ∧
        ∀ q, ψ (MulAut.conjNormal n.val q) = MulAut.conjNormal n'.val (ψ q) := by
  obtain ⟨φ,ψ,hφ,hφz,hψ,hψz,hψc⟩ := exists_cubic_coreGroup_equiv h e X h' e' X' hp hp'
  exact ⟨φ,ψ,hφ,hφz,hψ,hψz,hψc,fun n n' hn =>
    ⟨cubicNativeEquiv_intertwines h e X h' e' X' hp φ hφ n n' hn,
      coreEquiv_intertwines_normalizer h e X h' e' X' hp φ hφ ψ hψ hψc n n' hn⟩⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
