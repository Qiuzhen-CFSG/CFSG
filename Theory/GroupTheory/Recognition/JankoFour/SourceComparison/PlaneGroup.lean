module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerInvolution
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EvenGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.InvolutionGluing
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CubicNormalizer

/-!
# The full original plane-group comparison

The constructed six-cover and extraspecial-core maps glue on O²(H).
The original splitting involution has an action-compatible target lift;
the split-double-cover square calculation proves that lift is involutory.
Equivariance on the core and six-cover extends to their product, so gluing
over the two-element supplement gives H ≃ H′. Both literal restrictions
and the marked central involution are retained, as are the scalar cubic
and full cubic normalizer. Neither a plane isomorphism nor a compatible
normalizer map is an input.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
Aligning the point-plane and plane-line overlaps remains a separate step.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
include h in
/-- Inside the original cubic normalizer, O²(H) cuts out the cubic centralizer. -/
theorem cubicNormalizer_mem_even_iff (n : cubicNormalizerInH e X) :
    n.val ∈ planeEven e ↔ n.val ∈ cubicCentralizerInH e X := by
  rw [planeEven_eq_sup h e X]
  constructor
  · intro hn
    obtain ⟨q,hq,c,hc,hqc⟩ := mem_sup_of_normal_left.mp hn
    have hqN : q ∈ cubicNormalizerInH e X := by
      have he : q = n.val*c⁻¹ := by rw [←hqc]; group
      rw [he]
      exact mul_mem n.property (inv_mem (centralizer_le_normalizer _ hc))
    have hqC : q ∈ cubicCentralizerInH e X :=
      center_le_centralizer _ ((core_inf_cubicNormalizer h e X).le ⟨hq,hqN⟩)
    rw [←hqc]
    exact mul_mem hqC hc
  · exact fun hn => (le_sup_right : cubicCentralizerInH e X ≤
      core z ⊔ cubicCentralizerInH e X) hn

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
include h in
/-- The same splitting element supplements the entire two-residual in H. -/
theorem planeEven_sup_splitting (s : cubicNormalizerInH e X)
    (hs : s*s=1) (hsC : s.val ∉ cubicCentralizerInH e X) :
    planeEven e ⊔ zpowers s.val = ⊤ := by
  rw [planeEven_eq_sup h e X,sup_assoc,
    ←cubicNormalizer_eq_sup h e X s.val s.property hsC (congrArg Subtype.val hs)]
  exact core_sup_cubicNormalizer e h X

private theorem matching_actor_outer
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c)=cubicNativeProjection h e X c)
    (s : cubicNormalizerInH e X) (t : cubicNormalizerInH e' X')
    (hs : s.val ∉ cubicCentralizerInH e X)
    (ht : cubicNormalizerToCore e' X' t =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s)) :
    t.val ∉ cubicCentralizerInH e' X' := by
  intro htC
  let c := φ.symm ⟨t.val,htC⟩
  have hc : (φ c).val=t.val := congrArg Subtype.val (φ.apply_symm_apply _)
  have he : cubicNormalizerToCore e X s = QuotientGroup.mk' (core z) c.val := by
    apply (coreQuotientComparison h e X h' e' X').injective
    rw [←ht,←cubicNativeComparison_core h e X h' e' X' φ hφ,hc]
    rfl
  let cn : cubicNormalizerInH e X := ⟨c.val,centralizer_le_normalizer _ c.property⟩
  have hh : cubicNormalizerToCore e X s = cubicNormalizerToCore e X cn := he
  rcases (cubicNormalizer_fiber h e X s cn).mp hh with he | he
  · exact hs (he ▸ c.property)
  · rw [he] at hs
    exact hs (mul_mem (center_le_centralizer _ planeMarker_central) c.property)

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
include h in
private theorem even_intertwines
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (ψ : core z ≃* core z') (E : planeEven e ≃* planeEven e')
    (hEq : ∀ q : core z, ∀ hq : q.val ∈ planeEven e,
      (E ⟨q.val,hq⟩ : centralizer z') = ψ q)
    (hEc : ∀ c : cubicCentralizerInH e X, ∀ hc : c.val ∈ planeEven e,
      (E ⟨c.val,hc⟩ : centralizer z') = (φ c).val)
    (s : cubicNormalizerInH e X) (t : cubicNormalizerInH e' X')
    (hcs : ∀ c, φ (cubicNormalizerAction e X s c)=cubicNormalizerAction e' X' t (φ c))
    (hqs : ∀ q, ψ (MulAut.conjNormal s.val q)=MulAut.conjNormal t.val (ψ q))
    (n : planeEven e) :
    (E (MulAut.conjNormal s.val n) : centralizer z') = t.val * E n * t.val⁻¹ := by
  have hQ : core z ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_left
  have hC : cubicCentralizerInH e X ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_right
  let Q₀ := (core z).subgroupOf (planeEven e)
  let C₀ := (cubicCentralizerInH e X).subgroupOf (planeEven e)
  let f := ((planeEven e').subtype.comp E.toMonoidHom).comp
    (MulAut.conjNormal s.val : MulAut (planeEven e)).toMonoidHom
  let g := (MulAut.conj t.val).toMonoidHom.comp
    ((planeEven e').subtype.comp E.toMonoidHom)
  have hq : Q₀ ≤ f.eqLocus g := by
    intro q hq
    let x : core z := ⟨q.val,hq⟩
    change (E (MulAut.conjNormal s.val q) : centralizer z') = t.val * E q * t.val⁻¹
    rw [hEq x (hQ x.property)]
    have he := hEq (MulAut.conjNormal s.val x) (hQ (MulAut.conjNormal s.val x).property)
    rw [hqs] at he
    exact he
  have hc : C₀ ≤ f.eqLocus g := by
    intro c hc
    let x : cubicCentralizerInH e X := ⟨c.val,hc⟩
    change (E (MulAut.conjNormal s.val c) : centralizer z') = t.val * E c * t.val⁻¹
    rw [hEc x (hC x.property)]
    have he := hEc (cubicNormalizerAction e X s x) (hC (cubicNormalizerAction e X s x).property)
    rw [hcs] at he
    exact he
  have hgen : Q₀ ⊔ C₀ = ⊤ := by
    rw [←subgroupOf_sup hQ hC,←planeEven_eq_sup h e X,subgroupOf_self]
  exact (show (⊤ : Subgroup (planeEven e)) ≤ f.eqLocus g by
    rw [←hgen]; exact sup_le hq hc) (mem_top n)

/-- The full original plane groups are isomorphic. Both literal core and
six-cover restrictions, the marked center, and the chosen splitting actor
are retained; no plane comparison is an input. -/
theorem exists_plane_equiv
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (hsC : s.val ∉ cubicCentralizerInH e X)
    (s' : cubicNormalizerInH e' X') (hs' : s'*s'=1)
    (hs'C : s'.val ∉ cubicCentralizerInH e' X') :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (ψ : core z ≃* core z') (E : centralizer z ≃* centralizer z')
      (t : cubicNormalizerInH e' X'),
      (∀ c, cubicNativeProjection h' e' X' (φ c)=cubicNativeProjection h e X c) ∧
      E planeMarker = planeMarker ∧
      (∀ q : core z, E q.val = ψ q) ∧
      (∀ c : cubicCentralizerInH e X, E c.val = (φ c).val) ∧
      E s.val=t.val ∧ t*t=1 ∧
      cubicNormalizerToCore e' X' t =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s) := by
  obtain ⟨φ,ψ,hφ,hφz,hψ,hψz,hψc,hn⟩ :=
    exists_cubic_coreGroup_equiv_normalizer h e X h' e' X' hp hp'
  obtain ⟨t,ht⟩ := cubicNormalizerToCore_surjective h' e' X'
    (coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s))
  change cubicNormalizerToCore e' X' t =
    coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s) at ht
  have ht2 : t*t=1 := cubicNormalizer_square_one h' e' X' s' hs' hs'C t (by
    rw [ht,←map_pow,←map_pow,pow_two,hs,map_one,map_one])
  have htC := matching_actor_outer h e X h' e' X' φ hφ s t hsC ht
  obtain ⟨E₀,hEq,hEc⟩ := exists_planeEven_equiv_of_compatible h e X h' e' X' φ hφ hφz ψ hψc
  obtain ⟨E,hEn,hEs⟩ := InvolutionGluing.exists_equiv (planeEven e) (planeEven e') E₀
    s.val t.val (congrArg Subtype.val hs) (congrArg Subtype.val ht2)
    (fun he => hsC ((cubicNormalizer_mem_even_iff h e X s).mp he))
    (fun he => htC ((cubicNormalizer_mem_even_iff h' e' X' t).mp he))
    (planeEven_sup_splitting h e X s hs hsC) (planeEven_sup_splitting h' e' X' t ht2 htC)
    (even_intertwines h e X e' X' φ ψ E₀ hEq hEc s t (hn s t ht).1 (hn s t ht).2)
  have hQ : core z ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_left
  have hC : cubicCentralizerInH e X ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_right
  have hEcore (q : core z) : E q.val = ψ q :=
    (hEn ⟨q.val,hQ q.property⟩).trans (hEq q _)
  have hEcover (c : cubicCentralizerInH e X) : E c.val = (φ c).val :=
    (hEn ⟨c.val,hC c.property⟩).trans (hEc c _)
  have hmarker : (cubicMarker e X).val = planeMarker :=
    Subtype.ext (planeMarker_val (z := z)).symm
  have hmarker' : (cubicMarker e' X').val = planeMarker :=
    Subtype.ext (planeMarker_val (z := z')).symm
  have hEz : E planeMarker = planeMarker := by
    rw [←hmarker,←hmarker']
    exact (hEcover (cubicMarker e X)).trans (congrArg Subtype.val hφz)
  exact ⟨φ,ψ,E,t,hφ,hEz,hEcore,hEcover,hEs,ht2,ht⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))

/-- An instance-free export of the plane comparison, retaining the original
central marker, scalar cubic, core, and full cubic normalizer. -/
theorem exists_plane_equiv_marked
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (hsC : s.val ∉ cubicCentralizerInH e X)
    (s' : cubicNormalizerInH e' X') (hs' : s'*s'=1)
    (hs'C : s'.val ∉ cubicCentralizerInH e' X') :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (E : centralizer z ≃* centralizer z'),
      (∀ c, cubicNativeProjection h' e' X' (φ c)=cubicNativeProjection h e X c) ∧
      E planeMarker = planeMarker ∧
      (∀ c : cubicCentralizerInH e X, E c.val = (φ c).val) ∧
      (core z).map E.toMonoidHom = core z' ∧
      (cubicSylowImage e X).map E.toMonoidHom = cubicSylowImage e' X' ∧
      (cubicNormalizerInH e X).map E.toMonoidHom = cubicNormalizerInH e' X' := by
  let := h.extraspecial
  let := h'.extraspecial
  obtain ⟨φ,ψ,E,t,hφ,hEz,hEq,hEc,hEs,ht2,ht⟩ :=
    exists_plane_equiv h e X h' e' X' hp hp' s hs hsC s' hs' hs'C
  have htC := matching_actor_outer h e X h' e' X' φ hφ s t hsC ht
  have hcmap : (cubicCentralizerInH e X).map E.toMonoidHom = cubicCentralizerInH e' X' := by
    apply le_antisymm
    · rintro g ⟨c,hc,rfl⟩
      change E c ∈ cubicCentralizerInH e' X'
      rw [show E c=(φ ⟨c,hc⟩).val from hEc ⟨c,hc⟩]
      exact (φ ⟨c,hc⟩).property
    · intro c hc
      obtain ⟨d,hd⟩ := φ.surjective ⟨c,hc⟩
      exact ⟨d.val,d.property,(hEc d).trans (congrArg Subtype.val hd)⟩
  have hqmap : (core z).map E.toMonoidHom = core z' := by
    apply le_antisymm
    · rintro g ⟨q,hq,rfl⟩
      change E q ∈ core z'
      rw [show E q=(ψ ⟨q,hq⟩).val from hEq ⟨q,hq⟩]
      exact (ψ ⟨q,hq⟩).property
    · intro q hq
      obtain ⟨d,hd⟩ := ψ.surjective ⟨q,hq⟩
      exact ⟨d.val,d.property,(hEq d).trans (congrArg Subtype.val hd)⟩
  have hcomp : E.toMonoidHom.comp (cubicCentralizerInH e X).subtype =
      (cubicCentralizerInH e' X').subtype.comp φ.toMonoidHom := MonoidHom.ext hEc
  have hamap : (cubicSylowImage e X).map E.toMonoidHom = cubicSylowImage e' X' := by
    have he := congrArg (Subgroup.map (cubicCentralizerInH e' X').subtype)
      (cubicCentralizerEquiv_scalar h e X hp h' e' X' hp' φ)
    rw [map_map,←hcomp,←map_map,map_subgroupOf_eq_of_le (cubicSylowImage_le_centralizer h e X),
      map_subgroupOf_eq_of_le (cubicSylowImage_le_centralizer h' e' X')] at he
    exact he
  have hnmap : (cubicNormalizerInH e X).map E.toMonoidHom = cubicNormalizerInH e' X' := by
    rw [cubicNormalizer_eq_sup h e X s.val s.property hsC (congrArg Subtype.val hs),
      Subgroup.map_sup,hcmap,MonoidHom.map_zpowers]
    change cubicCentralizerInH e' X' ⊔ zpowers (E s.val) = _
    rw [hEs,
      ←cubicNormalizer_eq_sup h' e' X' t.val t.property htC (congrArg Subtype.val ht2)]
  exact ⟨φ,E,hφ,hEz,hEc,hqmap,hamap,hnmap⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
