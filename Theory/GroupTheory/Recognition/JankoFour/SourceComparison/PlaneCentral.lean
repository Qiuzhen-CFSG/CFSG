module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerCore

/-!
# Comparing the full plane groups modulo their marked centers

The conjugation action of H on its original extraspecial core Q has kernel
Z(H). The constructed core isomorphism transports the entire action image:
write an actor as qn with q in Q and n in the cubic normalizer, then use the
full normalizer equivariance. Faithful descent constructs H/Z(H) ≃ H'/Z(H').
The original core and six-cover restrictions, the full normalizer image,
and an equality criterion in terms of actual core actions are retained.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
The original central extension has not been identified here. Its involutory
normalizer lift and the subsequent full-H comparison remain necessary.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

include h in
/-- The full action on Q has kernel precisely the marked central involution. -/
theorem planeCoreAction_ker :
    (MulAut.conjNormal : centralizer z →* MulAut (core z)).ker = center (centralizer z) := by
  ext g
  constructor
  · intro hg
    have hgQ : g ∈ core z := by
      rw [←coreAction_kernel h]
      change quotientAut (center (core z)) (MulAut.conjNormal g) = 1
      rw [show MulAut.conjNormal g = 1 from hg,map_one]
    have hgZ : (⟨g,hgQ⟩ : core z) ∈ center (core z) := by
      apply mem_center_iff.mpr
      intro q
      apply Subtype.ext
      have he := congrArg (fun α : MulAut (core z) => (α q).val) (show MulAut.conjNormal g = 1 from hg)
      change g*q.val*g⁻¹=q.val at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [←core_center_eq_centralizer_center h]
    exact mem_map_of_mem (core z).subtype hgZ
  · intro hg
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    change g*q.val*g⁻¹=q.val
    rw [←mem_center_iff.mp hg q.val,mul_inv_cancel_right]

/-- The faithful central quotient action retains the literal quotient map. -/
noncomputable def planeCentralActionEquiv :
    (centralizer z ⧸ center (centralizer z)) ≃*
      (MulAut.conjNormal : centralizer z →* MulAut (core z)).range :=
  (QuotientGroup.quotientMulEquivOfEq (planeCoreAction_ker h).symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conjNormal : centralizer z →* MulAut (core z)))

theorem planeCentralActionEquiv_mk (g : centralizer z) :
    (planeCentralActionEquiv h (QuotientGroup.mk' (center (centralizer z)) g)).val =
      MulAut.conjNormal g := rfl

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

private theorem normalizer_actor_exists (n : cubicNormalizerInH e X) :
    ∃ n' : cubicNormalizerInH e' X', cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n) :=
  cubicNormalizerToCore_surjective h' e' X' _

private theorem source_normalizer_actor_exists (n' : cubicNormalizerInH e' X') :
    ∃ n : cubicNormalizerInH e X, cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n) := by
  obtain ⟨n,hn⟩ := cubicNormalizerToCore_surjective h e X
    ((coreQuotientComparison h e X h' e' X').symm (cubicNormalizerToCore e' X' n'))
  change cubicNormalizerToCore e X n =
    (coreQuotientComparison h e X h' e' X').symm (cubicNormalizerToCore e' X' n') at hn
  exact ⟨n,by rw [hn,MulEquiv.apply_symm_apply]⟩

private theorem compare_central
    (ψ : core z ≃* core z')
    (hn : ∀ (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X'),
      cubicNormalizerToCore e' X' n' =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n) →
      ∀ q, ψ (MulAut.conjNormal n.val q) = MulAut.conjNormal n'.val (ψ q)) :
    ∃ E : (centralizer z ⧸ center (centralizer z)) ≃*
        (centralizer z' ⧸ center (centralizer z')),
      ∀ (g : centralizer z) (g' : centralizer z'),
        E (QuotientGroup.mk' (center (centralizer z)) g) =
          QuotientGroup.mk' (center (centralizer z')) g' ↔
        MulAut.congr ψ (MulAut.conjNormal g) = MulAut.conjNormal g' := by
  let ρ : centralizer z →* MulAut (core z) := MulAut.conjNormal
  let σ : centralizer z' →* MulAut (core z') := MulAut.conjNormal
  have hn' (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X')
      (he : cubicNormalizerToCore e' X' n' =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n)) :
      MulAut.congr ψ (ρ n.val) = σ n'.val := by
    apply MulEquiv.ext
    intro q
    obtain ⟨q,rfl⟩ := ψ.surjective q
    simpa only [ρ,σ,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      using hn n n' he q
  have hq (q : core z) : MulAut.congr ψ (ρ q.val) = σ (ψ q).val := by
    simpa only [ρ,σ,MulAut.conjNormal_val] using MulAut.congr_conj ψ q
  let f₀ : centralizer z →* MulAut (core z') := (MulAut.congr ψ).toMonoidHom.comp ρ
  have hmem (g : centralizer z) : f₀ g ∈ σ.range := by
    obtain ⟨q,n,rfl⟩ := exists_core_mul_cubicNormalizer e h X g
    obtain ⟨n',he⟩ := normalizer_actor_exists h e X h' e' X' n
    refine ⟨(ψ q).val*n'.val,?_⟩
    change σ ((ψ q).val*n'.val) = MulAut.congr ψ (ρ (q.val*n.val))
    rw [map_mul,map_mul,map_mul,hq,hn' n n' he]
  let f : centralizer z →* σ.range := f₀.codRestrict σ.range hmem
  have hsurj : Function.Surjective f := by
    rintro ⟨_,g',rfl⟩
    obtain ⟨q',n',rfl⟩ := exists_core_mul_cubicNormalizer e' h' X' g'
    obtain ⟨n,he⟩ := source_normalizer_actor_exists h e X h' e' X' n'
    refine ⟨(ψ.symm q').val*n.val,Subtype.ext ?_⟩
    change MulAut.congr ψ (ρ ((ψ.symm q').val*n.val)) = σ (q'.val*n'.val)
    rw [map_mul,map_mul,map_mul,hq,hn' n n' he,ψ.apply_symm_apply]
  have hfker : f.ker = center (centralizer z) := by
    rw [MonoidHom.ker_codRestrict]
    change ((MulAut.congr ψ).toMonoidHom.comp ρ).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr ψ).injective]
    exact planeCoreAction_ker h
  let E₀ := (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  let E := E₀.trans (planeCentralActionEquiv h').symm
  have hE (g : centralizer z) :
      (planeCentralActionEquiv h' (E (QuotientGroup.mk' (center (centralizer z)) g))).val =
        MulAut.congr ψ (ρ g) := by
    change (planeCentralActionEquiv h' ((planeCentralActionEquiv h').symm (E₀ _))).val = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨E,fun g g' => ?_⟩
  rw [←(planeCentralActionEquiv h').injective.eq_iff,Subtype.ext_iff,hE,planeCentralActionEquiv_mk]

/-- The precise conclusion of the plane central-quotient comparison. This
proposition names the constructed maps and their literal restrictions; it is
proved below from original perfectness, not supplied as an input. -/
def PlaneCentralComparison : Prop :=
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (ψ : core z ≃* core z')
      (E : (centralizer z ⧸ center (centralizer z)) ≃*
        (centralizer z' ⧸ center (centralizer z'))),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      ψ (coreMarker h) = coreMarker h' ∧
      (∀ q : core z,
        E (QuotientGroup.mk' (center (centralizer z)) q.val) =
          QuotientGroup.mk' (center (centralizer z')) (ψ q).val) ∧
      (∀ c : cubicCentralizerInH e X,
        E (QuotientGroup.mk' (center (centralizer z)) c.val) =
          QuotientGroup.mk' (center (centralizer z')) (φ c).val) ∧
      ((cubicNormalizerInH e X).map (QuotientGroup.mk' (center (centralizer z)))).map
          E.toMonoidHom =
        (cubicNormalizerInH e' X').map (QuotientGroup.mk' (center (centralizer z'))) ∧
      ∀ (g : centralizer z) (g' : centralizer z'),
        E (QuotientGroup.mk' (center (centralizer z)) g) =
          QuotientGroup.mk' (center (centralizer z')) g' ↔
        ∀ q : core z, ψ (MulAut.conjNormal g q) = MulAut.conjNormal g' (ψ q)

/-- Construct the full plane central quotient comparison, including the core,
cover and cubic-normalizer restrictions in their original embeddings. -/
theorem exists_planeCentral_equiv
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X')) :
    PlaneCentralComparison h e X h' e' X' := by
  obtain ⟨φ,ψ,hφ,hφz,hψ,hψz,hψc,hn⟩ :=
    exists_cubic_coreGroup_equiv_normalizer h e X h' e' X' hp hp'
  obtain ⟨E,hE⟩ := compare_central h e X h' e' X' ψ (fun n n' he => (hn n n' he).2)
  have hEn (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X')
      (he : cubicNormalizerToCore e' X' n' =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n)) :
      E (QuotientGroup.mk' (center (centralizer z)) n.val) =
        QuotientGroup.mk' (center (centralizer z')) n'.val := by
    apply (hE _ _).mpr
    apply MulEquiv.ext
    intro q
    obtain ⟨q,rfl⟩ := ψ.surjective q
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      using (hn n n' he).2 q
  refine ⟨φ,ψ,E,hφ,hφz,hψz,?_,?_,?_,?_⟩
  · intro q
    apply (hE _ _).mpr
    simpa only [MulAut.conjNormal_val] using MulAut.congr_conj ψ q
  · intro c
    apply (hE _ _).mpr
    apply MulEquiv.ext
    intro q
    obtain ⟨q,rfl⟩ := ψ.surjective q
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      using hψc c q
  · apply le_antisymm
    · rintro _ ⟨_,⟨n,hnm,rfl⟩,rfl⟩
      obtain ⟨n',he⟩ := normalizer_actor_exists h e X h' e' X' ⟨n,hnm⟩
      exact ⟨n'.val,n'.property,(hEn ⟨n,hnm⟩ n' he).symm⟩
    · rintro _ ⟨n',hnm,rfl⟩
      obtain ⟨n,he⟩ := source_normalizer_actor_exists h e X h' e' X' ⟨n',hnm⟩
      exact ⟨QuotientGroup.mk' (center (centralizer z)) n.val,
        mem_map_of_mem _ n.property,hEn n ⟨n',hnm⟩ he⟩

  · intro g g'
    constructor
    · intro he q
      have hh := MulEquiv.congr_fun ((hE g g').mp he) (ψ q)
      simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh
    · intro he
      apply (hE g g').mpr
      apply MulEquiv.ext
      intro q
      obtain ⟨q,rfl⟩ := ψ.surjective q
      simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using he q

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
include h h' in
/-- Instance-free existence interface for the original chapter application. -/
theorem nonempty_planeCentral_equiv
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X')) :
    Nonempty ((centralizer z ⧸ center (centralizer z)) ≃*
      (centralizer z' ⧸ center (centralizer z'))) := by
  let := h.extraspecial
  let := h'.extraspecial
  obtain ⟨φ,ψ,E,_⟩ := exists_planeCentral_equiv h e X h' e' X' hp hp'
  exact ⟨E⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
