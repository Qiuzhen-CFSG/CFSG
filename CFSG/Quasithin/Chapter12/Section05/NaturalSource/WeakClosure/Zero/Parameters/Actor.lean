module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Actor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The full exterior automizer on the original chosen module

Local uniqueness puts N_G(V) in N_G(L). Its transported action therefore
normalizes the original exterior image of L. Self-normalization of that
image, together with its faithfulness, identifies the full automizer of V
with SL₅(2), equivariantly in the unchanged marking.

This supplies the full actor needed in Aschbacher--Smith 12.5.6,
printed pp.819--820; the restricted LT action alone does not suffice.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
include s

/-- Local uniqueness controls the full normalizer of the original V. -/
theorem normalizer_le_component_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  D.normal_subgroup_normalizer_le h.toHypothesis1221
    (D.le_sylow.trans le_sup_right) D.ne_bot s.normalizes

/-- The entire ambient automizer has the original exterior-square action. -/
theorem exists_full_automizer_equiv
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let := D.elementary
    ∃ e : Automizer V ≃* Representation.SL5TenDimensional.Group,
      ∀ (x : Automizer V) (v : Additive V),
        s.marking.linearCoordinates (automizerRepresentation V x v) =
          Representation.SL5TenDimensional.exteriorAction 2 (e x)
            (s.marking.linearCoordinates v) := by
  let := D.elementary
  let a := s.marking
  let H := normalizer (V : Set G)
  have hN := s.normalizer_le_component_normalizer h
  let c := a.linearCoordinates
  let φ : H →* MulAut V := V.normalizerMonoidHom
  have hφ (x : H) (v : V) : φ x v =
      ⟨(x : G) * v * (x : G)⁻¹,
        (mem_normalizer_iff.mp x.property v).mp v.property⟩ := by
    apply Subtype.ext
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  let ρ := Representation.elementaryRepresentation (p := 2) φ
  let τ : Representation (ZMod 2) H Representation.SL5ExteriorSquare.V :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  let σ := Representation.SL5TenDimensional.exteriorAction 2
  have hres (l : L) : τ.asGroupHom ⟨l, D.normalizes l.property⟩ =
      σ.asGroupHom (a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    change (a.coordinates (φ ⟨l, D.normalizes l.property⟩
      (a.coordinates.symm (Multiplicative.ofAdd w)))).toAdd = _
    rw [hφ]
    have hh := congrArg Multiplicative.toAdd
      (a.equivariant l (a.coordinates.symm (Multiplicative.ofAdd w)))
    simpa only [MulEquiv.apply_symm_apply, Representation.asGroupHom_apply, toAdd_ofAdd] using hh
  have himg : (L.subgroupOf H).map τ.asGroupHom = σ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩),
        (hres ⟨l, hl⟩).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨q, rfl⟩ := a.quotientEquiv.surjective g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact ⟨⟨l, D.normalizes l.property⟩, l.property, hres l⟩
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hN
  have hnorm := (L.subgroupOf H).le_normalizer_map τ.asGroupHom
  rw [normalizer_eq_top, himg, Representation.SL5TenDimensional.ExteriorNormalizer.normalizer_two]
    at hnorm
  have hmem (h : H) : τ.asGroupHom h ∈ σ.asGroupHom.range :=
    hnorm ⟨h, mem_top h, rfl⟩

  let δ : Representation (ZMod 2) (Automizer V) Representation.SL5ExteriorSquare.V :=
    c.conjRingEquiv.toMonoidHom.comp (automizerRepresentation V)
  have hδ (x : Automizer V) : δ.asGroupHom x ∈ σ.asGroupHom.range := by
    obtain ⟨n, hn⟩ := x.property
    have he : δ.asGroupHom x = τ.asGroupHom n := by
      apply Units.ext
      apply LinearMap.ext
      intro w
      change c (automizerRepresentation V x (c.symm w)) = c (ρ n (c.symm w))
      congr 1
      change Additive.ofMul (x.val (c.symm w).toMul) = _
      rw [← hn]
      rfl
    rw [he]
    exact hmem n
  let β : Automizer V →* σ.asGroupHom.range := δ.asGroupHom.codRestrict _ hδ
  let e₀ := MonoidHom.ofInjective
    (Representation.SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
  let α := e₀.symm.toMonoidHom.comp β
  have he (x : Automizer V) : σ.asGroupHom (α x) = δ.asGroupHom x :=
    congrArg Subtype.val (e₀.apply_symm_apply (β x))
  have hi : Function.Injective α := by
    intro x y hxy
    apply automizerRepresentation_injective V
    have hh := (he x).symm.trans ((congrArg σ.asGroupHom hxy).trans (he y))
    have hh' := congrArg Units.val hh
    exact c.conjRingEquiv.injective hh'
  have hs : Function.Surjective α := by
    intro g
    obtain ⟨q, rfl⟩ := a.quotientEquiv.surjective g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    refine ⟨V.normalizerMonoidHom.rangeRestrict ⟨l, D.normalizes l.property⟩, ?_⟩
    apply Representation.SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0
    exact (he _).trans (hres l)
  refine ⟨MulEquiv.ofBijective α ⟨hi, hs⟩, ?_⟩
  intro x v
  have hh := LinearMap.congr_fun (congrArg Units.val (he x)) (c v)
  change σ (α x) (c v) = c (automizerRepresentation V x (c.symm (c v))) at hh
  change c (automizerRepresentation V x v) = σ (α x) (c v)
  simpa only [LinearEquiv.symm_apply_apply] using hh.symm

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
