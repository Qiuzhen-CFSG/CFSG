module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportStrong
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.Normalizer
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitFixedSpace

/-!
# Natural support seeds before quotienting by fixed vectors

The marked support section is already natural SL₃ in odd binary degree.
Here the literal seed projection is shown to have trivial kernel. In larger
fields its kernel dimension is bounded by the vanishing dual first
cohomology. In degree one a nonzero kernel would give the four-dimensional
central cover; B.4.8 excludes a strong offender even in its full linear
normalizer. Normality of the original support puts the actual seed actor
inside that normalizer, with its original operators unchanged.

Thus the seed itself is natural and irreducible. D.3.4(4) propagates its
zero fixed space to the original commuting-component orbit. The literal
Chapter12 application is `SeedAlternativesMovedExhaustionSupportFixed`.
The subsequent movement, multiplicity, Suzuki exclusions, U = W and
Source325 assembly remain with this owner.
Source: Aschbacher--Smith D.3.17, p.203; B.4.8, p.91; I.1.6, p.408;
refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

private theorem strong_map {G D V W : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (α : Representation (ZMod 2) G V) (β : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (α g v) = β (f g) (e v))
    (hs : IsStrongFFModule α) : IsStrongFFModule β := by
  obtain ⟨A,hA,hlt⟩ := hs
  have h := (show IsOffender α A from ⟨hA,hlt.le⟩).map_equivariant α β f hf e he
  refine ⟨A.map f,h.1,?_⟩
  rw [←fixedCodim_map_equivariant α β f e he,rank_map_injective f hf]
  exact hlt

private theorem binary_cover_injective_of_strong_normalizer
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (p : σ.IntertwiningMap BinaryLinearThree.W) (hp : IsCover p)
    (hs : IsStrongFFModule (normalizerRepresentation σ)) : Function.Injective p := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  have hlo : 0 < Module.finrank (ZMod 2) p.toLinearMap.ker :=
    Nat.pos_of_ne_zero (fun he => hn (Submodule.finrank_eq_zero.mp he))
  have hle := finrank_ker_le_H1_of_cover p hp
  rw [SLThreeCentralExtension.finrank_H1_dual] at hle
  have hk : Module.finrank (ZMod 2) p.toLinearMap.ker = 1 := by omega
  have hd := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1,finrank_top,Module.finrank_fin_fun,hk] at hd
  exact SLThreeCentralExtension.cover_normalizer_not_strong σ p hp (by omega) hs

private theorem natural_cover_injective_of_strong_normalizer
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (F : BinaryField) (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) V)
    (p : σ.IntertwiningMap (linearNatural F 3)) (hp : IsCover p)
    (hs : IsStrongFFModule (normalizerRepresentation σ)) : Function.Injective p := by
  by_cases hF : 1 < F.degree
  · let := SourceCompletion.linearThree_natural_dual_H1 (linearNatural F 3) F hF
      ⟨⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩⟩
    have hk := finrank_ker_le_H1_of_cover p hp
    rw [show Module.finrank (ZMod 2) (H1 (linearNatural F 3).dual) = 0 from
      Module.finrank_zero_of_subsingleton] at hk
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hk))
  · have hF1 : F.degree = 1 := by have hh := F.degree_pos; omega
    let a := ExtensionConsequences.degreeOneNaturalEquiv F hF1 3
    let τ : Representation (ZMod 2) BinaryLinearThree.Group V := σ.comp a.groupEquiv.symm.toMonoidHom
    let q : τ.IntertwiningMap BinaryLinearThree.W :=
      (a.linearEquiv.toLinearMap.comp p.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g v
        have hh := a.intertwines (a.groupEquiv.symm g) (p v)
        rw [a.groupEquiv.apply_symm_apply] at hh
        exact (congrArg a.linearEquiv (Representation.IntertwiningMap.isIntertwining σ (linearNatural F 3) p _ v)).trans hh)
    have hq : IsCover q := by
      refine ⟨a.linearEquiv.surjective.comp hp.1,?_,?_⟩
      · intro v hv g
        have hv' : p v = 0 := a.linearEquiv.injective (hv.trans a.linearEquiv.map_zero.symm)
        exact hp.2.1 hv' (a.groupEquiv.symm g)
      · apply top_unique
        intro v _
        have hv : v ∈ Coinvariants.ker σ := hp.2.2.symm ▸ Submodule.mem_top
        exact (show Coinvariants.ker σ ≤ Coinvariants.ker τ by
          apply Submodule.span_le.mpr
          rintro _ ⟨⟨g,w⟩,rfl⟩
          have hh := Coinvariants.sub_mem_ker (ρ := τ) (a.groupEquiv g) w
          change σ (a.groupEquiv.symm (a.groupEquiv g)) w - w ∈ Coinvariants.ker τ at hh
          rw [a.groupEquiv.symm_apply_apply] at hh
          exact hh) hv
    have him : actionImage τ = actionImage σ := by
      ext u
      constructor
      · rintro ⟨g,rfl⟩; exact ⟨a.groupEquiv.symm g,by apply Units.ext; rfl⟩
      · rintro ⟨g,rfl⟩; exact ⟨a.groupEquiv g,by
          apply Units.ext
          change σ (a.groupEquiv.symm (a.groupEquiv g)) = σ g
          rw [a.groupEquiv.symm_apply_apply]⟩
    have hs' : IsStrongFFModule (normalizerRepresentation τ) := by
      unfold normalizerRepresentation linearNormalizer
      rw [him]
      exact hs
    have hi := binary_cover_injective_of_strong_normalizer τ q hq hs'
    exact fun v w hvw => hi (congrArg a.linearEquiv hvw)

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem seed_strong_normalizer
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) [X.Normal]
    (R : Submodule (ZMod 2) E) (hR : X ≤ subspaceStabilizer ρ R)
    {G : Type*} [Group G] (e : G ≃* X)
    (hs : IsStrongFFModule (subspaceImageRepresentation ρ R)) :
    IsStrongFFModule (normalizerRepresentation
      ((invariantSubspace ρ X R hR).toRepresentation.comp e.toMonoidHom)) := by
  let σ : Representation (ZMod 2) G R :=
    (invariantSubspace ρ X R hR).toRepresentation.comp e.toMonoidHom
  let α := stabilizerRepresentation ρ R
  let X₀ := X.subgroupOf (subspaceStabilizer ρ R)
  have him : actionImage σ = actionImage (α.comp X₀.subtype) := by
    ext u
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨⟨⟨e g,hR (e g).property⟩,(e g).property⟩,by apply Units.ext; rfl⟩
    · rintro ⟨x,rfl⟩
      refine ⟨e.symm ⟨x.val,x.property⟩,?_⟩
      apply Units.ext
      ext v
      change ρ (e (e.symm ⟨x.val,x.property⟩)) v.val = ρ x.val.val v.val
      rw [e.apply_symm_apply]
  have hle : subspaceActionImage ρ R ≤ linearNormalizer σ := by
    change actionImage α ≤ normalizer ((actionImage σ : Subgroup (Module.End (ZMod 2) R)ˣ) : Set _)
    rw [him]
    exact actionImage_le_linearNormalizer α X₀
  exact strong_map (subspaceImageRepresentation ρ R) (normalizerRepresentation σ)
    (inclusion hle) (inclusion_injective _) (LinearEquiv.refl _ _) (fun _ _ => rfl) hs

omit [Finite H] in
/-- Strong offending removes the central fixed kernel of the marked support seed. -/
theorem support_natural_seed_fixed_eq_bot
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) [X.Normal]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlus ρ X R)
    (F : BinaryField)
    (a : ActionEquiv (centralQuotientRepresentation ρ X R hR.choose) (linearNatural F 3))
    (hs : IsStrongFFModule (subspaceImageRepresentation ρ R)) :
    R ⊓ fixedSpace ρ X = ⊥ := by
  let σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) R :=
    (invariantSubspace ρ X R hR.choose).toRepresentation.comp a.groupEquiv.symm.toMonoidHom
  let q := ((fixedSpace ρ X).comap R.subtype).mkQ
  let p : σ.IntertwiningMap (linearNatural F 3) :=
    (a.linearEquiv.toLinearMap.comp q).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      have he := a.intertwines (a.groupEquiv.symm g) (q v)
      rw [a.groupEquiv.apply_symm_apply] at he
      exact he)
  have hp : IsCover p := by
    refine ⟨a.linearEquiv.surjective.comp (Submodule.mkQ_surjective _),?_,?_⟩
    · intro v hv g
      have hv' : q v = 0 := a.linearEquiv.injective (hv.trans a.linearEquiv.map_zero.symm)
      have hf := (Submodule.Quotient.mk_eq_zero _).mp hv'
      exact Subtype.ext (hf (a.groupEquiv.symm g))
    · have hm : R ≤ (Coinvariants.ker σ).map R.subtype := by
        conv_lhs => rw [←hR.choose_spec.1]
        apply Submodule.span_le.mpr
        rintro _ ⟨x,hx,v,hv,rfl⟩
        refine ⟨σ (a.groupEquiv ⟨x,hx⟩) ⟨v,hv⟩ - ⟨v,hv⟩,
          Coinvariants.sub_mem_ker _ _,?_⟩
        change ρ (a.groupEquiv.symm (a.groupEquiv ⟨x,hx⟩)) v - v = ρ x v-v
        rw [a.groupEquiv.symm_apply_apply]
      apply top_unique
      intro v _
      obtain ⟨w,hw,he⟩ := hm v.property
      exact (show w = v from Subtype.ext he) ▸ hw
  have hi := natural_cover_injective_of_strong_normalizer F σ p hp
    (seed_strong_normalizer ρ X R hR.choose a.groupEquiv.symm hs)
  apply bot_unique
  rintro v ⟨hv,hf⟩
  have hz : p ⟨v,hv⟩ = 0 := by
    change a.linearEquiv (q ⟨v,hv⟩) = 0
    rw [show q ⟨v,hv⟩ = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hf,map_zero]
  exact congrArg Subtype.val (hi (hz.trans p.map_zero.symm))

omit [FiniteDimensional (ZMod 2) E] in
/-- The quotient marking is transported from the actual support orbit to its
stable seed, retaining the original support as actor. -/
theorem support_seed_marked_quotient
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [X.Normal] [IsQuasisimple X]
    (hcore : pCore 2 H = ⊥) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (he : orbitSpan ρ P R = R)
    (hm : SupportMarkedLinearThreeSection ρ hR) :
    ∃ F : BinaryField, Odd F.degree ∧
      Nonempty (ActionEquiv (centralQuotientRepresentation ρ X R hR.invariant)
        (linearNatural F 3)) := by
  obtain ⟨_,F,ho,a,_,_⟩ := hm
  obtain ⟨_,e,_,hact⟩ := support_section_marked_linearThree ρ X P hcore R hR F ho a
  have hh : Nonempty (ActionEquiv
      (centralQuotientRepresentation ρ X (orbitSpan ρ P R)
        (orbitSpan_component_invariant ρ hR.normalizes hR.isIrrPlus))
      (linearNatural F 3)) := ⟨⟨e,a.linearEquiv,hact⟩⟩
  refine ⟨F,ho,?_⟩
  have transport (Y : Submodule (ZMod 2) E) (hY : X ≤ subspaceStabilizer ρ Y)
      (hYR : Y = R) (ha : Nonempty (ActionEquiv (centralQuotientRepresentation ρ X Y hY)
        (linearNatural F 3))) :
      Nonempty (ActionEquiv (centralQuotientRepresentation ρ X R hR.invariant)
        (linearNatural F 3)) := by
    subst Y
    exact ha
  exact transport _ _ he hh

/-- The original support seed, not just its quotient by fixed vectors, is a
marked odd-degree natural SL₃ module. -/
theorem support_seed_marked_natural
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [X.Normal] [IsQuasisimple X]
    (hcore : pCore 2 H = ⊥) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (he : orbitSpan ρ P R = R)
    (hs : SupportStrongSection ρ hR) (hm : SupportMarkedLinearThreeSection ρ hR) :
    R ⊓ fixedSpace ρ X = ⊥ ∧
      IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation ∧
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
          (linearNatural F 3)) := by
  obtain ⟨F,ho,⟨a⟩⟩ := support_seed_marked_quotient ρ X P hcore R hR he hm
  obtain ⟨D,_,_,hD,_⟩ := hs
  have hz := support_natural_seed_fixed_eq_bot ρ X R hR.isIrrPlus F a ⟨_,hD⟩
  let q := centralSectionEquiv ρ X R (disjoint_iff.mpr hz)
  let b : ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation
      (linearNatural F 3) := ⟨a.groupEquiv,q.trans a.linearEquiv,fun x v =>
        (congrArg a.linearEquiv (centralSectionEquiv_equivariant ρ X R
          (disjoint_iff.mpr hz) hR.invariant x v)).trans (a.intertwines x (q v))⟩
  exact ⟨hz,ExtensionConsequences.irreducible_of_equiv b
    (ExtensionConsequences.linearNatural_irreducible F (by decide)),F,ho,⟨b⟩⟩

omit [FiniteDimensional (ZMod 2) E] in
/-- Removing the seed fixed space removes it from every orbit under the
original ambient actor, including the commuting-component orbit used in D.3.18. -/
theorem support_seed_orbit_fixed_eq_bot
    (ρ : Representation (ZMod 2) H E) (X K : Subgroup H) [X.Normal]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlus ρ X R)
    (hz : R ⊓ fixedSpace ρ X = ⊥) :
    orbitSpan ρ K R ⊓ fixedSpace ρ X = ⊥ := by
  have hh := orbitSpan_inf_fixedSpace ρ X hR
  rw [hz] at hh
  have hb : orbitSpan ρ ⊤ (⊥ : Submodule (ZMod 2) E) = ⊥ := by
    exact le_antisymm (iSup_le fun _ => by rw [Submodule.map_bot]) bot_le
  rw [hb] at hh
  apply bot_unique
  apply le_trans (inf_le_inf_right _ ?_) hh.le
  exact iSup_le fun k => le_iSup (fun g : (⊤ : Subgroup H) => R.map (ρ g))
    ⟨k,mem_top _⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
