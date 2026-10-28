module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural

/-!
# Recognition by full binary linear images

A faithful degree-n binary action containing PSLₙ(2) fills GLₙ(2): the
projective group already has the order of the full binary linear group.
Conjugating the representation by a basis then constructs the group and
module equivalences, as well as proving that the subgroup is the whole group.

A second criterion handles representations whose image is self-normalizing.
Transport an ambient action to the model space. Normality of the subgroup
puts the whole represented ambient group in the model image's normalizer;
faithfulness then gives equality of the original groups.

These are the overgroup steps used in Aschbacher--Smith, G.9.3(11),(13),
printed pp.354,356--357. No irreducible-module classification or model
normalizer calculation is assumed to have been proved here.
-/

open scoped MatrixGroups
open BinaryLinear.OuterCyclic

@[expose] public section

namespace Representation.BinaryLinearRecognition

/-- The natural action of the actual binary projective group, using its
canonical identification with determinant-one matrices. -/
noncomputable def naturalAction (n : ℕ) (hn : 0 < n) :
    Representation (ZMod 2) PSL(n, ZMod 2) (Space n) :=
  (Representation.specialLinearNatural n).comp (projectiveEquivSL hn).toMonoidHom

/-- A faithful binary action in the natural degree has no proper overgroup
of a subgroup isomorphic to the projective special linear group. The
conclusion includes the actual intertwining maps. -/
theorem natural_of_dimension {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (L : Subgroup G) {n : ℕ} (hn : 0 < n)
    (e : L ≃* PSL(n, ZMod 2)) (hd : Module.finrank (ZMod 2) V = n) :
    L = ⊤ ∧ ∃ E : G ≃* PSL(n, ZMod 2), ∃ f : V ≃ₗ[ZMod 2] Space n,
      ∀ g v, f (ρ g v) = naturalAction n hn (E g) (f v) := by
  let f : V ≃ₗ[ZMod 2] Space n := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let σ : Representation (ZMod 2) G (Space n) := f.conjRingEquiv.toMonoidHom.comp ρ
  let θ : G →* LinearGroup n :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n)).toMonoidHom.comp
      σ.asGroupHom
  have hθ : Function.Injective θ := by
    intro x y hxy
    apply hf
    apply f.conjRingEquiv.injective
    exact congrArg LinearEquiv.toLinearMap hxy
  have hc : Nat.card (LinearGroup n) ≤ Nat.card G := by
    rw [← Nat.card_congr (e.trans (projectiveEquivLinear hn)).toEquiv]
    exact Nat.card_le_card_of_injective L.subtype L.subtype_injective
  let : Finite (LinearGroup n) := Finite.of_equiv L
    (e.trans (projectiveEquivLinear hn)).toEquiv
  let E : G ≃* LinearGroup n := MulEquiv.ofBijective θ (hθ.bijective_of_nat_card_le hc)
  have hL : L = ⊤ := by
    apply L.eq_top_of_card_eq
    exact (Nat.card_congr (e.trans (projectiveEquivLinear hn)).toEquiv).trans
      (Nat.card_congr E.toEquiv).symm
  let Esl : G ≃* SL(n, ZMod 2) := E.trans (slEquivLinear n).symm
  let Epsl := Esl.trans (projectiveEquivSL hn).symm
  refine ⟨hL, Epsl, f, ?_⟩
  intro g v
  change f (ρ g v) = Representation.specialLinearNatural n
    ((projectiveEquivSL hn) ((projectiveEquivSL hn).symm (Esl g))) (f v)
  rw [MulEquiv.apply_symm_apply]
  change f (ρ g v) = (slEquivLinear n (Esl g)) (f v)
  change f (ρ g v) = (slEquivLinear n ((slEquivLinear n).symm (E g))) (f v)
  rw [MulEquiv.apply_symm_apply]
  change f (ρ g v) = f (ρ g (f.symm (f v)))
  rw [LinearEquiv.symm_apply_apply]

/-- A represented normal subgroup cannot have a proper faithful
overgroup once the normalizer of its actual model image is itself. The
normalizer equality is an explicit input to this general transport lemma. -/
theorem eq_top_of_self_normalizing_image {G D V W : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (hf : Function.Injective ρ) (L : Subgroup G) [L.Normal]
    (e : L ≃* D) (f : V ≃ₗ[ZMod 2] W)
    (he : ∀ (l : L) v, f (ρ l v) = σ (e l) (f v))
    (hn : Subgroup.normalizer (σ.asGroupHom.range : Set (W →ₗ[ZMod 2] W)ˣ) =
      σ.asGroupHom.range) : L = ⊤ := by
  let τ : Representation (ZMod 2) G W := f.conjRingEquiv.toMonoidHom.comp ρ
  have hτ : Function.Injective τ.asGroupHom := by
    intro x y hxy
    apply hf
    apply f.conjRingEquiv.injective
    exact congrArg Units.val hxy
  have hres (l : L) : τ.asGroupHom l = σ.asGroupHom (e l) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    change f (ρ l (f.symm w)) = σ (e l) w
    rw [he, LinearEquiv.apply_symm_apply]
  have himg : L.map τ.asGroupHom = σ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨e ⟨l, hl⟩, (hres ⟨l, hl⟩).symm⟩
    · rintro ⟨d, rfl⟩
      refine ⟨e.symm d, (e.symm d).property, ?_⟩
      simpa using hres (e.symm d)
  have hnorm := L.le_normalizer_map τ.asGroupHom
  rw [Subgroup.normalizer_eq_top, himg, hn] at hnorm
  apply top_unique
  intro g _
  have hg : τ.asGroupHom g ∈ L.map τ.asGroupHom := by
    rw [himg]
    exact hnorm ⟨g, Subgroup.mem_top g, rfl⟩
  obtain ⟨l, hl, hlg⟩ := hg
  exact hτ hlg ▸ hl

end Representation.BinaryLinearRecognition
