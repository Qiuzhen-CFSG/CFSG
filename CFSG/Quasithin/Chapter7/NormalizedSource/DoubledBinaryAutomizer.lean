module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRank
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The marked binary natural–dual automizer

Conjugation on the component image is faithful because the natural–dual
commutant is trivial. It retains the original inner action and its covariance
on both coordinates. Inner operators preserve the first summand; every outer
operator exchanges the summands. Thus the original seed normalizer detects
the inner subgroup. An actual seed-moving element supplies the other coset,
so an ambient actor containing the component is the full automorphism group.

`NonFFSourceDoubledBinaryAutomizer` applies this to the original chosen orbit
and conjugator. These are the automizer and summand identifications used in
7.6–7.7; the global weak-closure and centralizer-core arguments remain separate.
Source: Aschbacher–Smith H.4.1 and 7.6–7.7, printed pp.380,701–709.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinearThree

private theorem pair_injective : Function.Injective NaturalDual.action := by
  intro g h he
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))

private def pairImageEquiv : Group ≃* actionImage NaturalDual.action :=
  MulEquiv.ofBijective (actionHom NaturalDual.action)
    ⟨fun _ _ he => pair_injective (congrArg (imageRepresentation NaturalDual.action) he),
      NaturalDual.action.asGroupHom.rangeRestrict_surjective⟩

private def normalizerAut : linearNormalizer NaturalDual.action →* MulAut Group :=
  (MulAut.congr pairImageEquiv.symm).toMonoidHom.comp
    (actionImage NaturalDual.action).normalizerMonoidHom

private theorem normalizerAut_covariance (f : linearNormalizer NaturalDual.action)
    (g : Group) (x : NaturalDual.Space) :
    f.val.val (NaturalDual.action g x) =
      NaturalDual.action (normalizerAut f g) (f.val.val x) := by
  have hh : NaturalDual.action.asGroupHom (normalizerAut f g) =
      f.val * NaturalDual.action.asGroupHom g * f.val⁻¹ := by
    have h := pairImageEquiv.apply_symm_apply
      ((actionImage NaturalDual.action).normalizerMonoidHom f (pairImageEquiv g))
    exact congrArg Subtype.val h
  have he : NaturalDual.action.asGroupHom (normalizerAut f g) * f.val =
      f.val * NaturalDual.action.asGroupHom g := by
    rw [hh]
    group
  exact (congrArg (fun z : (Module.End (ZMod 2) NaturalDual.Space)ˣ => z.val x) he).symm

private theorem normalizerAut_injective : Function.Injective normalizerAut := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro f hf
  have h := NaturalDual.centralizer_eq_one
    (LinearMap.GeneralLinearGroup.toLinearEquiv f.val) (fun g x => by
      have he := normalizerAut_covariance f g x
      rw [show normalizerAut f = 1 from hf] at he
      exact he)
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro x
  exact LinearEquiv.congr_fun h x

private theorem normalizerAut_inner (g : Group) :
    normalizerAut ⟨NaturalDual.action.asGroupHom g,
      (actionImage NaturalDual.action).le_normalizer ⟨g,rfl⟩⟩ = MulAut.conj g := by
  apply MulEquiv.ext
  intro k
  apply pairImageEquiv.injective
  apply Subtype.ext
  have h := pairImageEquiv.apply_symm_apply
    ((actionImage NaturalDual.action).normalizerMonoidHom
      ⟨NaturalDual.action.asGroupHom g,
        (actionImage NaturalDual.action).le_normalizer ⟨g,rfl⟩⟩ (pairImageEquiv k))
  change NaturalDual.action.asGroupHom _ = NaturalDual.action.asGroupHom (g * k * g⁻¹)
  rw [map_mul, map_mul, map_inv]
  exact congrArg Subtype.val h

/-- Conjugation on the marked component embeds the full acting group in
Aut(SL₃(2)), retaining its precise action on both coordinates. -/
theorem doubledBinary_marked_automorphisms
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ j v, E (ρ (i j) v) = NaturalDual.action (q j) (E v)) :
    ∃ f : H →* MulAut Group, Function.Injective f ∧
      (∀ j, f (i j) = MulAut.conj (q j)) ∧
      ∀ h g v, E (ρ h (E.symm (NaturalDual.action g (E v)))) =
        NaturalDual.action (f h g) (E (ρ h v)) := by
  let μ := NaturalDual.action
  let γ : Representation (ZMod 2) H NaturalDual.Space := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : γ (i j) = μ (q j) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← he]
    exact hE j v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,Units.ext (hres j).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨j,rfl⟩ := hq p
      exact ⟨i j,⟨j,rfl⟩,Units.ext (hres j)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  refine ⟨normalizerAut.comp j, normalizerAut_injective.comp hj, ?_, ?_⟩
  · intro l
    have hjl : j (i l) = ⟨NaturalDual.action.asGroupHom (q l),
      (actionImage NaturalDual.action).le_normalizer ⟨q l,rfl⟩⟩ := by
      apply Subtype.ext
      exact Units.ext (hres l)
    change normalizerAut (j (i l)) = _
    rw [hjl]
    exact normalizerAut_inner (q l)
  · intro h g v
    have hc := normalizerAut_covariance (j h) g (E v)
    change E (ρ h (E.symm (NaturalDual.action g (E v)))) =
      NaturalDual.action (normalizerAut (j h) g) (γ h (E v)) at hc
    rwa [← he] at hc
/-- In the natural–dual pair, the inner subgroup is exactly the stabilizer
of the natural summand. This also detects the outer action from the seed. -/
theorem doubledBinary_inner_iff_preserves
    (α : MulAut Group) (f : NaturalDual.Space ≃ₗ[ZMod 2] NaturalDual.Space)
    (hf : ∀ g x, f (NaturalDual.action g x) = NaturalDual.action (α g) (f x)) :
    α ∈ MulAut.innerSubgroup Group ↔
      ∀ x : NaturalDual.Space, x.2 = 0 → (f x).2 = 0 := by
  constructor
  · intro hi
    obtain ⟨g,rfl⟩ := NaturalDual.inner_operator α f hf hi
    intro x hx
    change W.dual g x.2 = 0
    rw [hx, map_zero]
  · intro hp
    by_contra hi
    obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
    have hzero : f (v,0) = 0 :=
      Prod.ext ((NaturalDual.outer_swaps α f hf hi).1 v) (hp (v,0) rfl)
    have h := f.map_eq_zero_iff.mp hzero
    exact hv (congrArg Prod.fst h)

/-- An embedded actor containing every inner automorphism and one outer
operator is the full automorphism group, using its actual index two. -/
theorem doubledBinary_onto_of_outer
    {H J : Type*} [_root_.Group H] [_root_.Group J]
    (f : H →* MulAut Group) (i : J →* H) (q : J →* Group)
    (hq : Function.Surjective q) (hi : ∀ j, f (i j) = MulAut.conj (q j))
    (t : H) (ht : f t ∉ MulAut.innerSubgroup Group) : Function.Surjective f := by
  have hinner : MulAut.innerSubgroup Group ≤ f.range := by
    rintro _ ⟨g,rfl⟩
    obtain ⟨j,rfl⟩ := hq g
    exact ⟨i j, hi j⟩
  intro α
  by_cases ha : α ∈ MulAut.innerSubgroup Group
  · exact hinner ha
  · have hprod : α * (f t)⁻¹ ∈ MulAut.innerSubgroup Group :=
      (Subgroup.mul_mem_iff_of_index_two
        Matrix.PSL3Two.Automorphisms.card_outer_sl).mpr
          ⟨fun h => (ha h).elim, fun h => (ht ((MulAut.innerSubgroup Group).inv_mem_iff.mp h)).elim⟩
    obtain ⟨h,hh⟩ := hinner hprod
    exact ⟨h*t, by rw [map_mul, hh, inv_mul_cancel_right]⟩
/-- Inner automorphisms of the component are exactly the ambient
normalizer elements preserving the actual seed subgroup. -/
theorem doubledBinary_inner_iff_seed_normalizer
    {G : Type*} [_root_.Group G] [Finite G]
    (V W : Subgroup G) [IsElementaryAbelian 2 W] (hVW : V ≤ W)
    (E : Additive W ≃ₗ[ZMod 2] NaturalDual.Space)
    (hV : ∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V)
    (f : ChapterE.Automizer W →* MulAut Group)
    (hf : ∀ h g v, E (ChapterE.automizerRepresentation W h
        (E.symm (NaturalDual.action g (E v)))) =
      NaturalDual.action (f h g) (E (ChapterE.automizerRepresentation W h v)))
    (n : normalizer (W : Set G)) :
    f (W.normalizerMonoidHom.rangeRestrict n) ∈ MulAut.innerSubgroup Group ↔
      (n : G) ∈ normalizer (V : Set G) := by
  let a := W.normalizerMonoidHom.rangeRestrict n
  let c : NaturalDual.Space ≃ₗ[ZMod 2] NaturalDual.Space :=
    (E.symm.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((ChapterE.automizerRepresentation W).asGroupHom a))).trans E
  have hc : ∀ g x, c (NaturalDual.action g x) = NaturalDual.action (f a g) (c x) := by
    intro g x
    have hh := hf a g (E.symm x)
    rw [E.apply_symm_apply] at hh
    exact hh
  rw [doubledBinary_inner_iff_preserves _ c hc]
  constructor
  · intro hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      let v : Additive W := Additive.ofMul ⟨x,hVW hx⟩
      have hz := hp (E v) ((hV v).mpr hx)
      change (E (ChapterE.automizerRepresentation W a (E.symm (E v)))).2 = 0 at hz
      rw [E.symm_apply_apply] at hz
      exact (hV _).mp hz
    · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
  · intro hn x hx
    have hv : ((E.symm x).toMul : G) ∈ V :=
      (hV _).mp (by rwa [E.apply_symm_apply])
    change (E (ChapterE.automizerRepresentation W a (E.symm x))).2 = 0
    apply (hV _).mpr
    exact (mem_normalizer_iff.mp hn _).mp hv

end CFSG.Quasithin.Chapter7.NormalizedSource
