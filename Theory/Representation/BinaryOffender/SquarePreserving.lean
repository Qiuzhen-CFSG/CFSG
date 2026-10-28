module
public import Theory.Representation.BinaryOffender.SquareNormalizerActors
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.CubicRatio.MarkedNormalizer

/-!
# The factor-preserving normalizer of a faithful square action

The common normalizer of the two literal factor images contains commuting
normal copies of both factors. The original pair representation is its
restriction, so irreducibility and all actor codimensions transport exactly.
An involution of the full normalizer either lies in this common normalizer
or induces an actual twisted exchange. Absorbing the twist in the marking
retains the elementary actor and proves the sharp exchange rank bound.

The even-linear constituent analysis in Chapter D is the consumer.
Source: Aschbacher--Smith D.3.7, printed pp.197--199.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.SquarePreserving
variable {S V : Type*} [Group S] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) (S × S) V)

@[expose] def leftImage : Subgroup (Module.End (ZMod 2) V)ˣ :=
  ((⊤ : Subgroup S).prod ⊥).map σ.asGroupHom
@[expose] def rightImage : Subgroup (Module.End (ZMod 2) V)ˣ :=
  ((⊥ : Subgroup S).prod ⊤).map σ.asGroupHom
@[expose] def group : Subgroup (Module.End (ZMod 2) V)ˣ :=
  normalizer (leftImage σ : Set _) ⊓ normalizer (rightImage σ : Set _)
@[expose] def action : Representation (ZMod 2) (group σ) V :=
  (Units.coeHom _).comp (group σ).subtype
@[expose] def left : Subgroup (group σ) := (leftImage σ).subgroupOf (group σ)
@[expose] def right : Subgroup (group σ) := (rightImage σ).subgroupOf (group σ)

theorem image_mem_group (g : S × S) : σ.asGroupHom g ∈ group σ :=
  ⟨((⊤ : Subgroup S).prod ⊥).le_normalizer_map σ.asGroupHom
      ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩,
    ((⊥ : Subgroup S).prod ⊤).le_normalizer_map σ.asGroupHom
      ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩⟩

@[expose] def pairHom : S × S →* group σ :=
  σ.asGroupHom.codRestrict (group σ) (image_mem_group σ)

theorem leftImage_le : leftImage σ ≤ group σ := by
  rintro _ ⟨g,_,rfl⟩
  exact image_mem_group σ g
theorem rightImage_le : rightImage σ ≤ group σ := by
  rintro _ ⟨g,_,rfl⟩
  exact image_mem_group σ g
instance left_normal : (left σ).Normal :=
  (normal_subgroupOf_iff_le_normalizer (leftImage_le σ)).mpr inf_le_left
instance right_normal : (right σ).Normal :=
  (normal_subgroupOf_iff_le_normalizer (rightImage_le σ)).mpr inf_le_right

theorem action_faithful : Function.Injective (action σ) := fun _ _ h => Subtype.ext (Units.ext h)

theorem pairHom_injective (hf : Function.Injective σ) : Function.Injective (pairHom σ) :=
  fun _ _ h => hf (congrArg (fun x : group σ => x.val.val) h)

theorem pairHom_range : (pairHom σ).range = left σ ⊔ right σ := by
  apply le_antisymm
  · rintro _ ⟨⟨x,y⟩,rfl⟩
    have he : pairHom σ (x,y) = pairHom σ (x,1) * pairHom σ (1,y) := by rw [←map_mul]; simp
    rw [he]
    exact (left σ ⊔ right σ).mul_mem (mem_sup_left ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩)
      (mem_sup_right ⟨(1,y),⟨rfl,mem_top _⟩,rfl⟩)
  · apply sup_le
    · rintro x ⟨g,_,hg⟩
      exact ⟨g,Subtype.ext hg⟩
    · rintro x ⟨g,_,hg⟩
      exact ⟨g,Subtype.ext hg⟩

theorem pair_irreducible (hi : σ.IsIrreducible) (hf : Function.Injective σ) :
    IsIrreducible ((action σ).comp (left σ ⊔ right σ).subtype) := by
  let e : (S × S) ≃* ↥(left σ ⊔ right σ) :=
    (MonoidHom.ofInjective (pairHom_injective σ hf)).trans
      (MulEquiv.subgroupCongr (pairHom_range σ))
  exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mp hi

@[expose] def leftHom : S →* left σ := ((pairHom σ).comp (MonoidHom.inl S S)).codRestrict
  (left σ) (fun x => ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩)
@[expose] def rightHom : S →* right σ := ((pairHom σ).comp (MonoidHom.inr S S)).codRestrict
  (right σ) (fun x => ⟨(1,x),⟨rfl,mem_top _⟩,rfl⟩)

theorem leftHom_bijective (hf : Function.Injective σ) : Function.Bijective (leftHom σ) := by
  constructor
  · intro x y h
    exact congrArg Prod.fst (pairHom_injective σ hf (congrArg Subtype.val h))
  · rintro ⟨z,g,hg,hz⟩
    refine ⟨g.1,Subtype.ext (Subtype.ext ?_)⟩
    change σ.asGroupHom (g.1,1) = z.val
    have he : (g.1,1) = g := Prod.ext rfl (mem_bot.mp hg.2).symm
    exact (congrArg σ.asGroupHom he).trans hz

theorem rightHom_bijective (hf : Function.Injective σ) : Function.Bijective (rightHom σ) := by
  constructor
  · intro x y h
    exact congrArg Prod.snd (pairHom_injective σ hf (congrArg Subtype.val h))
  · rintro ⟨z,g,hg,hz⟩
    refine ⟨g.2,Subtype.ext (Subtype.ext ?_)⟩
    change σ.asGroupHom (1,g.2) = z.val
    have he : (1,g.2) = g := Prod.ext (mem_bot.mp hg.1).symm rfl
    exact (congrArg σ.asGroupHom he).trans hz

@[expose] def leftEquiv (hf : Function.Injective σ) : S ≃* left σ :=
  MulEquiv.ofBijective (leftHom σ) (leftHom_bijective σ hf)
@[expose] def rightEquiv (hf : Function.Injective σ) : S ≃* right σ :=
  MulEquiv.ofBijective (rightHom σ) (rightHom_bijective σ hf)

theorem right_centralizes_left : right σ ≤ centralizer (left σ : Set (group σ)) := by
  rintro k ⟨⟨x,y⟩,hk,hky⟩ l ⟨⟨u,v⟩,hl,hlu⟩
  have hx : x=1 := mem_bot.mp hk.1
  have hv : v=1 := mem_bot.mp hl.2
  subst x v
  apply Subtype.ext
  change l.val * k.val = k.val * l.val
  change σ.asGroupHom (1,y) = k.val at hky
  change σ.asGroupHom (u,1) = l.val at hlu
  rw [←hky,←hlu,←map_mul,←map_mul]
  simp

theorem cubic_le_of_preserving_actor [FiniteDimensional (ZMod 2) V]
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A)
    (hd : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hleft : ∀ a ∈ A, a.val ∈ normalizer (leftImage σ : Set _))
    (hright : ∀ a ∈ A, a.val ∈ normalizer (rightImage σ : Set _)) :
    cubicRatio (action σ) ≤ 2 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let f : A →* group σ := ((linearNormalizer σ).subtype.comp A.subtype).codRestrict
    (group σ) (fun a => ⟨hleft a a.property,hright a a.property⟩)
  have hfi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : group σ => z.val) h))
  let E := f.range
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hE : IsElementaryTwo E := by
    refine ⟨?_,inferInstance⟩
    intro hz
    have hh : ∀ a : A, a = 1 := fun a => hfi
      ((mem_bot.mp (hz ▸ (show f a ∈ E from ⟨a,rfl⟩))).trans f.map_one.symm)
    exact hA.1 (bot_unique (fun a ha => congrArg (fun b : A => b.val) (hh ⟨a,ha⟩)))
  have hcod : fixedCodim (action σ) E = fixedCodim (normalizerRepresentation σ) A := by
    have he : fixedSpace (action σ) E = fixedSpace (normalizerRepresentation σ) A := by
      ext v
      constructor
      · intro hv a
        exact hv ⟨f a,⟨a,rfl⟩⟩
      · rintro hv ⟨_,a,rfl⟩
        exact hv a
    unfold fixedCodim
    rw [he]
  have hrank : rank E = rank A :=
    (congrArg (Nat.log 2) (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv)).symm
  apply (cubicRatio_le_nat_iff _ 2).mpr
  refine ⟨E,hE,?_,?_⟩
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ _ ⟨c,rfl⟩ v
    exact hc a a.property b b.property c c.property v
  · rw [hcod,hrank]
    exact hd

/-- Every involution in the full normalizer either preserves both factor images,
or satisfies a genuine twisted exchange equation on the original module. -/
theorem involution_preserves_or_exchanges [Finite S] [IsQuasisimple S]
    (hZ : center S = ⊥) (hf : Function.Injective σ)
    (a : linearNormalizer σ) (h2 : a^2=1) :
    a.val ∈ group σ ∨ ∃ α : MulAut S, ∀ g v,
      normalizerRepresentation σ a (σ g v) =
        σ (α g.2,α.symm g.1) (normalizerRepresentation σ a v) := by
  let e := PerfectNormalizer.imageEquiv σ hf
  let f : linearNormalizer σ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage σ).normalizerMonoidHom
  have hconj (g : S × S) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  rcases AutomorphismSquare.normal_form hZ (f a) with ⟨α,β,hdiag⟩ | ⟨α,β,hswap⟩
  · have hJL : leftImage σ ≤ actionImage σ := by rintro _ ⟨g,_,rfl⟩; exact ⟨g,rfl⟩
    have hJR : rightImage σ ≤ actionImage σ := by rintro _ ⟨g,_,rfl⟩; exact ⟨g,rfl⟩
    have hmemL (g : S × S) : (e g).val ∈ leftImage σ ↔ g.2=1 := by
      constructor
      · rintro ⟨k,hk,hkg⟩
        exact e.injective (Subtype.ext hkg) ▸ mem_bot.mp hk.2
      · intro hg
        exact ⟨g,⟨mem_top _,hg⟩,rfl⟩
    have hmemR (g : S × S) : (e g).val ∈ rightImage σ ↔ g.1=1 := by
      constructor
      · rintro ⟨k,hk,hkg⟩
        exact e.injective (Subtype.ext hkg) ▸ mem_bot.mp hk.1
      · intro hg
        exact ⟨g,⟨hg,mem_top _⟩,rfl⟩
    left
    constructor
    · apply mem_normalizer_iff.mpr
      intro z
      constructor
      · intro hz
        obtain ⟨g,rfl⟩ := hJL hz
        change (e g).val ∈ leftImage σ at hz
        change a.val * (e g).val * a.val⁻¹ ∈ leftImage σ
        rw [←hconj,hdiag]
        apply (hmemL _).mpr
        change β g.2=1
        rw [(hmemL g).mp hz,β.map_one]
      · intro hz
        have hz' : z ∈ actionImage σ := (mem_normalizer_iff.mp a.property z).mpr (hJL hz)
        obtain ⟨g,rfl⟩ := hz'
        change a.val * (e g).val * a.val⁻¹ ∈ leftImage σ at hz
        rw [←hconj,hdiag] at hz
        exact (hmemL g).mpr (β.injective (((hmemL _).mp hz).trans β.map_one.symm))
    · apply mem_normalizer_iff.mpr
      intro z
      constructor
      · intro hz
        obtain ⟨g,rfl⟩ := hJR hz
        change (e g).val ∈ rightImage σ at hz
        change a.val * (e g).val * a.val⁻¹ ∈ rightImage σ
        rw [←hconj,hdiag]
        apply (hmemR _).mpr
        change α g.1=1
        rw [(hmemR g).mp hz,α.map_one]
      · intro hz
        have hz' : z ∈ actionImage σ := (mem_normalizer_iff.mp a.property z).mpr (hJR hz)
        obtain ⟨g,rfl⟩ := hz'
        change a.val * (e g).val * a.val⁻¹ ∈ rightImage σ at hz
        rw [←hconj,hdiag] at hz
        exact (hmemR g).mpr (α.injective (((hmemR _).mp hz).trans α.map_one.symm))
  · have hfa2 : (f a)^2=1 := by rw [←map_pow,h2,map_one]
    have hba (x : S) : β (α x) = x :=
      congrArg Prod.snd (DFunLike.congr_fun (hswap ▸ hfa2) (1,x))
    have hβ : β = α.symm := by
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := α.surjective x
      exact (hba x).trans (α.symm_apply_apply x).symm
    refine Or.inr ⟨α,?_⟩
    intro g v
    have hh := congrArg (fun x : (Module.End (ZMod 2) V)ˣ => x.val
      (normalizerRepresentation σ a v)) (hconj g).symm
    rw [hswap,hβ] at hh
    change a.val.val (σ g ((a.val⁻¹).val (a.val.val v))) =
      σ (α g.2,α.symm g.1) (a.val.val v) at hh
    have hv : (a.val⁻¹).val (a.val.val v) = v := by
      change ((a.val⁻¹).val * a.val.val) v = v
      rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
      rfl
    rwa [hv] at hh

/-- Absorbing the automorphism twist in the factor marking gives the exchange
rank bound for the original elementary actor, without changing its carrier. -/
theorem twisted_exchange_rank_le [Finite S] [IsQuasisimple S]
    [FiniteDimensional (ZMod 2) V]
    (hZ : center S = ⊥) (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer σ) (ha : a ∈ A) (α : MulAut S)
    (hswap : ∀ g v, normalizerRepresentation σ a (σ g v) =
      σ (α g.2,α.symm g.1) (normalizerRepresentation σ a v)) :
    rank A ≤ primeRank 2 (MulAut S) + 1 := by
  let δ := α.prodCongr (MulEquiv.refl S)
  let τ : Representation (ZMod 2) (S × S) V := σ.comp δ.toMonoidHom
  have himage : actionImage τ = actionImage σ := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨δ g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := δ.surjective g
      exact ⟨g,Units.ext rfl⟩
  have hn : linearNormalizer σ ≤ linearNormalizer τ := by
    unfold linearNormalizer
    rw [himage]
  let j := inclusion hn
  let C := A.map j
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map j
  have hiτ : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective σ).mpr hi
  have hfτ : Function.Injective τ := hf.comp δ.injective
  have hs : ∀ g v, normalizerRepresentation τ (j a) (τ g v) =
      τ (g.2,g.1) (normalizerRepresentation τ (j a) v) := by
    rintro ⟨x,y⟩ v
    have hh := hswap (α x,y) v
    change normalizerRepresentation σ a (σ (α x,y) v) =
      σ (α y,x) (normalizerRepresentation σ a v)
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hb := square_exchange_rank_le hZ τ hiτ hfτ C (j a) (mem_map_of_mem j ha) hs
  rwa [rank_map_injective j (inclusion_injective hn) A] at hb
end Representation.BinaryOffender.SquarePreserving
