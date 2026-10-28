module
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent

/-!
# Large elementary actors in the field-four natural extension

An elementary subgroup containing an outer involution embeds in that
involution's centralizer. The native field-descent calculation bounds this
centralizer's two-rank by four, hence the subgroup has order at most sixteen.
Every larger elementary actor therefore lies in the actual marked Sp4(4)
component. Faithfulness identifies this component inside the original actor.

The literal-kernel application is Sp4Four.SourceComparison.OriginalElementaryMovers.
Source: the outer-centralizer calculation in Aschbacher--Smith B.5.1 and H.7,
pp.100 and388--389, applied to the elementary cross-image case of
Meierfrankenfeld--Stellmacher (1993), (5.5), pp.915--917.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
namespace SymplecticNaturalNormalizer
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G]

/-- An elementary actor of order greater than sixteen in a faithful natural
Sp4(4) extension belongs to the original component. -/
theorem large_elementary_le_component
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (e : B ≃* Sp F) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hlarge : 16 < Nat.card E) : E ≤ B := by
  let f : G →* naturalNormalizer (F := F) :=
    (linearAction ρ).codRestrict _ (operator_mem_naturalNormalizer B (by omega) e ρ hB)
  have hf : Function.Injective f := by
    intro x y h
    apply hfaith
    apply LinearMap.ext
    intro v
    exact congrArg (fun z : naturalNormalizer (F := F) => z.val v) h
  have hinner (x : G) (hx : (f x).val ∈ naturalDerivedImage) : x ∈ B := by
    obtain ⟨g,hg⟩ := (naturalEquiv (by omega : 2 < Nat.card F)).surjective ⟨(f x).val,hx⟩
    have he : ρ (e.symm g : G) = ρ x := by
      apply LinearMap.ext
      intro v
      rw [hB,e.apply_symm_apply]
      exact congrArg (fun z : naturalDerivedImage (F := F) => z.val v) hg
    exact hfaith he ▸ (e.symm g).property
  intro x hx
  by_contra hxn
  have hout : (f x).val ∉ naturalDerivedImage := fun h => hxn (hinner x h)
  have hx1 : f x ≠ 1 := fun h => hxn (hf (h.trans f.map_one.symm) ▸ B.one_mem)
  have hxo : orderOf (f x) = 2 := orderOf_eq_prime
    (by rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian x hx,map_one]) hx1
  have hr := outer_centralizer_rank_le_of_descent (n := 2) hF (by decide)
    (fun he g hg => DiagramAutomorphisms.InvolutionNormalForms.half_frobenius_cocycle_coboundary
      hF (by decide) he g hg) (f x) hxo hout
  let : Finite (naturalNormalizer (F := F)) := Finite.of_injective
    (fun s : naturalNormalizer (F := F) => (s.val : Vector F → Vector F))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  let C := centralizer ({f x} : Set (naturalNormalizer (F := F)))
  let j : E →* C := (f.comp E.subtype).codRestrict C (by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    change f y.val * f x = f x * f y.val
    rw [←map_mul,←map_mul]
    exact congrArg f (setLike_mul_comm y.property hx))
  have hj : Function.Injective j := by
    intro y z h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le C).mp hr j.range inferInstance
  rw [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv] at hc
  norm_num at hc
  omega
end SymplecticNaturalNormalizer
