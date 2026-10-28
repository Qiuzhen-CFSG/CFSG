module
public import Theory.Representation.OrthogonalFourPlusMatrix.IndependentFactors
public import Theory.Representation.BinaryOffender.PairActorBounds
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActorsGeneral
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Models

/-!
# Elementary actors on the general binary determinant module

Above rank n+1 an elementary actor preserves both SL₂ factors. Its two
nontrivial component kernels give independently supported inner involutions,
whose common fixed space has dimension at most n. Consequently its fixed
codimension is at least 3n, while its rank is at most 2n. Together with the
small-actor and minimum-displacement estimates, this proves the H.1.1 gap
rank(A) + n ≤ codim C(A) + 1 on the entire binary normalizer.

The final theorem transports these bounds through the actual marked tensor
coordinates. The original central Hall application uses the seed image and
retains the pointwise seed kernel in the full-module codimension budget.
Source: Aschbacher--Smith H.1.1(2), 9.2.1, printed pp.378,730,
refs/quasithin.pdf.
-/

public noncomputable section
open Matrix Module Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative MatrixGroups
namespace ClassicalOrthogonal.FourPlusMatrix.GeneralActors
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] in
private theorem binaryAction_injective : Function.Injective (binaryAction (F := F)) := by
  intro g h he
  apply matrixHom_injective
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun he v

omit [Finite F] in
private theorem supported_left
    (a : SquarePreserving.group (binaryAction (F := F))) (ha2 : a*a=1)
    (hc : a ∈ centralizer ((SquarePreserving.right (binaryAction (F := F))) : Set (SquarePreserving.group (binaryAction (F := F))))) :
    ∃ b : SL(2,F), b*b=1 ∧ (a ≠ 1 → b ≠ 1) ∧ a.val = (binaryAction (F := F)).asGroupHom (b,1) := by
  let t := LinearMap.GeneralLinearGroup.toLinearEquiv a.val
  obtain ⟨b,hb⟩ := right_centralizing_involution t
    (fun v => congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val v) ha2)
    (by
      intro g v
      have hh := hc (SquarePreserving.pairHom (binaryAction (F := F)) (1,g))
        (show SquarePreserving.pairHom (binaryAction (F := F)) (1,g) ∈ SquarePreserving.right (binaryAction (F := F)) from
          ⟨(1,g),⟨rfl,mem_top _⟩,rfl⟩)
      exact (congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val v) hh).symm)
  have he : a.val = (binaryAction (F := F)).asGroupHom (b,1) := Units.ext (LinearMap.ext hb)
  have hb2 : b*b=1 := by
    have hh := congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val) ha2
    change a.val.val * a.val.val = 1 at hh
    rw [he] at hh
    change binaryAction (F := F) _ * binaryAction (F := F) _ = 1 at hh
    rw [←map_mul,←map_one (binaryAction (F := F))] at hh
    exact congrArg Prod.fst (binaryAction_injective hh)
  refine ⟨b,hb2,?_,he⟩
  intro hane hb1
  apply hane
  apply Subtype.ext
  rw [he,hb1]
  exact (binaryAction (F := F)).asGroupHom.map_one

omit [Finite F] in
private theorem supported_right
    (a : SquarePreserving.group (binaryAction (F := F))) (ha2 : a*a=1)
    (hc : a ∈ centralizer ((SquarePreserving.left (binaryAction (F := F))) : Set (SquarePreserving.group (binaryAction (F := F))))) :
    ∃ b : SL(2,F), b*b=1 ∧ (a ≠ 1 → b ≠ 1) ∧ a.val = (binaryAction (F := F)).asGroupHom (1,b) := by
  let t := LinearMap.GeneralLinearGroup.toLinearEquiv a.val
  obtain ⟨b,hb⟩ := left_centralizing_involution t
    (fun v => congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val v) ha2)
    (by
      intro g v
      have hh := hc (SquarePreserving.pairHom (binaryAction (F := F)) (g,1))
        (show SquarePreserving.pairHom (binaryAction (F := F)) (g,1) ∈ SquarePreserving.left (binaryAction (F := F)) from
          ⟨(g,1),⟨mem_top _,rfl⟩,rfl⟩)
      exact (congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val v) hh).symm)
  have he : a.val = (binaryAction (F := F)).asGroupHom (1,b) := Units.ext (LinearMap.ext hb)
  have hb2 : b*b=1 := by
    have hh := congrArg (fun x : SquarePreserving.group (binaryAction (F := F)) => x.val.val) ha2
    change a.val.val * a.val.val = 1 at hh
    rw [he] at hh
    change binaryAction (F := F) _ * binaryAction (F := F) _ = 1 at hh
    rw [←map_mul,←map_one (binaryAction (F := F))] at hh
    exact congrArg Prod.snd (binaryAction_injective hh)
  refine ⟨b,hb2,?_,he⟩
  intro hane hb1
  apply hane
  apply Subtype.ext
  rw [he,hb1]
  exact (binaryAction (F := F)).asGroupHom.map_one

/-- Both literal component kernels supply independent inner operators. -/
theorem preserving_fixedCodim_ge_three_degree
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (SquarePreserving.group (binaryAction (F := F))))
    [IsElementaryAbelian 2 A] (hr : n < rank A) :
    3*finrank (ZMod 2) F ≤ fixedCodim (SquarePreserving.action (binaryAction (F := F))) A := by
  let : Finite (Module.End (ZMod 2) (Mat (F := F))) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  obtain ⟨a,ha,ha1,hac⟩ := SquarePreserving.exists_centralizing_member_of_rank_gt
    (binaryAction (F := F)) n hn hF A (SquarePreserving.right (binaryAction (F := F)))
    (SquarePreserving.rightEquiv (binaryAction (F := F)) binaryAction_injective) hr
  obtain ⟨b,hb,hb1,hbc⟩ := SquarePreserving.exists_centralizing_member_of_rank_gt
    (binaryAction (F := F)) n hn hF A (SquarePreserving.left (binaryAction (F := F)))
    (SquarePreserving.leftEquiv (binaryAction (F := F)) binaryAction_injective) hr
  have ha2 : a*a=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hb2 : b*b=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  obtain ⟨x,hx,hx1,hax⟩ := supported_left a ha2 hac
  obtain ⟨y,hy,hy1,hby⟩ := supported_right b hb2 hbc
  have hh := fixedCodim_ge_three_degree_of_independent_inner
    (A.map (SquarePreserving.group (binaryAction (F := F))).subtype) x y hx hy (hx1 ha1) (hy1 hb1)
    (hax ▸ mem_map_of_mem _ ha) (hby ▸ mem_map_of_mem _ hb)
  have he := fixedCodim_map_equivariant (SquarePreserving.action (binaryAction (F := F)))
    (Units.coeHom _) (SquarePreserving.group (binaryAction (F := F))).subtype
    (LinearEquiv.refl (ZMod 2) (Mat (F := F))) (fun _ _ => rfl) A
  exact he ▸ hh

variable [IsQuasisimple SL(2,F)]
/-- A large elementary image in the entire binary normalizer moves at least 3n dimensions. -/
theorem normalizer_fixedCodim_ge_three_degree
    (hi : (binaryAction (F := F)).IsIrreducible) (hZ : center SL(2,F) = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (linearNormalizer (binaryAction (F := F))))
    [IsElementaryAbelian 2 A] (hr : n+1 < rank A) :
    3*finrank (ZMod 2) F ≤ fixedCodim (normalizerRepresentation (binaryAction (F := F))) A := by
  have hp := SquarePreserving.preserving_of_rank_gt (binaryAction (F := F)) hi binaryAction_injective
    hZ n hn hF A hr
  let j : A →* SquarePreserving.group (binaryAction (F := F)) :=
    ((linearNormalizer (binaryAction (F := F))).subtype.comp A.subtype).codRestrict _
      (fun a => hp a a.property)
  have hj : Function.Injective j := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : SquarePreserving.group (binaryAction (F := F)) => z.val) h))
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have he : rank j.range = rank A :=
    (congrArg (Nat.log 2) (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv)).symm
  have hb := preserving_fixedCodim_ge_three_degree n hn hF j.range (by rw [he]; omega)
  have hfix : fixedSpace (SquarePreserving.action (binaryAction (F := F))) j.range =
      fixedSpace (normalizerRepresentation (binaryAction (F := F))) A := by
    ext v
    exact ⟨fun hv a => hv ⟨j a,⟨a,rfl⟩⟩,fun hv ⟨_,a,rfl⟩ => hv a⟩
  unfold fixedCodim at hb ⊢
  rwa [hfix] at hb

/-- H.1.1's rank/codimension gap on the entire determinant normalizer. -/
theorem normalizer_rank_add_degree_le_fixedCodim_add_one
    (hi : (binaryAction (F := F)).IsIrreducible) (hZ : center SL(2,F) = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (linearNormalizer (binaryAction (F := F)))) (hA : IsElementaryTwo A) :
    rank A + n ≤ fixedCodim (normalizerRepresentation (binaryAction (F := F))) A + 1 := by
  let := hA.2
  have hd : finrank (ZMod 2) F = n := Representation.BinaryOffender.NaturalTensor.finrank_field F hF
  have hr := SquarePreserving.normalizer_rank_le_twice_degree (binaryAction (F := F)) hi
    binaryAction_injective hZ n hn hF A
  by_cases hlarge : n+1 < rank A
  · have hb := normalizer_fixedCodim_ge_three_degree hi hZ n hn hF A hlarge
    rw [hd] at hb
    omega
  by_cases hsmall : fixedCodim (normalizerRepresentation (binaryAction (F := F))) A < 2*n
  · have hc := NaturalTensor.rank_le_one_of_fixedCodim_lt_twice_degree
      (by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2^2)
          (Nat.pow_le_pow_right (by decide) hn))
      (binaryAction (F := F)) binaryAction_injective (MulEquiv.refl _) (LinearEquiv.refl _ _)
      (fun _ _ => rfl) A (by rwa [hd])
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have hm := NaturalTensor.normalizer_displacement_ge (binaryAction (F := F)) binaryAction_injective
      (MulEquiv.refl _) (LinearEquiv.refl _ _) (fun _ _ => rfl) a ha1
    have hb := operatorFixedCodim_le_fixedCodim (normalizerRepresentation (binaryAction (F := F))) A ha
    rw [hd] at hm
    omega
  · omega
end ClassicalOrthogonal.FourPlusMatrix.GeneralActors

namespace ClassicalOrthogonal.FourPlusMatrix.GeneralActors
variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V] [IsQuasisimple SL(2,F)]

/-- Transport the rank gap and large-image displacement with the original marking. -/
theorem marked_normalizer_bounds
    (σ : Representation (ZMod 2) (PairSL (F := F)) V) (hi : σ.IsIrreducible)
    (hZ : center SL(2,F) = ⊥) (e : MulAut (PairSL (F := F)))
    (f : V ≃ₗ[ZMod 2] Mat (F := F))
    (hf : ∀ g v, f (σ g v) = (binaryAction (F := F)) (e g) (f v))
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    rank A ≤ 2*n ∧
      rank A+n ≤ fixedCodim (normalizerRepresentation σ) A+1 ∧
      (n+1 < rank A → 3*n ≤ fixedCodim (normalizerRepresentation σ) A) := by
  let b : σ.Equiv ((binaryAction (F := F)).comp e.toMonoidHom) :=
    Representation.Equiv.mk f (fun g => LinearMap.ext (hf g))
  have hi' : (binaryAction (F := F)).IsIrreducible :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective (binaryAction (F := F))).mp
      ((RepEquiv.ofRepresentationEquiv b.symm).irreducible_of_euqiv hi)
  let u := BinaryNormalizerResidual.unitConj f
  have hm := BinaryNormalizerResidual.normalizer_map σ (binaryAction (F := F)) e f hf
  let j : linearNormalizer σ →* linearNormalizer (binaryAction (F := F)) :=
    (u.toMonoidHom.comp (linearNormalizer σ).subtype).codRestrict _
      (fun a => hm ▸ mem_map_of_mem u.toMonoidHom a.property)
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (u.injective (congrArg (fun z : linearNormalizer (binaryAction (F := F)) => z.val) h))
  let C := A.map j
  let := hA.2
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.map j⟩
    intro hz
    exact hA.1 ((Subgroup.map_injective hj) (hz.trans (map_bot j).symm))
  have he : fixedCodim (normalizerRepresentation σ) A =
      fixedCodim (normalizerRepresentation (binaryAction (F := F))) C :=
    fixedCodim_map_equivariant _ _ j f (fun a v => by
      change f (a.val.val v) = f (a.val.val (f.symm (f v)))
      rw [f.symm_apply_apply]) A
  have hr : rank C = rank A := rank_map_injective j hj A
  let := hC.2
  have hb := SquarePreserving.normalizer_rank_le_twice_degree (binaryAction (F := F)) hi'
    binaryAction_injective hZ n hn hF C
  have hg := normalizer_rank_add_degree_le_fixedCodim_add_one hi' hZ n hn hF C hC
  have hd := Representation.BinaryOffender.NaturalTensor.finrank_field F hF
  refine ⟨by rwa [hr] at hb,by rwa [hr,←he] at hg,?_⟩
  intro hlarge
  have hh := normalizer_fixedCodim_ge_three_degree hi' hZ n hn hF C (by rwa [hr])
  rwa [hd,←he] at hh
end ClassicalOrthogonal.FourPlusMatrix.GeneralActors
