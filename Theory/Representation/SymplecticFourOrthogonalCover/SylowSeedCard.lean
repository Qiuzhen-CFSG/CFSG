module

public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Conjugation
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The fixed Sylow seed has order at most q squared

Every central cover is a quotient of the explicit odd-orthogonal cover.
Fixed-point lifting makes the induced map on Sylow fixed spaces surjective.
The model fixed space is the preimage of its unique natural fixed line,
which has dimension two over the field. Thus every literal fixed seed has
order at most q squared, including its entire fixed central attachment.
The subgroup consumer applies this to U intersect C(T) when T's actual
image is a full model Sylow.

Source: MS93 (3.2),(3.4), pp.864,868; the model flag and universal-cover
identifications are proved in the imported modules.
-/

public section

open Representation.OneCohomology
namespace Representation.SymplecticFourOrthogonalCover
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := K)) W}

theorem cover_sylow_fixed_card_le (p : σ.IntertwiningMap (binaryNatural (K := K)))
    (hp : IsCover p) (S : Sylow 2 (L (K := K))) :
    Nat.card (fixed (σ.comp (S : Subgroup (L (K := K))).subtype)) ≤ Nat.card K ^ 2 := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let A := (S : Subgroup (L (K := K)))
  let F₀ := fixed ((binaryAction (K := K)).comp A.subtype)
  let F₁ := fixed (σ.comp A.subtype)
  let φ : F₀ → F₁ := fun v => ⟨f v,by
    intro a
    change σ a.val (f v) = f v
    rw [←f.isIntertwining]
    exact congrArg f (v.property a)⟩
  have hφ : Function.Surjective φ := by
    intro w
    obtain ⟨v,hv⟩ := hf w.val
    have hfixed : v ∈ F₀ := by
      intro a
      change binaryAction (K := K) a.val v = v
      apply cover_fixed_of_projection_fixed (binaryProjection (K := K))
        (binaryProjection_isCover (K := K)) a.val v
      rw [←hpf,hv,←p.isIntertwining]
      exact congrArg p (w.property a)
    exact ⟨⟨v,hfixed⟩,Subtype.ext hv⟩
  have hc0 : Nat.card (fixed ((action (K := K)).comp
      (S : Subgroup (L (K := K))).subtype)) = Nat.card K ^ 2 := by
    obtain ⟨g,hg⟩ := SylowFlag.exists_marking S
    rw [hg,SylowFlag.moved_cover_fixed,Module.natCard_eq_pow_finrank (K := K),
      SylowFlag.moved_preimage_finrank]
  have hc : Nat.card F₀ = Nat.card K ^ 2 := hc0
  exact (Nat.card_le_card_of_surjective φ hφ).trans_eq hc

variable {G : Type*} [Group G]
open Subgroup
open scoped IsMulCommutative

theorem centralizer_cover_sylow_card_le
    (U T : Subgroup G) [Finite U] [IsElementaryAbelian 2 U]
    (π : T →* L (K := K)) (S : Sylow 2 (L (K := K)))
    (himage : π.range = (S : Subgroup (L (K := K))))
    (σ : Representation (ZMod 2) (L (K := K)) (Additive U))
    (hact : ∀ t : T, ∀ u : U,
      ((σ (π t) (Additive.ofMul u)).toMul : G) = (t:G)*u*(t:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ Nat.card K ^ 2 := by
  let φ : (U ⊓ centralizer (T : Set G) : Subgroup G) →
      fixed (σ.comp (S : Subgroup (L (K := K))).subtype) := fun x =>
    ⟨Additive.ofMul ⟨x,x.property.1⟩,by
      intro a
      obtain ⟨t,ht⟩ := (show (a : L (K := K)) ∈ π.range from himage.symm ▸ a.property)
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((σ a.val (Additive.ofMul ⟨x,x.property.1⟩)).toMul : G) = x
      rw [←ht,hact]
      change (t:G)*(x:G)*(t:G)⁻¹ = (x:G)
      rw [x.property.2 t t.property,mul_inv_cancel_right]⟩
  have hi : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun w => (w.val.toMul : G)) h
  exact (Nat.card_le_card_of_injective φ hi).trans (cover_sylow_fixed_card_le p hp S)

theorem centralizer_embedded_cover_sylow_card_le
    (U T : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjU : j.range = U)
    (π : T →* L (K := K)) (S : Sylow 2 (L (K := K)))
    (himage : π.range = (S : Subgroup (L (K := K))))
    (σ : Representation (ZMod 2) (L (K := K)) W)
    (hact : ∀ t : T, ∀ w : W,
      j (Multiplicative.ofAdd (σ (π t) w)) = (t:G)*j (Multiplicative.ofAdd w)*(t:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ Nat.card K ^ 2 := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let V := fixed (σ.comp (S : Subgroup (L (K := K))).subtype)
  let φ : V → (U ⊓ centralizer (T : Set G) : Subgroup G) := fun w =>
    ⟨j (Multiplicative.ofAdd w),⟨hjU ▸ ⟨_,rfl⟩,by
      intro t ht
      have hm : π ⟨t,ht⟩ ∈ (S : Subgroup (L (K := K))) := himage ▸ ⟨⟨t,ht⟩,rfl⟩
      have he := congrArg (fun x => j (Multiplicative.ofAdd x)) (w.property ⟨π ⟨t,ht⟩,hm⟩)
      change j (Multiplicative.ofAdd (σ (π ⟨t,ht⟩) w)) = j (Multiplicative.ofAdd w) at he
      rw [hact] at he
      exact mul_inv_eq_iff_eq_mul.mp he⟩⟩
  have hs : Function.Surjective φ := by
    intro y
    obtain ⟨w,hw⟩ := (show (y:G) ∈ j.range from hjU.symm ▸ y.property.1)
    have hfix : w.toAdd ∈ V := by
      intro a
      obtain ⟨t,ht⟩ := (show (a:L (K := K)) ∈ π.range from himage.symm ▸ a.property)
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (σ a.val w.toAdd)) = j w
      rw [←ht,hact,hw]
      change (t:G)*j w*(t:G)⁻¹ = (y:G)
      rw [hw,y.property.2 t t.property,mul_inv_cancel_right]
    exact ⟨⟨w.toAdd,hfix⟩,Subtype.ext hw⟩
  exact (Nat.card_le_card_of_surjective φ hs).trans (cover_sylow_fixed_card_le p hp S)

end Representation.SymplecticFourOrthogonalCover
