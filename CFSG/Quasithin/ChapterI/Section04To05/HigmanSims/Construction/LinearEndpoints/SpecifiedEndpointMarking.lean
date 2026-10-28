module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.SpecifiedEndpoint
public import Theory.GroupTheory.SplitExtensionGivenComplement

/-!
# Exact quotient and kernel coordinates on the specified endpoint

The endpoint and complement supplied by the frozen constructor are retained.
Its literal inverse-image equality reconstructs the quotient map into the
specified native embedding. The kernel coordinates are the prescribed
symplectic coordinates followed by the inverse native coordinates. Both
comparison equations are exported for whole-Borel compatibility.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "SL" => Representation.SL2FourNatural.SL
local notation "W" => Representation.SL2FourNatural.V

/-- The literal inverse image of a specified natural SL₂(4) embedding
is split, with its whole original kernel and quotient action retained. -/
theorem exists_exactly_marked_natural_endpoint
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (e : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      Matrix.PSp4Three.Sp 2 (ZMod 2))
    (hφ : ∀ (g : normalizer (A : Set G)) (x : A),
      (φ (QuotientGroup.mk g)).val *ᵥ e (Additive.ofMul x) =
        e (Additive.ofMul (A.normalizerMonoidHom g x)))
    (v : W ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (ι : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2)) (hι : Function.Injective ι)
    (hv : ∀ g w, (ι g).val *ᵥ v w = v (Representation.SL2FourNatural.action g w)) :
    ∃ (P K : Subgroup G) (_hAP : A ≤ P)
      (hPN : P ≤ normalizer (A : Set G)) (hKP : K ≤ P),
      P = (ι.range.comap (φ.toMonoidHom.comp
        (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G)))))).map
          (normalizer (A : Set G)).subtype ∧
      Nat.card P = 960 ∧ Nat.card K = 60 ∧ A ⊓ K = ⊥ ∧ A ⊔ K = P ∧
      ∃ q : P →* SL, Function.Surjective q ∧ q.ker = A.subgroupOf P ∧
        ∃ c : A ≃* Multiplicative W,
          (∀ g : P, ι (q g) = φ (QuotientGroup.mk (inclusion hPN g))) ∧
          (∀ a : A, (c a).toAdd = v.symm (e (Additive.ofMul a))) ∧
          (∀ (g : P) (a : A), c (A.normalizerMonoidHom (inclusion hPN g) a) =
            Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd)) ∧
          (A.subgroupOf P).IsComplement' (K.subgroupOf P) ∧
          ∃ k : K ≃* SL, ∀ g : K, k g = q (inclusion hKP g) := by
  obtain ⟨P, K, hAP, hPN, hKP, hPe, hP, hK, hAK, hjoin,
    _, _, _, _, _, hcomp, _⟩ :=
    exists_specified_natural_endpoint A hA e φ hφ v ι hι hv
  let N := normalizer (A : Set G)
  let AN := A.subgroupOf N
  let qN : N →* Matrix.PSp4Three.Sp 2 (ZMod 2) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' AN)
  have hqN : Function.Surjective qN :=
    φ.surjective.comp (QuotientGroup.mk'_surjective AN)
  have hqNk (g : N) : qN g = 1 ↔ (g : G) ∈ A := by
    change φ (QuotientGroup.mk' AN g) = 1 ↔ _
    rw [← φ.map_one, φ.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  have hmem (g : P) : qN (inclusion hPN g) ∈ ι.range := by
    have hg := g.property
    simp only [hPe] at hg
    obtain ⟨x, hx, he⟩ := hg
    have he' : x = inclusion hPN g := Subtype.ext he
    exact he' ▸ hx
  let j : SL ≃* ι.range := MonoidHom.ofInjective hι
  let qR : P →* ι.range :=
    (qN.comp (inclusion hPN)).codRestrict ι.range hmem
  let q : P →* SL := j.symm.toMonoidHom.comp qR
  have hιq (g : P) : ι (q g) = qN (inclusion hPN g) :=
    congrArg Subtype.val (j.apply_symm_apply (qR g))
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g, hg⟩ := hqN (ι a)
    have hgP : (g : G) ∈ P := by
      rw [hPe]
      refine ⟨g, ?_, rfl⟩
      change qN g ∈ ι.range
      rw [hg]
      exact ⟨a, rfl⟩
    refine ⟨⟨g, hgP⟩, hι ?_⟩
    rw [hιq]
    exact hg
  have hk : q.ker = A.subgroupOf P := by
    ext g
    change q g = 1 ↔ ((inclusion hPN g : N) : G) ∈ A
    rw [← hqNk (inclusion hPN g), ← hιq, ← ι.map_one, hι.eq_iff]
  let l : Additive A ≃ₗ[ZMod 2] W := e.trans v.symm
  let c : A ≃* Multiplicative W := MulEquiv.toAdditive.symm l.toAddEquiv
  have hc (g : P) (a : A) : c (A.normalizerMonoidHom (inclusion hPN g) a) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd) := by
    apply Multiplicative.toAdd.injective
    apply v.injective
    change v (v.symm (e (Additive.ofMul (A.normalizerMonoidHom (inclusion hPN g) a)))) =
      v (Representation.SL2FourNatural.action (q g) (v.symm (e (Additive.ofMul a))))
    rw [v.apply_symm_apply, ← hv, v.apply_symm_apply, hιq]
    exact (hφ (inclusion hPN g) a).symm
  have hcomp' : q.ker.IsComplement' (K.subgroupOf P) := hk ▸ hcomp
  let k' : K.subgroupOf P ≃* SL := hcomp'.symm.QuotientMulEquiv.symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hk' (g : K.subgroupOf P) : k' g = q g := by
    have he : hcomp'.symm.QuotientMulEquiv.symm g = QuotientGroup.mk' q.ker g := by
      apply hcomp'.symm.QuotientMulEquiv.injective
      rw [MulEquiv.apply_symm_apply, quotientMulEquiv_mk_apply_of_isComplement']
    change QuotientGroup.quotientKerEquivOfSurjective q hq
      (hcomp'.symm.QuotientMulEquiv.symm g) = q g
    rw [he]
    rfl
  let k := (subgroupOfEquivOfLe hKP).symm.trans k'
  refine ⟨P, K, hAP, hPN, hKP, hPe, hP, hK, hAK, hjoin, q, hq, hk, c,
    hιq, (fun _ => rfl), hc, hcomp, k, ?_⟩
  intro g
  exact hk' ((subgroupOfEquivOfLe hKP).symm g)

end CFSG.Quasithin.HigmanSims
