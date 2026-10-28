module
public import Theory.Representation.RepEquiv
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryConjugationSection.Cover
public import Theory.Representation.BinaryConjugationSection.Descent

/-!
# Original normalizers on marked binary sections

Conjugation extends to the numerator and its marked quotient using the
literal coordinate map. Its compatibility with the component automorphism
is retained. Equal section markings transport irreducibility. Source use:
Aschbacher–Smith10.2.9, printed p.751.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {L W Z P : Subgroup G} [IsElementaryAbelian 2 W]

/-- Literal conjugation on an elementary abelian subgroup. -/
def originalNormalizerAction (hPW : P ≤ normalizer (W : Set G)) :
    Representation (ZMod 2) P (Additive W) :=
  let β := W.normalizerMonoidHom.comp (inclusion hPW)
  { toFun p := (β p).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro w; change β 1 w.toMul = w.toMul; rw [map_one]; rfl
    map_mul' p r := by
      apply LinearMap.ext
      intro w
      change β (p*r) w.toMul = β p (β r w.toMul)
      rw [map_mul]
      rfl }

/-- The numerator action is literal conjugation. -/
theorem originalNormalizerAction_apply
    (hPW : P ≤ normalizer (W : Set G)) (p : P) (w : Additive W) :
    (originalNormalizerAction hPW p w).toMul =
      W.normalizerMonoidHom (inclusion hPW p) w.toMul := by rfl

/-- The literal ambient formula for the numerator action. -/
theorem originalNormalizerAction_apply_coe
    (hPW : P ≤ normalizer (W : Set G)) (p : P) (w : Additive W) :
    ((originalNormalizerAction hPW p w).toMul : G) =
      p*w.toMul*(p : G)⁻¹ := by rfl

/-- The given section coordinates extend to every common normalizer of
its numerator and kernel, without requiring its actor to contain them. -/
theorem exists_original_quotient_action
    {ρ : Representation (ZMod 2) L V}
    (c : BinaryConjugationSection L W Z ρ)
    (hPW : P ≤ normalizer (W : Set G)) (hPZ : P ≤ normalizer (Z : Set G)) :
    ∃ η : Representation (ZMod 2) P V,
      ∀ (p : P) (w : W), η p (c.coordinates w).toAdd =
        (c.coordinates (W.normalizerMonoidHom (inclusion hPW p) w)).toAdd := by
  let : (Z.subgroupOf W).Normal := c.kernel_normal
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action P W Z hPW hPZ c.kernel_normal
  let η₀ : Representation (ZMod 2) P (Additive (W ⧸ Z.subgroupOf W)) := {
    toFun p := (β p).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; change β 1 v.toMul = v.toMul; rw [map_one]; rfl
    map_mul' p r := by
      apply LinearMap.ext
      intro v
      change β (p*r) v.toMul = β p (β r v.toMul)
      rw [map_mul]
      rfl }
  let E : Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (c.quotientEquiv.toMonoidHom.toAdditiveLeft.toZModLinearMap 2)
      c.quotientEquiv.bijective
  let η := E.conjRingEquiv.toMonoidHom.comp η₀
  refine ⟨η,fun p w => ?_⟩
  have he (w : W) : E (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
      (c.coordinates w).toAdd := congrArg Multiplicative.toAdd (c.quotientEquiv_mk w)
  rw [←he w]
  change E (η₀ p (E.symm (E (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w))))) = _
  rw [E.symm_apply_apply]
  change E (Additive.ofMul (β p (QuotientGroup.mk' (Z.subgroupOf W) w))) = _
  rw [hβ]
  exact he _

/-- A marked component action and literal normalizer action have the same
conjugation automorphism on their fully moved module. -/
theorem originalNormalizerAction_compatible
    (q : L →* J) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) J (Additive W))
    (hσ : ∀ (l : L) (w : Additive W),
      ((σ (q l) w).toMul : G) = l*w.toMul*(l : G)⁻¹)
    (hPL : P ≤ normalizer (L : Set G)) (hPW : P ≤ normalizer (W : Set G))
    (a : P →* MulAut J)
    (ha : ∀ (p : P) (l : L), a p (q l) =
      q (L.normalizerMonoidHom (inclusion hPL p) l)) :
    ∀ p j w, originalNormalizerAction hPW p (σ j w) =
      σ (a p j) (originalNormalizerAction hPW p w) := by
  intro p j w
  obtain ⟨l,rfl⟩ := hq j
  apply Additive.toMul.injective
  apply Subtype.ext
  change (p : G)*((σ (q l) w).toMul : G)*(p : G)⁻¹ = _
  rw [ha,hσ,hσ]
  change (p : G)*((l : G)*w.toMul*(l : G)⁻¹)*(p : G)⁻¹ =
    ((p : G)*l*(p : G)⁻¹)*((p : G)*w.toMul*(p : G)⁻¹)*
      ((p : G)*l*(p : G)⁻¹)⁻¹
  group
end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
open Representation.OneCohomology
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {L W Z P : Subgroup G} [IsElementaryAbelian 2 W]

/-- The same marked normalizer compatibility descends through a surjective
intertwiner; this avoids changing quotient coordinates. -/
theorem quotient_action_compatible
    {ρ : Representation (ZMod 2) J V}
    {σ : Representation (ZMod 2) J (Additive W)}
    (f : σ.IntertwiningMap ρ) (hf : Function.Surjective f)
    (τ : Representation (ZMod 2) P (Additive W))
    (η : Representation (ZMod 2) P V) (a : P →* MulAut J)
    (ht : ∀ p j w, τ p (σ j w) = σ (a p j) (τ p w))
    (hη : ∀ p w, f (τ p w) = η p (f w)) :
    ∀ p j v, η p (ρ j v) = ρ (a p j) (η p v) := by
  intro p j v
  obtain ⟨w,rfl⟩ := hf v
  rw [←f.isIntertwining,←hη,ht,f.isIntertwining,hη]
end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
open Subgroup Representation.OneCohomology
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {L W Z P : Subgroup G} [IsElementaryAbelian 2 W]

omit [IsElementaryAbelian 2 W] in
/-- Simplicity transports between two markings of the same literal section. -/
theorem irreducible_of_same_section
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) L U} {σ : Representation (ZMod 2) L V}
    (c : BinaryConjugationSection L W Z ρ)
    (d : BinaryConjugationSection L W Z σ) (hi : ρ.IsIrreducible) :
    σ.IsIrreducible := by
  let : (Z.subgroupOf W).Normal := c.kernel_normal
  let E : U ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective
      ((AddMonoidHom.toMultiplicative.symm (c.quotientEquiv.symm.trans d.quotientEquiv).toMonoidHom).toZModLinearMap 2)
      (c.quotientEquiv.symm.trans d.quotientEquiv).bijective
  have he (w : W) : E (c.coordinates w).toAdd = (d.coordinates w).toAdd := by
    change (d.quotientEquiv (c.quotientEquiv.symm (c.coordinates w))).toAdd = _
    rw [←c.quotientEquiv_mk, c.quotientEquiv.symm_apply_apply, d.quotientEquiv_mk]
  let e : ρ.Equiv σ := Representation.Equiv.mk E (by
    intro l
    apply LinearMap.ext
    intro u
    obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd u)
    change E (ρ l (c.coordinates w).toAdd) = σ l (E (c.coordinates w).toAdd)
    rw [←c.equivariant,he,he,d.equivariant])
  exact (Representation.RepEquiv.ofRepresentationEquiv e.symm).irreducible_of_euqiv hi
end Representation.BinaryConjugationSection
