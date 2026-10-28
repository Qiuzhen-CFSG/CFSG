module
public import Theory.GroupAction.NormalizerFrattiniTransport

/-!
# Relative normalizer actions after an injective restriction

If a homomorphism embeds P ≤ X, it identifies P with its image and transports
irreducibility under N_{N_G(X)}(P) to the corresponding image normalizer.
The homomorphism need not embed X or either ambient group.

This extends the Frattini transport theorem using the actual map between
N_G(X) and N_H(f(X)). It is used for the core-quotient action in
Aschbacher–Smith, 13.1.12(3), printed p.875.
-/

public noncomputable section
namespace Subgroup

/-- Restrict the actual quotient map to the two actual normalizers. The
irreducible actor is transported only after checking injectivity on P. -/
theorem irreducible_map_relative_normalizer
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (X P : Subgroup G) (hPX : P ≤ X)
    (hf : Function.Injective (f.comp P.subtype))
    (hirr : IsNormalizerFrattiniIrreducible (P.subgroupOf (normalizer X))) :
    IsNormalizerFrattiniIrreducible ((P.map f).subgroupOf (normalizer (X.map f))) := by
  let NX := normalizer (X : Set G)
  let NY := normalizer (X.map f : Set H)
  let φ : NX →* NY := (f.comp NX.subtype).codRestrict NY (by
    intro x
    exact X.le_normalizer_map f (mem_map_of_mem f x.property))
  let P₀ := P.subgroupOf NX
  let e : P₀ ≃* P := subgroupOfEquivOfLe (hPX.trans X.le_normalizer)
  have hi : Function.Injective (φ.subgroupMap P₀) := by
    intro a b hab
    apply e.injective
    apply hf
    exact congrArg (fun y : P₀.map φ => ((y.val : NY) : H)) hab
  have he : P₀.map φ = (P.map f).subgroupOf NY := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,hPX.trans X.le_normalizer hx⟩,hx,Subtype.ext he⟩
  rw [←he]
  exact normalizerFrattiniIrreducible_map φ P₀ (normalizer P₀) le_rfl hi hirr

end Subgroup
