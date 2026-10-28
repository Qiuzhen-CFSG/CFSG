module
public import Theory.Representation.IrreducibleFivePlaneInverter
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.NormalizerFrattiniTransport

/-!
# The five-plane bound through its actual embedding and Frattini quotient

An elementary five-plane has trivial Frattini subgroup. The literal quotient
map therefore reflects invariance and inversion. A faithful embedding then
transports these properties to the actual subgroup of the actor group,
keeping the conjugation action fixed. The six-dimensional displacement
bound applies without identifying two different action kernels.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Representation
namespace Representation.IrreducibleFivePlaneInverter
variable {G Y W : Type*} [Group G] [Finite G] [Group Y] [Finite Y]
  [IsElementaryAbelian 5 Y]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual Frattini action and embedding supply the five-plane bound. -/
theorem six_le_displacement_of_embedded_frattini
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (j : Y →* G) (hj : Function.Injective j) (hY : Nat.card Y = 25)
    (a : G →* MulAut Y) (he : ∀ g y, j (a g y) = g * j y * g⁻¹)
    (A : Subgroup G) (hA : IsPGroup 3 A)
    (hirr : ∀ B : Subgroup (Y ⧸ frattini Y),
      (∀ g ∈ A, ∀ x ∈ B, quotientAut (frattini Y) (a g) x ∈ B) → B = ⊥ ∨ B = ⊤)
    (t : G) (ht : IsInvolution t)
    (hinv : ∀ x : Y ⧸ frattini Y, quotientAut (frattini Y) (a t) x = x⁻¹) :
    6 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  let : Fact (IsPGroup 5 Y) := ⟨IsElementaryAbelian.isPGroup 5 Y⟩
  let q : Y →* (Y ⧸ frattini Y) := QuotientGroup.mk' (frattini Y)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk',frattini_eq_bot_of_isElementaryAbelian (R := Y) (p := 5)])
  have hirrY (B : Subgroup Y)
      (hB : ∀ g ∈ A, ∀ x ∈ B, a g x ∈ B) : B = ⊥ ∨ B = ⊤ := by
    have hh := hirr (B.map q) (by
      intro g hg x hx
      obtain ⟨y,hy,rfl⟩ := hx
      change quotientAut (frattini Y) (a g) (QuotientGroup.mk' (frattini Y) y) ∈ B.map q
      rw [quotientAut_apply_mk]
      exact mem_map_of_mem q (hB g hg y hy))
    rcases hh with hb | htop
    · exact Or.inl ((Subgroup.map_injective hq) (by simpa only [Subgroup.map_bot] using hb))
    · exact Or.inr ((Subgroup.map_injective hq) (by
        simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using htop))
  have hinvY (y : Y) : a t y = y⁻¹ := by
    apply hq
    simpa only [q,map_inv,quotientAut_apply_mk] using hinv (q y)
  let P := j.range
  let e : Y ≃* P := MonoidHom.ofInjective hj
  let : IsElementaryAbelian 5 P := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hP : Nat.card P = 25 := (Nat.card_congr e.toEquiv).symm.trans hY
  have hN (g : G) : g ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨a g y,he g y⟩
    · rintro ⟨y,hy⟩
      refine ⟨a g⁻¹ y,?_⟩
      rw [he,hy]
      group
  let n : G →* normalizer (P : Set G) := (MonoidHom.id G).codRestrict _ hN
  have hequiv (g : G) (y : Y) : e (a g y) = P.normalizerMonoidHom (n g) (e y) :=
    Subtype.ext (he g y)
  apply six_le_displacement ρ hf P hP (n.comp A.subtype) hA
  · intro B hB
    have hh := hirrY (B.comap e.toMonoidHom) (by
      intro g hg x hx
      change e (a g x) ∈ B
      rw [hequiv]
      exact hB ⟨g,hg⟩ (e x) hx)
    rcases hh with hb | htop
    · left
      apply Subgroup.comap_injective (f := e.toMonoidHom) e.surjective
      simpa only [MonoidHom.comap_bot,(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective] using hb
    · right
      apply Subgroup.comap_injective (f := e.toMonoidHom) e.surjective
      simpa only [comap_top] using htop
  · exact ht
  · rintro x ⟨y,rfl⟩
    rw [←he,hinvY,map_inv]
end Representation.IrreducibleFivePlaneInverter
