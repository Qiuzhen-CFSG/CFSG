module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The covered residuals of Notation 13.2.1

The definitions retain the actual central preimage, relative normalizer,
commutator, and embedded two-residual. Characteristic residuals and quotient
centers give the normalization relations needed for these particular source
subgroups. None of the definitions identifies a subgroup with its quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877; used in 13.8.21(1), printed p.957.
The concrete covered model, its local actions, and placement inside K remain
separate mathematical obligations.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G]

/-- The intrinsic two-residual, embedded in the original ambient group. -/
def residual (A : Subgroup G) : Subgroup G := (pResidual 2 A).map A.subtype

/-- The actual O₂,Z(L): inverse image of Z(L/O₂(L)), embedded in G. -/
def centralPreimage (L : Subgroup G) : Subgroup G :=
  ((center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))).map L.subtype

/-- L₀ = O²(O₂,Z(L)) from Notation 13.2.1. -/
def zero (L : Subgroup G) : Subgroup G := residual (centralPreimage L)

/-- M₁ = N_{LT}(V₁), with LT expressed as a subgroup join. -/
def parabolic (L T V₁ : Subgroup G) : Subgroup G :=
  (L ⊔ T) ⊓ normalizer (V₁ : Set G)

/-- L₁ = O²(M₁), distinct from the whole parabolic M₁. -/
def one (L T V₁ : Subgroup G) : Subgroup G := residual (parabolic L T V₁)

/-- X = L₁,+ = O²([L₁,T ∩ L]), with all groups embedded in G. -/
def plus (L T V₁ : Subgroup G) : Subgroup G := residual ⁅one L T V₁, T ⊓ L⁆

theorem residual_le (A : Subgroup G) : residual A ≤ A := map_subtype_le _

theorem zero_le (L : Subgroup G) : zero L ≤ L :=
  (residual_le _).trans (map_subtype_le _)

/-- Normalization passes to the embedded characteristic residual. -/
theorem normalizer_le_residual_normalizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (residual A : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨a, ha, rfl⟩ := hx
  let f := A.normalizerMonoidHom ⟨g, hg⟩
  exact ⟨f a, map_pResidual_le 2 f.toMonoidHom ⟨a, ha, rfl⟩, rfl⟩

/-- Conjugation preserving L preserves the inverse image of its quotient center. -/
theorem normalizer_le_centralPreimage_normalizer (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (centralPreimage L : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨a, ha, rfl⟩ := hx
  let f := L.normalizerMonoidHom ⟨g, hg⟩
  let fbar := quotientAut (pCore 2 L) f
  have hf : (center (L ⧸ pCore 2 L)).comap fbar.toMonoidHom = center (L ⧸ pCore 2 L) :=
    (inferInstance : (center (L ⧸ pCore 2 L)).Characteristic).fixed fbar
  have hfa : fbar (QuotientGroup.mk' (pCore 2 L) a) ∈ center (L ⧸ pCore 2 L) := by
    change QuotientGroup.mk' (pCore 2 L) a ∈ (center (L ⧸ pCore 2 L)).comap fbar.toMonoidHom
    rw [hf]
    exact ha
  refine ⟨f a, ?_, rfl⟩
  change QuotientGroup.mk' (pCore 2 L) (f a) ∈ center (L ⧸ pCore 2 L)
  rw [← quotientAut_apply_mk]
  exact hfa

/-- Every normalizer of L also normalizes the source L₀. -/
theorem normalizer_le_zero_normalizer (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (zero L : Set G) :=
  (normalizer_le_centralPreimage_normalizer L).trans (normalizer_le_residual_normalizer _)

/-- L₀ is normal relative to L; ambient normality is not asserted. -/
theorem L_normalizes_zero (L : Subgroup G) : L ≤ normalizer (zero L : Set G) := by
  exact L.le_normalizer.trans (normalizer_le_zero_normalizer L)

theorem one_le (L T V₁ : Subgroup G) : one L T V₁ ≤ parabolic L T V₁ :=
  residual_le _

/-- The T-invariant source line puts T in M₁, hence in N_G(L₁). -/
theorem T_normalizes_one (L T V₁ : Subgroup G)
    (hTV : T ≤ normalizer (V₁ : Set G)) : T ≤ normalizer (one L T V₁ : Set G) :=
  (le_inf le_sup_right hTV).trans
    ((parabolic L T V₁).le_normalizer.trans (normalizer_le_residual_normalizer _))

/-- The commutator and its residual are normalized by L₁. -/
theorem one_normalizes_plus (L T V₁ : Subgroup G) :
    one L T V₁ ≤ normalizer (plus L T V₁ : Set G) :=
  (normalizer_commutator_ge_left _ _).trans (normalizer_le_residual_normalizer _)

theorem plus_le_one (L T V₁ : Subgroup G)
    (hTV : T ≤ normalizer (V₁ : Set G)) : plus L T V₁ ≤ one L T V₁ :=
  (residual_le _).trans (le_normalizer_iff_commutator_le_left.mp
    (inf_le_left.trans (T_normalizes_one L T V₁ hTV)))

/-- T normalizes both commutator factors and therefore their residual. -/
theorem T_normalizes_plus (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G)) :
    T ≤ normalizer (plus L T V₁ : Set G) := by
  apply le_trans ?_ (normalizer_le_residual_normalizer _)
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (T_normalizes_one L T V₁ hTV ht),
    mem_normalizer_iff_map_conj_eq.mp
      (((le_inf T.le_normalizer hTL).trans inf_normalizer_le_normalizer_inf) ht)]


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
