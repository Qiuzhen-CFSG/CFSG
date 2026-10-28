module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Fixed points on a centralizer over an irreducible section

Let `E ≤ R`, with `E` abelian, and let `D` normalize `R` and act
irreducibly on the section `R/E`. If `f ∈ C_E(D)` centralizes an element
of `R − E`, then `C_R(f)` is a `D`-invariant subgroup strictly above `E`.
Thus it equals `R`. When `L ≤ ⟨D,R⟩`, `E ≤ T`, and `C_T(L)=1`, this
forces `f=1`. A commutator with this element then embeds `C_E(D)` in
any subgroup containing its commutator values.

The irreducibility premise is stated in terms of intermediate invariant
subgroups; callers must derive it from their actual section action. This is
an alternative to the torus argument in Aschbacher–Smith, Lemma 6.1.26,
combined 1 March 2004 manuscript, printed pp.678–679.
-/

namespace Subgroup

public theorem fixed_centralizer_eq_bot_of_irreducible_section
    {G : Type*} [Group G] {D R E T L : Subgroup G}
    (hER : E ≤ R) (hET : E ≤ T) (hEE : E ≤ centralizer (E : Set G))
    (hDR : D ≤ normalizer (R : Set G))
    (hL : L ≤ D ⊔ R) (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hIrr : ∀ A : Subgroup G, E ≤ A → A ≤ R →
      D ≤ normalizer (A : Set G) → A = E ∨ A = R)
    {u : G} (huR : u ∈ R) (huE : u ∉ E) :
    (E ⊓ centralizer (D : Set G)) ⊓ centralizer ({u} : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hDC : D ≤ centralizer ({f} : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hf.1.2 d hd)
  let A := R ⊓ centralizer ({f} : Set G)
  have hEA : E ≤ A := by
    intro e he
    exact ⟨hER he, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp
      (hEE hf.1.1) e he)⟩
  have hDA : D ≤ normalizer (A : Set G) :=
    (le_inf hDR (hDC.trans (centralizer ({f} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have huA : u ∈ A := ⟨huR, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hf.2).symm⟩
  have hAR : A = R := (hIrr A hEA inf_le_left hDA).resolve_left (by
    intro hAE
    exact huE (hAE ▸ huA))
  have hRC : R ≤ centralizer ({f} : Set G) := hAR ▸ (inf_le_right : A ≤ _)
  have hfL : f ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((hL.trans (sup_le hDC hRC)) hx)
  exact hCT ▸ (show f ∈ T ⊓ centralizer (L : Set G) from ⟨hET hf.1.1, hfL⟩)

open scoped commutatorElement in
public theorem card_le_of_injective_commutator
    {G : Type*} [Group G] [Finite G] {F Z : Subgroup G} {u : G}
    (hfix : F ⊓ centralizer ({u} : Set G) = ⊥)
    (hcomm : ∀ f ∈ F, ⁅f, u⁆ ∈ Z) : Nat.card F ≤ Nat.card Z := by
  let c : F → Z := fun f => ⟨⁅(f : G), u⁆, hcomm f f.property⟩
  apply Nat.card_le_card_of_injective c
  intro f g hfg
  have hh : ⁅(f : G), u⁆ = ⁅(g : G), u⁆ := congrArg Subtype.val hfg
  have heq : (g : G)⁻¹ * f ∈ F ⊓ centralizer ({u} : Set G) := by
    refine ⟨F.mul_mem (F.inv_mem g.property) f.property,
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hh' : (f : G) * u * (f : G)⁻¹ = (g : G) * u * (g : G)⁻¹ :=
      mul_right_cancel hh
    calc
      _ = (g : G)⁻¹ * ((f : G) * u * (f : G)⁻¹) * (f : G) := by group
      _ = _ := by rw [hh']; group
  have hone : (g : G)⁻¹ * f = 1 := by simpa only [hfix, mem_bot] using heq
  exact Subtype.ext (inv_mul_eq_one.mp hone).symm

end Subgroup
