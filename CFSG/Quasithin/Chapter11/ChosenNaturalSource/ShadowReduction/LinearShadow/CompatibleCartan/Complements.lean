module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Invariant field complements and the central commutator

Maschke's theorem constructs invariant complements over the specified
binary field for an odd-order actor. Their images are actual ambient
subgroups with a disjoint product decomposition. For the source pair of
abelian groups V and P, mutual normalization forces the commutator of
subgroups in V and P into V intersect P, hence into the center of their
join. Normalization by the actual Cartan passes to that commutator.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
after 11.3.8 and before 11.3.9, printed p.775. This does not yet prove that
the commutator is nontrivial or identify its scalar weights. The chosen
source complement application is in SourceFields.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
section Field
variable {F H M : Type*} [Field F] [CharP F 2] [Group H] [Finite H]
  [AddCommGroup M] [Module F M]

/-- Maschke over the actual coefficient field, with its specified action. -/
theorem exists_invariant_field_complement (hodd : Odd (Nat.card H))
    (ρ : Representation F H M) (U : Submodule F M)
    (hU : ∀ h : H, ∀ u ∈ U, ρ h u ∈ U) :
    ∃ W : Submodule F M, IsCompl U W ∧ ∀ h : H, ∀ w ∈ W, ρ h w ∈ W := by
  have : NeZero (Nat.card H : F) := ⟨fun hz => hodd.not_two_dvd_nat
    ((CharP.cast_eq_zero_iff F 2 (Nat.card H)).mp hz)⟩
  let U' : Subrepresentation ρ := ⟨U, hU⟩
  obtain ⟨W, hW⟩ := ComplementedLattice.exists_isCompl U'
  exact ⟨W.toSubmodule, IsCompl.of_eq
    (congrArg Subrepresentation.toSubmodule hW.inf_eq_bot)
    (congrArg Subrepresentation.toSubmodule hW.sup_eq_top), W.apply_mem_toSubmodule⟩

variable {G : Type*} [Group G] {P X : Subgroup G} [IsMulCommutative P]
    [Module F (Additive P)]

/-- A field subspace, as an actual subgroup of the original ambient group. -/
def ambientSubgroup (U : Submodule F (Additive P)) : Subgroup G :=
  U.toAddSubgroup.toSubgroup.map P.subtype

omit [CharP F 2] in
theorem mem_ambientSubgroup (U : Submodule F (Additive P)) (p : P) :
    (p : G) ∈ ambientSubgroup U ↔ Additive.ofMul p ∈ U := by
  constructor
  · rintro ⟨v, hv, he⟩
    have h : v = p := Subtype.ext he
    exact h ▸ hv
  · intro hp
    exact ⟨p, hp, rfl⟩

omit [CharP F 2] in
/-- Invariance of the vector subspace gives normalization of its literal image. -/
theorem normalizes_ambientSubgroup (ρ : Representation F X (Additive P))
    (hρ : ∀ (x : X) (p : Additive P),
      ((ρ x p).toMul : G) = (MulAut.conj (x : G)) (p.toMul : G))
    (U : Submodule F (Additive P)) (hU : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U) :
    X ≤ normalizer (ambientSubgroup U : Set G) := by
  intro x hx
  apply mem_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hv := hU ⟨x, hx⟩ (Additive.ofMul p) hp
    have hm := (mem_ambientSubgroup U (ρ ⟨x, hx⟩ (Additive.ofMul p)).toMul).mpr hv
    simpa [hρ] using hm
  · intro hg
    obtain ⟨p, hp, he⟩ := hg
    have hv := hU (⟨x, hx⟩ : X)⁻¹ (Additive.ofMul p) hp
    have hm := (mem_ambientSubgroup U (ρ (⟨x, hx⟩ : X)⁻¹ (Additive.ofMul p)).toMul).mpr hv
    rw [hρ] at hm
    have hm : x⁻¹ * (p : G) * x ∈ ambientSubgroup U := by simpa using hm
    change (p : G) = x * g * x⁻¹ at he
    rw [he] at hm
    simpa [mul_assoc] using hm

omit [CharP F 2] in
/-- Linear complements give a disjoint product inside the original subgroup. -/
theorem ambient_complement {U W : Submodule F (Additive P)} (h : IsCompl U W) :
    Disjoint (ambientSubgroup U) (ambientSubgroup W) ∧
      ambientSubgroup U ⊔ ambientSubgroup W = P := by
  constructor
  · apply disjoint_iff.mpr
    apply bot_unique
    rintro g ⟨⟨p, hp, rfl⟩, hW⟩
    have hpW := (mem_ambientSubgroup W p).mp hW
    have hz : Additive.ofMul p ∈ (⊥ : Submodule F (Additive P)) :=
      h.inf_eq_bot ▸ (show Additive.ofMul p ∈ U ⊓ W from ⟨hp, hpW⟩)
    have hz0 : Additive.ofMul p = 0 := hz
    have he := congrArg (fun z : Additive P => (z.toMul : G)) hz0
    simpa using he
  · apply le_antisymm
    · exact sup_le (map_subtype_le _) (map_subtype_le _)
    · intro g hg
      have hm : Additive.ofMul (⟨g, hg⟩ : P) ∈ U ⊔ W := h.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨u, hu, w, hw, he⟩ := Submodule.mem_sup.mp hm
      have hprod := mul_mem ((le_sup_left : ambientSubgroup U ≤ _)
        ((mem_ambientSubgroup U u.toMul).mpr hu))
        ((le_sup_right : ambientSubgroup W ≤ _)
        ((mem_ambientSubgroup W w.toMul).mpr hw))
      have he' := congrArg (fun z : Additive P => (z.toMul : G)) he
      have he'' : (u.toMul : G) * (w.toMul : G) = g := by simpa using he'
      rwa [he''] at hprod


variable [Finite G]

/-- Produce the actual invariant ambient complement from a stable field plane. -/
theorem exists_ambient_field_complement
    (hodd : Odd (Nat.card X)) (ρ : Representation F X (Additive P))
    (hρ : ∀ (x : X) (p : Additive P),
      ((ρ x p).toMul : G) = (MulAut.conj (x : G)) (p.toMul : G))
    (U : Submodule F (Additive P))
    (hU : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U) :
    ∃ W : Submodule F (Additive P), IsCompl U W ∧
      Disjoint (ambientSubgroup U) (ambientSubgroup W) ∧
      ambientSubgroup U ⊔ ambientSubgroup W = P ∧
      X ≤ normalizer (ambientSubgroup W : Set G) := by
  obtain ⟨W, hcompl, hW⟩ := exists_invariant_field_complement hodd ρ U hU
  exact ⟨W, hcompl, (ambient_complement hcompl).1, (ambient_complement hcompl).2,
    normalizes_ambientSubgroup ρ hρ W hW⟩

end Field

section Commutators
variable {G : Type*} [Group G] {V P W₁ W₂ X : Subgroup G}

/-- An actor normalizing both inputs normalizes their literal commutator. -/
theorem normalizes_commutator (h₁ : X ≤ normalizer (W₁ : Set G))
    (h₂ : X ≤ normalizer (W₂ : Set G)) : X ≤ normalizer ((⁅W₁, W₂⁆ : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (h₁ hx), mem_normalizer_iff_map_conj_eq.mp (h₂ hx)]

/-- With the source mutual normalization, the commutator lies in the actual
intersection, so abelianness of P and V makes it central in the generated group. -/
theorem commutator_central [IsMulCommutative V] [IsMulCommutative P]
    (hVP : V ≤ normalizer (P : Set G)) (hPV : P ≤ normalizer (V : Set G))
    (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ P) :
    ⁅W₁, W₂⁆ ≤ V ⊓ P ∧
      ⁅W₁, W₂⁆ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by
  have hc : ⁅W₁, W₂⁆ ≤ V ⊓ P :=
    (commutator_mono h₁ h₂).trans (le_inf
      (le_normalizer_iff_commutator_le_left.mp hPV)
      (le_normalizer_iff_commutator_le_right.mp hVP))
  have hv : V ≤ centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hp : P ≤ centralizer (P : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcenter : V ⊔ P ≤ centralizer ((V ⊓ P : Subgroup G) : Set G) :=
    sup_le (hv.trans (centralizer_le inf_le_left)) (hp.trans (centralizer_le inf_le_right))
  exact ⟨hc, hc.trans ((le_centralizer_iff.mp hcenter).trans
    (centralizer_le (sup_le_sup h₁ h₂)))⟩
end Commutators

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
