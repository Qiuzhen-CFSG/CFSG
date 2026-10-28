module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymplecticFour
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
/-!
# Natural symplectic coordinates preserve both parabolic types

A group mark and an intertwining binary linear equivalence suffice to place
all ambient conjugations in the natural-module normalizer. Its established
diagram preservation gives two proper Sylow-invariant parabolics, excluding
minimal parabolicity. No identification of the full endomorphism field is
required. This form applies directly to the B.5.1 central quotient.

Source: Aschbacher–Smith, B.6.9, printed p.116.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
variable {G F V : Type*} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- The original full action preserves the two symplectic parabolic types. -/
theorem symplectic_coordinates_preserveDiagram
    (L : Subgroup G) [L.Normal] (ρ : Representation (ZMod 2) G V)
    (e : L ≃* Sp F) (f : V ≃ₗ[ZMod 2] Vector F)
    (he : ∀ (l : L) v, f (ρ (l : G) v) = symplecticNatural 2 (e l) (f v))
    (hcard : 2 < Nat.card F) (g : G) : PreservesDiagram (extensionAction L e.symm g) := by
  let a : G →* (Vector F ≃ₗ[ZMod 2] Vector F) :=
    linearAction (f.conjRingEquiv.toMonoidHom.comp ρ)
  have ha (l : L) : a l = SymplecticNaturalNormalizer.naturalHom (e l) := by
    apply LinearEquiv.ext
    intro v
    change f (ρ l (f.symm v)) = _
    rw [he,f.apply_symm_apply]
    rfl
  have him : L.map a = naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      rw [show a l = _ from ha ⟨l,hl⟩]
      exact SymplecticNaturalNormalizer.naturalHom_mem hcard _
    · rintro _ ⟨l,rfl⟩
      let x := e.symm l.val
      refine ⟨x,x.property,?_⟩
      have hx := ha x
      rw [e.apply_symm_apply] at hx
      exact hx
  have hn : a g ∈ naturalNormalizer := by
    change a g ∈ normalizer (naturalDerivedImage (F := F))
    rw [← him]
    exact L.le_normalizer_map a (mem_map_of_mem a (by rw [L.normalizer_eq_top]; trivial))
  have hc : SymplecticNaturalNormalizer.conjugation hcard ⟨a g,hn⟩ =
      extensionAction L e.symm g := by
    apply MulEquiv.ext
    intro x
    apply SymplecticNaturalNormalizer.naturalHom_injective
    rw [SymplecticNaturalNormalizer.conjugation_apply]
    have hx (y : Sp F) : a (e.symm y).val = SymplecticNaturalNormalizer.naturalHom y := by
      simpa only [e.apply_symm_apply] using ha (e.symm y)
    rw [← hx,← hx]
    change a g * a _ * (a g)⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,extensionAction_apply]
  rw [← hc]
  exact SymplecticNaturalNormalizer.conjugation_preservesDiagram hcard _

/-- Actual natural Sp4 coordinates exclude a minimal parabolic over an ambient Sylow. -/
theorem not_minimalParabolic_of_symplectic_coordinates
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤) (ρ : Representation (ZMod 2) G V)
    (e : L ≃* Sp F) (f : V ≃ₗ[ZMod 2] Vector F)
    (he : ∀ (l : L) v, f (ρ (l : G) v) = symplecticNatural 2 (e l) (f v))
    (hcard : 2 < Nat.card F) : ¬ IsMinimalParabolicOver T ⊤ := by
  intro hp
  classical
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n:ℕ) := by
    by_contra hh
    have hh' : (n:ℕ)=1 := by have := n.pos; omega
    rw [hF,hh'] at hcard
    norm_num at hcard
  obtain ⟨S,hS,hpN,hqN⟩ := exists_sylow_normalizing_parabolic_pair hF hn' L e.symm
    (symplectic_coordinates_preserveDiagram L ρ e f he hcard)
  let j : Sp F →* G := L.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := L.subtype_injective.comp e.symm.injective
  have htop : (⊤ : Subgroup (Sp F)).map j = L := by
    rw [show j = L.subtype.comp e.symm.toMonoidHom from rfl,← Subgroup.map_map,
      map_top_of_surjective _ e.symm.surjective,← MonoidHom.range_eq_map,range_subtype]
  let P := (pointParabolic (F:=F)).map j
  let Q := (planeParabolic (F:=F)).map j
  have hPQ : P ⊔ Q = L := by
    rw [show P = pointParabolic.map j from rfl,show Q = planeParabolic.map j from rfl,
      ← Subgroup.map_sup,parabolics_sup_eq_top,htop]
  have hP : P ≠ L := fun hh => pointParabolic_ne_top
    (map_injective hj (hh.trans htop.symm))
  have hQ : Q ≠ L := fun hh => planeParabolic_ne_top
    (map_injective hj (hh.trans htop.symm))
  have hi (D : Subgroup (Sp F)) (hD : unipotent ≤ D) : L ⊓ (S : Subgroup G) ≤ D.map j := by
    rintro x ⟨hxL,hxS⟩
    have hx : e ⟨x,hxL⟩ ∈ unipotent := by
      rw [← hS]
      change (e.symm (e ⟨x,hxL⟩)).val ∈ S
      rw [e.symm_apply_apply]
      exact hxS
    exact ⟨e ⟨x,hxL⟩,hD hx,congrArg Subtype.val (e.symm_apply_apply ⟨x,hxL⟩)⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G T S
  let a := MulAut.conj g
  have hTS : (T : Subgroup G).map a.toMonoidHom = S := congrArg Sylow.toSubgroup hg
  have hL : L.map a.toMonoidHom = L := normal_iff_map_conj_eq.mp (inferInstance : L.Normal) g
  have hgenS : L ⊔ (S : Subgroup G) = ⊤ := by
    have hh := congrArg (map a.toMonoidHom) hgen
    simpa only [Subgroup.map_sup,hL,hTS,map_top_of_surjective a.toMonoidHom a.surjective] using hh
  have hps : IsMinimalParabolicOver S ⊤ := by
    have hh := minimalParabolic_map_of_kernel_le_core T hp a.toMonoidHom a.surjective
      (by rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]; exact bot_le)
    have hS' : T.mapSurjective (f:=a.toMonoidHom) a.surjective = S := Sylow.ext hTS
    rwa [hS'] at hh
  exact (not_minimalParabolic_of_two_overgroups S L P Q hgenS hPQ hP hQ hpN hqN
    (hi pointParabolic (unipotent_le_borel.trans inf_le_left))
    (hi planeParabolic (unipotent_le_borel.trans inf_le_right))) hps
end CFSG.Quasithin.ChapterB
