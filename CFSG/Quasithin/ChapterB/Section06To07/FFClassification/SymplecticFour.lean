module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.NaturalRatios.Ambient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantParabolicPair

/-!
# Natural Sp4 actions exclude minimal parabolicity

The natural binary module forces every ambient conjugation to preserve the
symplectic diagram. Extend the standard unipotent group to one ambient Sylow;
this Sylow normalizes both actual point and plane parabolics. Conjugating the
same pair and Sylow to the prescribed Sylow retains both normalizations and
their common Sylow intersection. Their proper overgroups contradict uniqueness
of the maximal Sylow overgroup.

Source: Aschbacher--Smith B.6.9, printed p.116. The ambient representation and
its actual natural identification supply diagram preservation; no separate
parabolic-invariance or semilinear-action assumption is used.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open ChapterK.Symplectic
variable {G F V : Type*} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual natural action supplies two proper Sylow-invariant parabolics. -/
theorem exists_sylow_invariant_symplectic_parabolics
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (ρ : Representation (ZMod 2) G V)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype))
    (hcard : 2 < Nat.card F) :
    ∃ P Q : Subgroup G, P ⊔ Q = L ∧ P ≠ L ∧ Q ≠ L ∧ P ≠ Q ∧
      (T : Subgroup G) ≤ normalizer (P : Set G) ∧
      (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      L ⊓ (T : Subgroup G) ≤ P ∧ L ⊓ (T : Subgroup G) ≤ Q := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 1 < (n : ℕ) := by
    by_contra hh
    have hh' : (n : ℕ) = 1 := by have := n.pos; omega
    rw [hF, hh'] at hcard
    norm_num at hcard
  let e := h.groupEquiv.symm
  let f : Sp F →* G := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  have hftop : (⊤ : Subgroup (Sp F)).map f = L := by
    rw [show f = L.subtype.comp e.toMonoidHom from rfl, ← map_map,
      map_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨S, hS, hpN, hqN⟩ := exists_sylow_normalizing_parabolic_pair hF hn' L e
    (h.preservesDiagram hcard)
  let P₀ := (pointParabolic (F := F)).map f
  let Q₀ := (planeParabolic (F := F)).map f
  have hPQ₀ : P₀ ⊔ Q₀ = L := by
    rw [show P₀ = pointParabolic.map f from rfl,
      show Q₀ = planeParabolic.map f from rfl, ← Subgroup.map_sup, parabolics_sup_eq_top, hftop]
  have hP₀ : P₀ ≠ L := by
    intro he
    exact pointParabolic_ne_top (map_injective hf (he.trans hftop.symm))
  have hQ₀ : Q₀ ≠ L := by
    intro he
    exact planeParabolic_ne_top (map_injective hf (he.trans hftop.symm))
  have hint (D : Subgroup (Sp F)) (hd : unipotent ≤ D) :
      L ⊓ (S : Subgroup G) ≤ D.map f := by
    rintro x ⟨hxL, hxS⟩
    have hx : e.symm ⟨x, hxL⟩ ∈ unipotent := by
      rw [← hS]
      change (e (e.symm ⟨x, hxL⟩)).val ∈ S
      rw [e.apply_symm_apply]
      exact hxS
    refine ⟨e.symm ⟨x, hxL⟩, hd hx, ?_⟩
    change (e (e.symm ⟨x, hxL⟩)).val = x
    rw [e.apply_symm_apply]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let a := MulAut.conj g
  have hST : (S : Subgroup G).map a.toMonoidHom = T := by
    exact congrArg Sylow.toSubgroup hg
  have hL : L.map a.toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [L.normalizer_eq_top]; trivial)
  let P := P₀.map a.toMonoidHom
  let Q := Q₀.map a.toMonoidHom
  have hPQ : P ⊔ Q = L := by
    change P₀.map _ ⊔ Q₀.map _ = _
    rw [← Subgroup.map_sup, hPQ₀, hL]
  have hP : P ≠ L := by
    intro he
    exact hP₀ (map_injective a.injective (he.trans hL.symm))
  have hQ : Q ≠ L := by
    intro he
    exact hQ₀ (map_injective a.injective (he.trans hL.symm))
  refine ⟨P, Q, hPQ, hP, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hP (by simpa only [← he, sup_idem] using hPQ)
  · have hh := map_mono (f := a.toMonoidHom) hpN
    rwa [hST, map_equiv_normalizer_eq] at hh
  · have hh := map_mono (f := a.toMonoidHom) hqN
    rwa [hST, map_equiv_normalizer_eq] at hh
  · have hh := map_mono (f := a.toMonoidHom)
      (hint pointParabolic (unipotent_le_borel.trans inf_le_left))
    rwa [map_inf _ _ _ a.injective, hL, hST] at hh
  · have hh := map_mono (f := a.toMonoidHom)
      (hint planeParabolic (unipotent_le_borel.trans inf_le_right))
    rwa [map_inf _ _ _ a.injective, hL, hST] at hh

/-- A natural Sp4 supplement over a field of order greater than two cannot
occur in a minimal parabolic. -/
theorem not_minimalParabolic_of_natural_symplectic_four
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (ρ : Representation (ZMod 2) G V)
    (h : NaturalIdentification (F := F) (ρ.comp L.subtype))
    (hcard : 2 < Nat.card F) : ¬ IsMinimalParabolicOver T ⊤ := by
  obtain ⟨P, Q, hPQ, hP, hQ, _, hnP, hnQ, hiP, hiQ⟩ :=
    exists_sylow_invariant_symplectic_parabolics T L ρ h hcard
  exact not_minimalParabolic_of_two_overgroups T L P Q hgen hPQ hP hQ hnP hnQ hiP hiQ

/-- The literal two-residual of a minimal parabolic has no such natural action. -/
theorem minimalParabolic_not_natural_residual_symplectic_four
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) G V) (hcard : 2 < Nat.card F) :
    ¬ Nonempty (NaturalIdentification (F := F) (ρ.comp (pResidual 2 G).subtype)) := by
  rintro ⟨h⟩
  exact not_minimalParabolic_of_natural_symplectic_four T (pResidual 2 G)
    (pResidual_sup_sylow_eq_top T) ρ h hcard hP
end CFSG.Quasithin.ChapterB
