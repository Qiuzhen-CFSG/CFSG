module

public import Theory.Representation.SL2FourNaturalOrbits.PlaneTransport
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice

/-!
# The two natural factors of the upper Borel of SL₂(4)

The normal upper root group is the actual two-core. Its common fixed space
is F₄e₁. The diagonal torus is transitive on the three nonzero vectors of
this binary plane. The literal quotient has the same transitivity property,
by the existing plane-stabilizer calculation. Consequently both factors
are irreducible and noncentral, including after any surjective actor pullback.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
14.7.70, printed p.1074 (PDF p.1091). These are model calculations; the
marking of the source quotient and the chief-series assembly are separate.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.BorelFactors
open Subgroup Matrix.SpecialLinearGroup

/-- The literal upper triangular Borel, equivalently the upper-root normalizer. -/
abbrev B0 : Subgroup SL := rankOneBorel F

/-- Its actual upper unipotent subgroup in SL₂(4). -/
abbrev U0 : Subgroup SL := upperUnipotent F

/-- Restricted natural action of the Borel. -/
def natural : Representation (ZMod 2) B0 V :=
  PointCommutator.representation.comp B0.subtype

theorem upper_eq_transvection (a : F) :
    upper a = transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one a := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [upper, transvection_coe]

theorem mem_U0 (g : SL) : g ∈ U0 ↔ ∃ a : F, upper a = g := by
  simp only [U0, mem_upperUnipotent, upper_eq_transvection]

theorem twoCoreIn_B0 : B0.pCoreIn 2 = U0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := upperUnipotentSylow F 2
  have hUB : U0 ≤ B0 := U0.le_normalizer
  apply le_antisymm
  · have h := pCoreIn_le_sylow B0 (P.subtype hUB)
    change B0.pCoreIn 2 ≤ (U0.subgroupOf B0).map B0.subtype at h
    rwa [map_subgroupOf_eq_of_le hUB] at h
  · exact le_pCoreIn_of_normalizes P.isPGroup' hUB le_rfl

/-- The selected plane is intrinsically the fixed space of the actual core. -/
theorem mem_upperFixed_iff_core (v : V) :
    v ∈ upperFixed ↔ ∀ g ∈ B0.pCoreIn 2, action g v = v := by
  rw [twoCoreIn_B0]
  constructor
  · intro hv g hg
    obtain ⟨a, rfl⟩ := (mem_U0 g).mp hg
    exact (upper_fixed_iff v).mpr ((mem_upperFixed v).mp hv) a
  · intro h
    apply (mem_upperFixed v).mpr
    exact (upper_fixed_iff v).mp (fun a => h (upper a) ((mem_U0 _).mpr ⟨a, rfl⟩))

/-- Preserving the chosen plane is exactly membership in the upper Borel. -/
theorem preserves_upperFixed_iff (g : SL) :
    (∀ v ∈ upperFixed, action g v ∈ upperFixed) ↔ g ∈ B0 := by
  rw [mem_rankOneBorel_iff]
  constructor
  · intro h
    have hm := (mem_upperFixed _).mp (h (![1, 0] : V) ((mem_upperFixed _).mpr rfl))
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hm
  · intro hg v hv
    apply (mem_upperFixed _).mpr
    have hv1 := (mem_upperFixed v).mp hv
    simp [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hg, hv1]

/-- The invariant F₄-line, as a binary subrepresentation. -/
def line : Subrepresentation natural where
  toSubmodule := upperFixed
  apply_mem_toSubmodule g := (preserves_upperFixed_iff g.val).mpr g.property

/-- The representation on the actual quotient by the line. -/
abbrev quotient := line.quotientRepresentation

/-- Torus transitivity on the nonzero vectors of F₄e₁. -/
theorem line_transitive (v w : line.toSubmodule) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : B0, line.toRepresentation g v = w := by
  have hv1 := (mem_upperFixed v.val).mp v.property
  have hw1 := (mem_upperFixed w.val).mp w.property
  have hv0 : v.val 0 ≠ 0 := by
    intro he
    apply hv
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [he, hv1]
  have hw0 : w.val 0 ≠ 0 := by
    intro he
    apply hw
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [he, hw1]
  let a := w.val 0 / v.val 0
  have ha : a ≠ 0 := div_ne_zero hw0 hv0
  refine ⟨⟨diag2 a ha, diag_mem_rankOneBorel a ha⟩, ?_⟩
  apply Subtype.ext
  change action (diag2 a ha) v.val = w.val
  funext i
  fin_cases i <;>
    simp [action_apply, diag2_coe', Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      hv1, hw1, a, div_mul_cancel₀ _ hv0]

/-- Transitivity on the nonzero cosets of the literal natural quotient. -/
theorem quotient_transitive (v w : V ⧸ line.toSubmodule) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : B0, quotient g v = w := by
  obtain ⟨v, rfl⟩ := upperFixed.mkQ_surjective v
  obtain ⟨w, rfl⟩ := upperFixed.mkQ_surjective w
  obtain ⟨g, hg, he⟩ := plane_quotient_transitive upperFixed card_upperFixed v w
    (fun h => hv ((Submodule.Quotient.mk_eq_zero _).mpr h))
    (fun h => hw ((Submodule.Quotient.mk_eq_zero _).mpr h))
  refine ⟨⟨g, (preserves_upperFixed_iff g).mp hg⟩, ?_⟩
  exact ((Submodule.Quotient.eq upperFixed).mpr he).symm

/-- Transitivity on nonzero vectors implies irreducibility for the specified actor. -/
theorem irreducible_of_transitive {K M : Type*} [Group K] [AddCommGroup M]
    [Module (ZMod 2) M] [Nontrivial M] (ρ : Representation (ZMod 2) K M)
    (h : ∀ v w : M, v ≠ 0 → w ≠ 0 → ∃ g, ρ g v = w) : IsIrreducible ρ := by
  classical
  refine ⟨fun S => ?_⟩
  by_cases hs : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hs)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · subst w
      exact S.toSubmodule.zero_mem
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
    obtain ⟨g, rfl⟩ := h v w hv0 hw
    exact S.apply_mem_toSubmodule g hv

instance line_nontrivial : Nontrivial line.toSubmodule := by
  apply (Submodule.nontrivial_iff_ne_bot).mpr
  intro h
  have hm : (![1, 0] : V) ∈ line.toSubmodule := (mem_upperFixed _).mpr rfl
  rw [h] at hm
  have he := congrFun (show (![1, 0] : V) = 0 from hm) 0
  simp at he

instance quotient_nontrivial : Nontrivial (V ⧸ line.toSubmodule) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  intro h
  have hm : (![0, 1] : V) ∈ line.toSubmodule := by rw [h]; trivial
  have he := (mem_upperFixed _).mp hm
  simp at he

instance line_irreducible : IsIrreducible line.toRepresentation :=
  irreducible_of_transitive _ line_transitive

instance quotient_irreducible : IsIrreducible quotient :=
  irreducible_of_transitive _ quotient_transitive

/-- The diagonal cubic moves an actual vector of the invariant line. -/
theorem line_noncentral : ∃ g v, line.toRepresentation g v ≠ v := by
  let c : B0 := ⟨PointCommutator.cubic, (mem_rankOneBorel_iff _).mpr rfl⟩
  let v : line.toSubmodule := ⟨![1, 0], (mem_upperFixed _).mpr rfl⟩
  refine ⟨c, v, ?_⟩
  intro h
  have he := congrArg (fun x : line.toSubmodule => x.val 0) h
  have hn : action PointCommutator.cubic (![1, 0] : V) 0 ≠ 1 := by decide +kernel
  exact hn he

/-- The same cubic moves an actual coset in the quotient. -/
theorem quotient_noncentral : ∃ g v, quotient g v ≠ v := by
  let c : B0 := ⟨PointCommutator.cubic, (mem_rankOneBorel_iff _).mpr rfl⟩
  refine ⟨c, upperFixed.mkQ (![0, 1] : V), ?_⟩
  intro h
  have he := (mem_upperFixed _).mp ((Submodule.Quotient.eq upperFixed).mp h)
  have hn : (action PointCommutator.cubic (![0, 1] : V) - (![0, 1] : V)) 1 ≠ 0 := by
    decide +kernel
  exact hn he

/-- The two factors have binary dimension two, in addition to their action data. -/
theorem line_finrank : Module.finrank (ZMod 2) line.toSubmodule = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := line.toSubmodule)
  rw [show Nat.card line.toSubmodule = 4 from card_upperFixed,
    Nat.card_eq_fintype_card, ZMod.card] at hc
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm

theorem quotient_finrank : Module.finrank (ZMod 2) (V ⧸ line.toSubmodule) = 2 := by
  have h := Submodule.finrank_quotient_add_finrank line.toSubmodule
  rw [line_finrank, finrank_vector] at h
  omega

end Representation.SL2FourNatural.BorelFactors
