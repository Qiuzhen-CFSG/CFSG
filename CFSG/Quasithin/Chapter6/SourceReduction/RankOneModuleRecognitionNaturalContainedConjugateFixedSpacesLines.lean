module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesActions
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Transporting natural field lines to the original Sylow line

The actual quotient marking turns the Sylow intersection's fixed subgroup
into an F-linear space. Its order identifies it as a line. Transitivity of
SL₂ on nonzero vectors supplies a line transporter, lifted through the
literal map L → L/O₂(L). Equivariance then gives the required ambient
conjugation equality, with the same lifted element of L.

Source: Aschbacher--Smith 6.1.13(2), printed p.670 (PDF p.687).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] {L B : Subgroup G}
  {F : Type} [Field F]

/-- The field-linear fixed space of the actual Sylow intersection, in the given marking. -/
def sylowSpace (T : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Submodule F (Fin 2 → F) where
  carrier := {v | ∀ l : L, (l : G) ∈ T →
    (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec v = v}
  zero_mem' := by intro l _; exact map_zero (Matrix.SpecialLinearGroup.toLin' _)
  add_mem' := by
    intro v w hv hw l hl
    rw [Matrix.mulVec_add, hv l hl, hw l hl]
  smul_mem' := by
    intro c v hv l hl
    rw [Matrix.mulVec_smul, hv l hl]

theorem mem_sylowSpace_iff (T : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (v : Fin 2 → F) :
    v ∈ sylowSpace T e ↔
      v ∈ coordinateSpace f (B ⊓ centralizer (T ⊓ L : Set G)) := by
  have he (l : L) := hf l (f.symm (Multiplicative.ofAdd v))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at he
  constructor
  · intro hv
    refine ⟨(f.symm _).property, mem_centralizer_iff.mpr ?_⟩
    intro l hl
    have hh := he ⟨l, hl.2⟩
    rw [hv ⟨l, hl.2⟩ hl.1] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  · intro hv l hl
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hv.2 (l : G) ⟨hl, l.property⟩)

variable [Finite F]

theorem fieldLine_transport
    (T : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (hZcard : Nat.card (B ⊓ centralizer (T ⊓ L : Set G) : Subgroup G) = Nat.card F)
    {U : Subgroup G} (hUB : U ≤ B)
    (X : Submodule F (Fin 2 → F)) (hX : Module.finrank F X = 1)
    (hXU : X.toAddSubgroup = coordinateSpace f U) :
    ∃ l ∈ L, U = (B ⊓ centralizer (T ⊓ L : Set G)).map (MulAut.conj l).toMonoidHom := by
  let W := sylowSpace T e
  have hW : W.toAddSubgroup = coordinateSpace f (B ⊓ centralizer (T ⊓ L : Set G)) :=
    AddSubgroup.ext (mem_sylowSpace_iff T e f hf)
  have hWcard : Nat.card W = Nat.card F := by
    change Nat.card W.toAddSubgroup = Nat.card F
    rw [hW, coordinateSpace_card f inf_le_left, hZcard]
  have hWdim : Module.finrank F W = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F W = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank (K := F) (V := W), hWcard, pow_one]
  obtain ⟨z, hz, hz0⟩ := W.ne_bot_iff.mp (Submodule.isAtom_iff_finrank_eq_one.mpr hWdim).ne_bot
  obtain ⟨v, hv, hv0⟩ := X.ne_bot_iff.mp (Submodule.isAtom_iff_finrank_eq_one.mpr hX).ne_bot
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq F z v hz0 hv0
  have hWspan := eq_span_singleton_of_mem_of_finrank_eq_one hWdim hz hz0
  have hXspan := eq_span_singleton_of_mem_of_finrank_eq_one hX hv hv0
  have hmap : W.map (Matrix.SpecialLinearGroup.toLin' g).toLinearMap = X := by
    rw [hWspan, hXspan, Submodule.map_span, Set.image_singleton]
    congr 1
    exact congrArg Set.singleton hg
  obtain ⟨q, hq⟩ := e.surjective g
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hlg : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl, hq]
  refine ⟨l, l.property, ?_⟩
  apply le_antisymm
  · intro x hx
    let w := Multiplicative.toAdd (f ⟨x, hUB hx⟩)
    have hw : w ∈ X := by
      change w ∈ X.toAddSubgroup
      rw [hXU]
      simpa [w] using hx
    rw [← hmap] at hw
    obtain ⟨y, hy, he⟩ := hw
    have hyZ : (f.symm (Multiplicative.ofAdd y) : G) ∈
        B ⊓ centralizer (T ⊓ L : Set G) := by
      exact (mem_sylowSpace_iff T e f hf y).mp hy
    refine ⟨f.symm (Multiplicative.ofAdd y), hyZ, ?_⟩
    have hh := hf l (f.symm (Multiplicative.ofAdd y))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, hlg] at hh
    change g.val.mulVec y = w at he
    rw [he] at hh
    simpa [w] using hh.symm
  · rintro x ⟨y, hy, rfl⟩
    let w := Multiplicative.toAdd (f ⟨y, hy.1⟩)
    have hw : w ∈ W := by
      apply (mem_sylowSpace_iff T e f hf w).mpr
      simpa [w] using hy
    have hwX : g.val.mulVec w ∈ X := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    change g.val.mulVec w ∈ X.toAddSubgroup at hwX
    rw [hXU] at hwX
    have hh := hf l ⟨y, hy.1⟩
    rw [hlg] at hh
    change (f.symm (Multiplicative.ofAdd (g.val.mulVec w)) : G) ∈ U at hwX
    rwa [hh] at hwX

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
