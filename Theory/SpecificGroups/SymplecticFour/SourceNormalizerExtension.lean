module
public import Theory.GroupTheory.Amalgam.NormalBaseAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel.Parabolics
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Native restriction and coherent lifts of marked symplectic actions

The automorphisms fixing both actual parabolics restrict injectively to the
marked amalgam: the parabolics generate Sp₄(F). Consequently pointwise
extendibility of a group action on this amalgam forces a unique homomorphic
lift. The same result holds with the endpoint orientation reversed.

Conjugation by the full Borel gives flag automorphisms. In nonbinary
characteristic two these are exactly the inner flag automorphisms: an
inner automorphism fixing a parabolic fixes its solvable residual, whose
native normalizer is that parabolic. No automorphism classification or
existence of extensions of arbitrary amalgam automorphisms is asserted.

This is the native restriction boundary in the symplectic specialization
of Aschbacher–Smith 5.3.2 and F.4.3, printed pp.659 and 274 of
`refs/quasithin.pdf`. The source application constructs a faithful marked
action; membership of its values in this restriction image remains necessary.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
variable (F : Type*) [Field F]

abbrev diagram := RankTwoAmalgam.ofSubgroups
  (pointParabolic (F := F)) borel planeParabolic inf_le_left inf_le_right

def flagAutomorphisms : Subgroup (MulAut (Sp F)) :=
  MulAction.stabilizer (MulAut (Sp F)) (pointParabolic (F := F)) ⊓
    MulAction.stabilizer (MulAut (Sp F)) (planeParabolic (F := F))

variable {F}
theorem flagAutomorphisms_mem (a : MulAut (Sp F)) :
    a ∈ flagAutomorphisms F ↔
      pointParabolic.map a.toMonoidHom = pointParabolic ∧
      planeParabolic.map a.toMonoidHom = planeParabolic := Iff.rfl

def restriction : flagAutomorphisms F →* RankTwoAmalgam.Iso (diagram F) (diagram F) where
  toFun a := RankTwoAmalgam.pairRestriction pointParabolic planeParabolic a.val a.property.1 a.property.2
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

theorem restriction_injective : Function.Injective (restriction (F := F)) := by
  intro a b he
  apply Subtype.ext
  exact (RankTwoAmalgam.pairRestriction_eq_iff _ _ parabolics_sup_eq_top
    a.val b.val a.property.1 a.property.2 b.property.1 b.property.2).mp he

theorem flag_preservesDiagram (a : flagAutomorphisms F) :
    DiagramAutomorphisms.PreservesDiagram a.val := by
  constructor
  · refine ⟨1, ?_⟩
    rw [map_one]
    change pointParabolic.map a.val.toMonoidHom = pointParabolic.map (MonoidHom.id (Sp F))
    rw [Subgroup.map_id]
    exact a.property.1
  · refine ⟨1, ?_⟩
    rw [map_one]
    change planeParabolic.map a.val.toMonoidHom = planeParabolic.map (MonoidHom.id (Sp F))
    rw [Subgroup.map_id]
    exact a.property.2

/-- Conjugation by the actual common Borel gives native flag automorphisms. -/
def innerBorel : borel (F := F) →* flagAutomorphisms F :=
  (MulAut.conj.comp borel.subtype).codRestrict _ (fun g =>
    ⟨mem_normalizer_iff_map_conj_eq.mp (pointParabolic.le_normalizer g.property.1),
     mem_normalizer_iff_map_conj_eq.mp (planeParabolic.le_normalizer g.property.2)⟩)

theorem innerBorel_apply (b : borel (F := F)) :
    (innerBorel b).val = MulAut.conj b.val := rfl

/-- In nonbinary characteristic two, an inner flag automorphism comes from
precisely the full Borel, not merely its unipotent Sylow. -/
theorem inner_flag_iff [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (g : Sp F) :
    MulAut.conj g ∈ flagAutomorphisms F ↔ g ∈ borel := by
  constructor
  · intro hg
    have hp := DiagramAutomorphisms.pointLocal_map hF hn (MulAut.conj g) hg.1
    have hq := DiagramAutomorphisms.planeLocal_map hF hn (MulAut.conj g) hg.2
    exact ⟨(DiagramAutomorphisms.pointLocal_normalizer hF hn) ▸
      mem_normalizer_iff_map_conj_eq.mpr hp,
      (DiagramAutomorphisms.planeLocal_normalizer hF hn) ▸
      mem_normalizer_iff_map_conj_eq.mpr hq⟩
  · intro hg
    exact (innerBorel (⟨g,hg⟩ : borel (F := F))).property

/-- Restriction in the other orientation changes both endpoint maps. -/
def reverseRestriction : flagAutomorphisms F →*
    RankTwoAmalgam.Iso (diagram F).reverse (diagram F).reverse where
  toFun a := (restriction a).reverse
  map_one' := rfl
  map_mul' _ _ := rfl

theorem reverseRestriction_injective : Function.Injective (reverseRestriction (F := F)) := by
  intro a b he
  apply restriction_injective
  exact congrArg (fun e => e.reverse) he

private theorem lift_unique {A B D : Type*} [Group A] [Group B] [Group D]
    (r : A →* B) (hr : Function.Injective r) (ρ : D →* B)
    (hρ : ∀ d, ρ d ∈ r.range) : ∃! σ : D →* A, r.comp σ = ρ := by
  choose f hf using hρ
  let σ : D →* A :=
    { toFun := f
      map_one' := hr (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hr (by rw [hf, map_mul, map_mul, hf, hf]) }
  refine ⟨σ, ?_, ?_⟩
  · ext x : 1
    exact hf x
  · intro τ hτ
    ext x : 1
    apply hr
    exact (congrArg (fun a : D →* B => a x) hτ).trans (hf x).symm

variable {D : Type*} [Group D]
/-- Pointwise extendibility is enough: generation forces coherence and uniqueness. -/
theorem existsUnique_lift (ρ : D →* RankTwoAmalgam.Iso (diagram F) (diagram F))
    (hρ : ∀ d, ρ d ∈ (restriction (F := F)).range) :
    ∃! σ : D →* flagAutomorphisms F, restriction.comp σ = ρ :=
  lift_unique restriction restriction_injective ρ hρ

/-- The identical unique lifting assertion retains the reversed marking. -/
theorem existsUnique_reverse_lift
    (ρ : D →* RankTwoAmalgam.Iso (diagram F).reverse (diagram F).reverse)
    (hρ : ∀ d, ρ d ∈ (reverseRestriction (F := F)).range) :
    ∃! σ : D →* flagAutomorphisms F, reverseRestriction.comp σ = ρ :=
  lift_unique reverseRestriction reverseRestriction_injective ρ hρ

theorem lift_injective (ρ : D →* RankTwoAmalgam.Iso (diagram F) (diagram F))
    (hρ : Function.Injective ρ) (σ : D →* flagAutomorphisms F)
    (hσ : restriction.comp σ = ρ) : Function.Injective σ := by
  intro x y hxy
  apply hρ
  rw [← hσ]
  exact congrArg restriction hxy

end Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
