module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.SpecificGroups.LieType.A02ParabolicSections
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Constructing the binary symplectic Levi section from seven root-word identities

The proved seven-relator presentation is isomorphic to the literal Sp₆(2)
matrix group. Evaluating its two marked generators in any group therefore
constructs a marked homomorphism from Sp₆(2). Binary simplicity makes this
map injective whenever its first generator is nonidentity.

If the two images centralize a specified noncentral involution z, the whole
image lies in C(z) = N(⟨z⟩). That normalizer is proper, and ⟨z⟩ has order two.
The actual image supplies a `NormalizerSection` with target PSp₆(2), using
the characteristic-two equivalence between Sp₆(2) and its central quotient.
The exceptional source producer verifies the seven identities for its actual
root words; this module assumes no local classification or section witness.

Sources: the ATLAS presentation S62G1-P1.M and its proved matrix comparison
in `KernelUpperBound.Faithfulness`; GLS3 §2.6; Aschbacher–Smith A.2.18,
printed p.40.
-/

public noncomputable section

namespace Theory.SpecificGroups.LieType.SourceLevi.Sp6Presentation

open Subgroup SymplecticSix
open SymplecticSix.UniversalDoubleCover

private def presentedEquiv : KernelPresentation.Presented ≃* Sp (ZMod 2) :=
  MulEquiv.ofBijective KernelPresentation.matrixMap
    ⟨KernelPresentation.matrixMap_injective, KernelPresentation.matrixMap_surjective⟩

variable {H : Type*} [Group H]

private def presentedHom (A B : H)
    (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1) :
    KernelPresentation.Presented →* H :=
  PresentedGroup.toGroup (f := fun i : Bool => cond i B A) (by
    rintro _ ⟨i, rfl⟩
    rw [KernelPresentation.relator, KernelPresentation.map_word]
    simpa only [FreeGroup.lift_apply_of, Bool.cond_false, Bool.cond_true] using rel i)

private theorem presentedHom_generator (A B : H)
    (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1) (i : Bool) :
    presentedHom A B rel (KernelPresentation.generator i) = cond i B A :=
  PresentedGroup.toGroup.of _

/-- The actual seven word identities construct a homomorphism from Sp₆(2). -/
def hom (A B : H) (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1) :
    Sp (ZMod 2) →* H :=
  (presentedHom A B rel).comp presentedEquiv.symm.toMonoidHom

/-- The first literal ATLAS matrix is sent to the specified first root word. -/
theorem hom_a (A B : H) (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1) :
    hom A B rel KernelPresentation.a = A := by
  change hom A B rel (KernelPresentation.matrixGenerator false) = A
  rw [← KernelPresentation.matrixMap_generator false]
  change presentedHom A B rel
    (presentedEquiv.symm (presentedEquiv (KernelPresentation.generator false))) = A
  rw [presentedEquiv.symm_apply_apply, presentedHom_generator]
  rfl

/-- The second literal ATLAS matrix is sent to the specified second root word. -/
theorem hom_b (A B : H) (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1) :
    hom A B rel KernelPresentation.b = B := by
  change hom A B rel (KernelPresentation.matrixGenerator true) = B
  rw [← KernelPresentation.matrixMap_generator true]
  change presentedHom A B rel
    (presentedEquiv.symm (presentedEquiv (KernelPresentation.generator true))) = B
  rw [presentedEquiv.symm_apply_apply, presentedHom_generator]
  rfl

/-- Binary simplicity makes the constructed map faithful as soon as A survives. -/
theorem hom_injective (A B : H) (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1)
    (hA : A ≠ 1) : Function.Injective (hom A B rel) := by
  let : IsSimpleGroup (PSp (ZMod 2)) := isSimpleGroup_binary
  let : IsSimpleGroup (Sp (ZMod 2)) := (EvenProjective.equiv (F := ZMod 2)).isSimpleGroup
  rcases (inferInstance : (hom A B rel).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (hom A B rel).ker_eq_bot_iff.mp hk
  · exfalso
    apply hA
    rw [← hom_a A B rel]
    change KernelPresentation.a ∈ (hom A B rel).ker
    rw [hk]
    exact mem_top _

/-- Centralization by both marked generators propagates to their actual image. -/
theorem hom_range_le_centralizer (A B z : H)
    (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1)
    (hAz : Commute A z) (hBz : Commute B z) :
    (hom A B rel).range ≤ centralizer ({z} : Set H) := by
  rintro _ ⟨g, rfl⟩
  change presentedEquiv.symm g ∈ (centralizer ({z} : Set H)).comap (presentedHom A B rel)
  apply PresentedGroup.generated_by
  intro i
  change presentedHom A B rel (KernelPresentation.generator i) ∈ centralizer ({z} : Set H)
  rw [presentedHom_generator]
  cases i
  · exact mem_centralizer_singleton_iff.mpr hAz.eq
  · exact mem_centralizer_singleton_iff.mpr hBz.eq

variable [Finite H]

/-- The actual embedded Sp₆(2) inside the proper normalizer of the specified
noncentral involution gives the required literal projective section. -/
def normalizerSection (A B z : H)
    (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1)
    (hA : A ≠ 1) (hz : orderOf z = 2) (hzC : z ∉ center H)
    (hAz : Commute A z) (hBz : Commute B z) : NormalizerSection H (PSp (ZMod 2)) := by
  have hQ : zpowers z ≠ ⊥ := by
    intro h
    have hz1 : z = 1 := by simpa only [h, mem_bot] using mem_zpowers z
    exact hzC (hz1 ▸ (center H).one_mem)
  have htwo : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hproper : normalizer (zpowers z : Set H) ≠ ⊤ := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two z hz]
    intro h
    apply hzC
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.mp (show g ∈ centralizer ({z} : Set H) by
      rw [h]
      exact mem_top _)
  let f : PSp (ZMod 2) →* H :=
    (hom A B rel).comp (EvenProjective.equiv (F := ZMod 2)).symm.toMonoidHom
  have hf : Function.Injective f :=
    (hom_injective A B rel hA).comp (EvenProjective.equiv (F := ZMod 2)).symm.injective
  have hN : f.range ≤ normalizer (zpowers z : Set H) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two z hz]
    rintro _ ⟨g, rfl⟩
    exact hom_range_le_centralizer A B z rel hAz hBz ⟨_, rfl⟩
  exact NormalizerSection.ofEmbedding (zpowers z) hQ htwo hproper f hf hN

/-- The constructed section uses exactly the cyclic subgroup of the supplied involution. -/
theorem normalizerSection_twoSubgroup (A B z : H)
    (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1)
    (hA : A ≠ 1) (hz : orderOf z = 2) (hzC : z ∉ center H)
    (hAz : Commute A z) (hBz : Commute B z) :
    (normalizerSection A B z rel hA hz hzC hAz hBz).twoSubgroup = zpowers z := by
  unfold normalizerSection
  rfl

end Theory.SpecificGroups.LieType.SourceLevi.Sp6Presentation
