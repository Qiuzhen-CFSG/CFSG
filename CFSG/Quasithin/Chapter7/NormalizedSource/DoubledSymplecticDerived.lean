module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticLocal
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SymmetricRestriction
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticLocal

/-!
# The genuine binary derived symplectic pair

Restriction from Aut(S₆) onto Aut(A₆) is surjective: its image contains the
natural symmetric group and the exceptional outer automorphism. The literal
polar isomorphism therefore extends every automorphism of Sp₄(2)′ to Sp₄(2).
The seed nonisomorphism forces that extension to move the diagram, giving
graph-pair coordinates while preserving both original axes.

A faithful ambient action normalizing the actual derived image embeds into
its full binary linear normalizer. H.7 then gives m ≥ 3n and a < 2n, also
for n = 1. The chosen-module application is in
NonFFSourceDoubledSymplecticSix. Global weak closure is a separate obligation.

Source: Aschbacher--Smith H.7 and 7.3.2--7.3.5, printed pp.388--389,698--699,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open SymplecticConjugatePair SymplecticConjugatePair.Ambient
namespace CFSG.Quasithin.Chapter7.NormalizedSource

private theorem binary_symmetricRestriction_surjective :
    Function.Surjective AlternatingSix.ShadowLocal.symmetricRestriction := by
  open AlternatingSix.ShadowLocal GLS3.Chapter5 in
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_natural_lt
  refine lt_of_le_of_ne ?_ ?_
  · rintro a ⟨s,rfl⟩
    exact ⟨MulAut.conj s,symmetricRestriction_conj s⟩
  · intro he
    have ho : outerAltAut ∈ symmetricRestriction.range := ⟨outerAut, by ext x : 2; rfl⟩
    rw [← he] at ho
    obtain ⟨s,hs⟩ := ho
    have hc := congrArg (fun a : MulAut A6 => (a baseThreeCycle).val.cycleType) hs
    change (s * baseThreeCycle.val * s⁻¹).cycleType = _ at hc
    rw [Equiv.Perm.cycleType_conj,baseThreeCycle_isThreeCycle,outerAltAut_base_cycleType] at hc
    have hh := congrArg Multiset.card hc
    norm_num at hh

/-- Every automorphism of the genuine binary derived group extends to the
full matrix group, with its restriction recorded pointwise. -/
theorem doubledSymplectic_binary_derived_extension
    (a : MulAut (commutator (Sp (ZMod 2)))) :
    ∃ τ : MulAut (Sp (ZMod 2)), ∀ x : commutator (Sp (ZMod 2)),
      τ x.val = (a x).val := by
  let e := Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.symmetricSymplecticEquiv
  let d := Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.alternatingDerivedEquiv
  obtain ⟨b,hb⟩ := binary_symmetricRestriction_surjective (MulAut.congr d.symm a)
  refine ⟨MulAut.congr e b, ?_⟩
  intro x
  obtain ⟨y,rfl⟩ := d.surjective x
  have hh := congrArg Subtype.val (DFunLike.congr_fun hb y)
  change b y.val = (d.symm (a (d y))).val at hh
  have hd (z : alternatingGroup (Fin 6)) : (d z).val = e z.val := rfl
  change e (b (e.symm (d y).val)) = (a (d y)).val
  rw [hd,e.symm_apply_apply,hh,← hd,d.apply_symm_apply]

theorem doubledSymplectic_derived_pair_coordinates {J U : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (q : J →* commutator (Sp (ZMod 2)))
    (e : U ≃ₗ[ZMod 2] Vector (ZMod 2))
    (he : ∀ j v, e (ρ j v) = symplecticDerivedNatural 2 (q j) (e v))
    (α : MulAut J) (a : MulAut (commutator (Sp (ZMod 2))))
    (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    ∃ E : (U × U) ≃ₗ[ZMod 2] Space (ZMod 2),
      (∀ j v, E ((ρ.prod (ρ.comp α.toMonoidHom)) j v) =
        derivedPair graphAut (q j) (E v)) ∧
      (∀ v, (E v).1 = 0 ↔ v.1 = 0) ∧
      (∀ v, (E v).2 = 0 ↔ v.2 = 0) := by
  obtain ⟨τ,hτ⟩ := doubledSymplectic_binary_derived_extension a
  let q' := (commutator (Sp (ZMod 2))).subtype.comp q
  have ha' (j : J) : τ (q' j) = q' (α j) :=
    (hτ (q j)).trans (congrArg Subtype.val (ha j))
  obtain ⟨_,E,hE,h1,h2⟩ := doubledSymplectic_pair_coordinates ρ q' e he α τ ha' hne
  exact ⟨E,hE,h1,h2⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The full faithful ambient actor is controlled by its normal derived
image, including the binary case where that image is A₆. -/
theorem doubledSymplectic_parameters_of_marked_derived_range
    {H J U : Type*} [Group H] [Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* commutator (Sp F)) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] Space F)
    (hE : ∀ j v, E (ρ (i j) v) = derivedPair graphAut (q j) (E v))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    3*n ≤ ChapterE.moduleM ρ ∧ ChapterE.moduleA ρ < (2*n : ℕ) := by
  let γ : Representation (ZMod 2) H (Space F) := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : linearAction γ (i j) = linearAction (derivedPair graphAut) (q j) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    exact (he (i j) v).symm.trans (hE j v)
  have himage : i.range.map (linearAction γ) = derivedImage (graphAut (F := F)) := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,(hres j).symm⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨j,rfl⟩ := hq x
      exact ⟨i j,⟨j,rfl⟩,hres j⟩
  have hm (g : H) : linearAction γ g ∈ pairedNormalizer (graphAut (F := F)) := by
    change linearAction γ g ∈ normalizer (derivedImage (graphAut (F := F)) : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map (linearAction γ)
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let f : H →* pairedNormalizer (graphAut (F := F)) := (linearAction γ).codRestrict _ hm
  have hf : Function.Injective f := by
    intro x y hxy
    exact linearAction_injective γ hγ (congrArg Subtype.val hxy)
  have hfE : ∀ g v, E (ρ g v) = normalizerAction graphAut (f g) (E v) := he
  have hs := doubledSymplectic_normalizer_parameters (graphAut (F := F))
    graphAut_not_preservesDiagram hF hn
  exact ⟨hs.1.trans (moduleM_ge_of_embedding _ _ f hf E hfE),
    (ChapterE.moduleA_le_of_equivariant_injective _ _ f hf E hfE).trans_lt hs.2⟩

end CFSG.Quasithin.Chapter7.NormalizedSource
