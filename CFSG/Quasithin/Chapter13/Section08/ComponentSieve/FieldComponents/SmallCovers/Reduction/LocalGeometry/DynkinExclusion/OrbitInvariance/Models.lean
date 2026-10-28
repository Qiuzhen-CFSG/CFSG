module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The natural-module alternatives in F.9.18(4iii)

The groups and their actions are concrete. Changing the group isomorphism
allows the natural-module twists in the source. For A₆ the natural action is
the four-dimensional deleted permutation section; for SL and Sp it is matrix
multiplication, restricted to binary scalars. A₇'s separate four-dimensional
alternative is retained by the caller, since the source does not call it a
natural module.

`PairCarrier` forgets only the module coordinates, to isolate the concrete
model distinctions needed in the triple-cover case. It is not a group-family
tag unrelated to the acting group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(4iii),
printed p.325; B.4.2(2),(3),(6),(7),(9), printed p.86.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

noncomputable def binaryLinear (d n : ℕ) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin d) (GaloisField 2 n))
      (Fin d → GaloisField 2 n) where
  toFun g := (specialLinearNatural d g).restrictScalars (ZMod 2)
  map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (specialLinearNatural d).map_one v
  map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ((specialLinearNatural d).map_mul g h) v

noncomputable def binarySymplectic (n : ℕ) :
    Representation (ZMod 2) (Matrix.symplecticGroup (Fin 2) (GaloisField 2 n))
      ((Fin 2 ⊕ Fin 2) → GaloisField 2 n) where
  toFun g := (symplecticNatural 2 g).restrictScalars (ZMod 2)
  map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (symplecticNatural 2).map_one v
  map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ((symplecticNatural 2).map_mul g h) v

/-- The group consequences of every alternative in F.9.18(4iii). -/
def PairCarrier (E : Type*) [Group E] : Prop :=
  (∃ n : ℕ, 0 < n ∧ Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ∨
  (∃ n : ℕ, 0 < n ∧ Nonempty (E ≃* Matrix.symplecticGroup (Fin 2) (GaloisField 2 n))) ∨
  Nonempty (E ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
  Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
  Nonempty (E ≃* alternatingGroup (Fin 7))

/-- The five natural actions in (4iii), with actual equivariant coordinates.
Over the binary field SL₄ and SL₅ have trivial scalar centers, so these are
the literal matrix realizations of the source L₄(2) and L₅(2). -/
def NaturalModel {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) : Prop :=
  (∃ (n : ℕ) (_ : 0 < n)
      (e : E ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)),
    Nonempty (σ.Equiv ((binaryLinear 3 n).comp e.toMonoidHom))) ∨
  (∃ (n : ℕ) (_ : 0 < n)
      (e : E ≃* Matrix.symplecticGroup (Fin 2) (GaloisField 2 n)),
    Nonempty (σ.Equiv ((binarySymplectic n).comp e.toMonoidHom))) ∨
  (∃ e : E ≃* alternatingGroup (Fin 6),
    Nonempty (σ.Equiv ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).comp
      e.toMonoidHom))) ∨
  (∃ e : E ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
    Nonempty (σ.Equiv ((specialLinearNatural 4).comp e.toMonoidHom))) ∨
  (∃ e : E ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
    Nonempty (σ.Equiv ((specialLinearNatural 5).comp e.toMonoidHom)))

theorem NaturalModel.pairCarrier {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] {σ : Representation (ZMod 2) E W}
    (h : NaturalModel σ) : PairCarrier E := by
  rcases h with ⟨n, hn, e, _⟩ | ⟨n, hn, e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))

theorem PairCarrier.of_equiv {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (h : PairCarrier F) : PairCarrier E := by
  rcases h with ⟨n, hn, f⟩ | ⟨n, hn, f⟩ | f | f | f | f
  · exact Or.inl ⟨n, hn, f.map (e.trans ·)⟩
  · exact Or.inr (Or.inl ⟨n, hn, f.map (e.trans ·)⟩)
  · exact Or.inr (Or.inr (Or.inl (f.map (e.trans ·))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (f.map (e.trans ·)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (f.map (e.trans ·))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (f.map (e.trans ·))))))

private theorem no_equiv_center_one {E : Type*} [Group E]
    (h : Nat.card (Subgroup.center E) = 1)
    (e : Atlas.Codes.HexEvenAutomorphisms ≃* E) : False := by
  have hc := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [Representation.Hexacode.even_center_card, h] at hc
  norm_num at hc

/-- In characteristic two SL₃ contains the actual SL₃(2), of order 168.
Its order cannot divide the order 1080 of the triple cover. -/
theorem hex_not_equiv_sl3 (n : ℕ)
    (e : Atlas.Codes.HexEvenAutomorphisms ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) : False := by
  let f := algebraMap (ZMod 2) (GaloisField 2 n)
  let g := Matrix.SpecialLinearGroup.map (n := Fin 3) f
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    funext i j
    exact f.injective (congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) => a.val i j) h)
  have hd := Subgroup.card_dvd_of_injective g hg
  rw [Matrix.PSL3Two.card_SL, ← Nat.card_congr e.toEquiv, Atlas.Codes.hexEven_card] at hd
  norm_num at hd

/-- None of the six actual group models in (4iii) is the triple cover.
Only this model separation, not a classification of their modules, is needed. -/
theorem hex_not_pairCarrier : ¬ PairCarrier Atlas.Codes.HexEvenAutomorphisms := by
  intro h
  rcases h with ⟨n, _, ⟨e⟩⟩ | ⟨n, _, ⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · exact hex_not_equiv_sl3 n e
  · exact no_equiv_center_one (by
      rw [Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot]
      simp) e
  · obtain ⟨e⟩ := e
    exact no_equiv_center_one (by
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6))]
      simp) e
  · obtain ⟨e⟩ := e
    exact no_equiv_center_one (by
      rw [Atlas.ExceptionalSupport.card_sl_center]
      norm_num) e
  · obtain ⟨e⟩ := e
    exact no_equiv_center_one (by
      rw [Atlas.ExceptionalSupport.card_sl_center]
      norm_num) e
  · obtain ⟨e⟩ := e
    exact no_equiv_center_one (by
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7))]
      simp) e

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
