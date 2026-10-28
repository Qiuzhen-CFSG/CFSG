module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Homogeneous
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Line

/-!
# The Cartan dichotomy on the whole original omega-center

In every homogeneous coordinate, an original omega-center vector is fixed
by T intersect L. Inner flag uniqueness puts that coordinate in the same
first field line. The Cartan acts there by a single scalar in every copy.
Thus a nonzero common fixed vector forces that scalar to be one for every
Cartan actor, and the entire omega-center is fixed. Otherwise its fixed
space is zero. The actual natural K-quotient and movement hypothesis exclude
the fixed alternative and give C_{V_H}(K)=1.

This treats both original natural models and every permitted multiplicity,
including the doubled SL₃ branch, with the original flag and quotient maps.
The natural marking and actual Cartan are constructed by Action/SourceComplete;
no module-classification or fixed-space premise remains in that assembly.
Source: Aschbacher--Smith, 11.3.7(3), printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem model_fixed_mem_line
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (w : c.Space)
    (hwfix : ∀ l : L, (l : G) ∈ (T : Subgroup G) → c.modelAction (c.quotientMap l) w = w) :
    w ∈ f.space 0 := by
  by_cases hw : w = 0
  · rw [hw]; exact Submodule.zero_mem _
  let U : Submodule S.field.Carrier c.Space := Submodule.span S.field.Carrier {w}
  have hn : (T : Subgroup G) ⊓ L ≤ normalizer (c.preimage U : Set G) := by
    intro l hl
    apply (c.mem_normalizer_preimage_iff U ⟨l,hl.2⟩).mpr
    intro u
    have he (u : c.Space) (hu : u ∈ U) :
        c.modelAction (c.quotientMap ⟨l,hl.2⟩) u = u := by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul,hwfix _ hl.1]
    constructor
    · intro hx
      have hx' := he _ hx
      have hi := (c.modelLinearEquiv (c.quotientMap ⟨l,hl.2⟩)).injective
      have hu' : c.modelAction (c.quotientMap ⟨l,hl.2⟩) u = u := hi hx'
      rwa [hu'] at hx
    · intro hx
      rwa [he _ hx]
  have he : U = f.space 0 := hu 0 U (finrank_span_singleton hw) hn
  rw [←he]
  exact Submodule.subset_span (Set.mem_singleton w)

/-- One scalar on all Sylow-fixed coordinates gives the whole omega-center dichotomy. -/
theorem omega_fixed_dichotomy_of_coordinates
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A : Subgroup G) (hAL : A ≤ L) (hn : A ≤ normalizer (f.Vi 0 : Set G))
    (hfixed : omegaCenter T ⊓ centralizer (L : Set G) = ⊥)
    (r : ℕ) (e : ComponentOmegaSpace D S ≃ₗ[ZMod 2] (Fin r → c.Space))
    (he : ∀ (l : L) (v : ComponentOmegaSpace D S) i,
      e (componentOmegaRepresentation D S (componentOmegaActorMap D S l) v) i =
        c.modelAction (c.quotientMap l) (e v i)) :
    omegaCenter T ⊓ centralizer (A : Set G) = omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T,A⁆ = ⊥ := by
  let u (z : G) (hz : z ∈ omegaCenter T) : ComponentOmegaSpace D S :=
    Additive.ofMul ⟨⟨z,((omegaCenter_le_sylow T).trans le_sup_right hz)⟩,
      le_conjugateSpanBy (omegaCenter T) L hz⟩
  have hfix (z : G) (hz : z ∈ omegaCenter T) (l : L)
      (hl : (l : G) ∈ centralizer ({z} : Set G)) :
      componentOmegaRepresentation D S (componentOmegaActorMap D S l) (u z hz) = u z hz := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (componentOmegaRepresentation_apply (D := D) (S := S)
      (inclusion le_sup_left l) (u z hz)).trans
        (mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) z (Set.mem_singleton z)).symm)
  have hmem (z : G) (hz : z ∈ omegaCenter T) (i : Fin r) : e (u z hz) i ∈ f.space 0 := by
    apply model_fixed_mem_line c f hu
    intro l hl
    rw [←he]
    have hh : componentOmegaRepresentation D S (componentOmegaActorMap D S l) (u z hz) = u z hz := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (componentOmegaRepresentation_apply (D := D) (S := S)
        (inclusion le_sup_left l) (u z hz)).trans
          (mul_inv_eq_iff_eq_mul.mpr (omegaCenter_le_sylow_centralizer T hz l hl))
    rw [hh]
  by_cases hzero : omegaCenter T ⊓ centralizer (A : Set G) = ⊥
  · exact Or.inl (hzero.trans hfixed.symm)
  right
  obtain ⟨z,hz,hz1⟩ := (omegaCenter T ⊓ centralizer (A : Set G)).bot_or_exists_ne_one.resolve_left hzero
  have hne : e (u z hz.1) ≠ 0 := by
    intro hh
    have he0 := e.injective (hh.trans e.map_zero.symm)
    exact hz1 (congrArg (fun v : ComponentOmegaSpace D S => (v.toMul.val : G)) he0)
  obtain ⟨i,hi⟩ : ∃ i : Fin r, e (u z hz.1) i ≠ 0 := by
    by_contra! hh
    exact hne (funext hh)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro y hy d hd
  let l : L := ⟨d,hAL hd⟩
  obtain ⟨a,ha⟩ := line_scalar_of_normalizes c f l (hn hd)
  have hzl : (l : G) ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro w rfl
    exact (hz.2 d hd).symm
  have has : a • e (u z hz.1) i = e (u z hz.1) i := by
    rw [←ha _ (hmem z hz.1 i),←he,hfix z hz.1 l hzl]
  have ha1 : a = 1 := by
    have hh : (a-1) • e (u z hz.1) i = 0 := by rw [sub_smul,one_smul,has,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hi)
  have hey : componentOmegaRepresentation D S (componentOmegaActorMap D S l) (u y hy) = u y hy := by
    apply e.injective
    funext j
    rw [he,ha _ (hmem y hy j),ha1,one_smul]
  have hyy := congrArg (fun v : ComponentOmegaSpace D S => (v.toMul.val : G)) hey
  exact mul_inv_eq_iff_eq_mul.mp
    ((componentOmegaRepresentation_apply (D := D) (S := S)
      (inclusion le_sup_left l) (u y hy)).symm.trans hyy)

/-- The original SL₃/Sp₄ source supplies the Cartan dichotomy, with no module callback. -/
theorem source_cartan_dichotomy
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) = omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T,oddCartanPart A⁆ = ⊥ := by
  have hAL : oddCartanPart A ≤ L := hAX.trans (hX.1.trans inf_le_left)
  obtain ⟨r,_,e,he⟩ := source_component_coordinates cL hG2 s c A hA hHall hAL
  exact omega_fixed_dichotomy_of_coordinates cL f hu (oddCartanPart A) hAL
    (hAX.trans (f.cartan_normalizes hu hX 0))
    (source_left_fixed_spaces s c A hA hHall hAL).1 r e he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
