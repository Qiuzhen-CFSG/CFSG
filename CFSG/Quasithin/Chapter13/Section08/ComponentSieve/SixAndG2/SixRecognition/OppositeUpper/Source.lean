module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Marking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Permutation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Actors

/-!
# Closing the strong-offender branch on the literal upper section

The strong natural constituent first forces the full symmetric actor. Sylow
conjugacy marks the original source Sylow, and the actual γ-to-α conjugator
places the offender in the original parabolic's relative two-core. The
index-three parabolic calculation then selects the syntheme marking.
The source seed gives the actual upper carrier as a noncentral syntheme
quotient. Its even transvection cube cannot be quadratic, contradicting
13.8.4(6) transported by that same source conjugator.

This is a separately named direct permutation-quotient route to the
contradiction in 13.8.26. It reuses the invariant-kernel calculation already
proved for 13.8.34 and does not require choosing the upper four-dimensional
quotient. Consequently it also discharges the `OppositeUpper` callbacks of
`Strict.source_no_two_faithful_sections` by excluding their strong premise.
No identification of the two outer-related actions is made.

The remaining inputs are the natural constituent, the source Sylow and
index-three field data, F.9.13 placement, and 13.8.4(5–6). Their final
chapter discharge belongs to `qt-d-138-six-section-recognition` and its
earlier-source owners, including `qt-d-1381-source`.

Source: Aschbacher–Smith 13.8.26, printed p.962/PDF p.979, using B.3.4(2)(i).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
open NaturalSix

variable {J E F : Type*} [Group J] [Finite J]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- The strong-offender contradiction from an actual parabolic-fixed cyclic
upper module. The parabolic marking and symmetric actor are conclusions. -/
theorem no_strong_of_parabolic_cyclic
    {σ : Representation (ZMod 2) J E} (m : NaturalSection σ)
    (ha : alternatingGroup (Fin 6) ≤ m.actor.range)
    (τ : Representation (ZMod 2) J F) (T : Sylow 2 J) (P A : Subgroup J)
    (hTP : (T : Subgroup J) ≤ P) (hi : (T : Subgroup J).relIndex P = 3)
    (hcyclic : IsParabolicCyclic τ P) (hnc : ∃ a v, τ a v ≠ v)
    (hq : IsQuadratic τ A) (h : J)
    (hplace : A.map (MulAut.conj h).toMonoidHom ≤ P.pCoreIn 2) :
    ¬ ∃ B ≤ A, IsStrongOffender σ B := by
  classical
  rintro ⟨B, hBA, hB⟩
  obtain ⟨n, hn, hT⟩ := m.exists_sylow_marking ha T hB
  let e : J ≃* Symmetric := MulEquiv.ofBijective n.actor ⟨n.injective, hn⟩
  have hm := parabolic_marking n T P A B h hTP hi hT hplace hBA hB
  have hAT : (A.map (MulAut.conj h).toMonoidHom).map n.actor ≤
      ChapterB.Offenders.Six.sylowCarrier := by
    have hh := map_mono (f := n.actor) hplace
    rw [map_pCoreIn_of_injective 2 P n.actor n.injective, hm, H2_core_eq_D] at hh
    exact hh.trans Marked.D_le_sylow
  have hc := (n.conjugateMarking h).strong_image_eq_cube hBA hB (by
    rw [n.conjugateMarking_actor_map]
    exact hAT)
  have hDa : D ≤ (A.map (MulAut.conj h).toMonoidHom).map n.actor := by
    rw [← hc, n.conjugateMarking_actor_map]
    exact map_mono (map_mono hBA)
  let : Fintype (J ⧸ P) := Fintype.ofFinite _
  exact not_quadratic_of_parabolic_cyclic τ P _ e hm hcyclic hnc
    (inf_le_left.trans hDa) (quadratic_conjugate τ A h hq)

open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G : Type*} [Group G] [Finite G] {L T H V V₃ : Subgroup G}

/-- The literal source upper section excludes strong offenders on any of
the displayed natural lower sections. The original `L₁ ⊔ T` is used both
for the seed normalizer and for the F.9.13 relative two-core placement. -/
theorem source_no_strong
    {σ : Representation (ZMod 2) (Source.Hstar H) E}
    (m : NaturalSection σ) (ha : alternatingGroup (Fin 6) ≤ m.actor.range)
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (L₁ R : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H) (hRH : R ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hq : ⁅R, ⁅R, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : R.map (MulAut.conj (y : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    ¬ ∃ B ≤ Source.starImage H R, IsStrongOffender σ B := by
  obtain ⟨hcyclic, hmove⟩ := source_cyclic t (L₁ ⊔ T) hflag hindex hnorm hnc
  apply no_strong_of_parabolic_cyclic m ha τ S (Source.starImage H (L₁ ⊔ T)) _
    (by rw [hS]; exact Seven.LocalGeometry.starImage_mono H le_sup_right)
    (by rwa [hS]) hcyclic hmove (upper_quadratic_of_commutator τ t R hq)
    (QuotientGroup.mk' (pCore 2 H) y)
  exact Seven.LocalGeometry.star_conjugate_le_twoCore H (L₁ ⊔ T) R
    (sup_le hL hT) hRH y hplace

/-- The direct source contradiction supplies precisely the callback required
by `Strict`, without adding an upper-quotient hypothesis. This theorem does
not claim a constructive selection of a four-dimensional quotient. -/
theorem source_oppositeUpper_of_strong
    {σ : Representation (ZMod 2) (Source.Hstar H) E}
    (m : NaturalSection σ) (ha : alternatingGroup (Fin 6) ≤ m.actor.range)
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (L₁ R : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H) (hRH : R ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hq : ⁅R, ⁅R, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : R.map (MulAut.conj (y : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (B : Subgroup (Source.Hstar H)) (hBA : B ≤ Source.starImage H R)
    (hB : IsStrongOffender σ B) :
    Nonempty (SixRecognition.OppositeUpper σ τ (Source.starImage H R)) :=
  (source_no_strong m ha τ t L₁ R hL hT hRH S hS hi hflag hindex hnorm hnc
    hq y hplace ⟨B, hBA, hB⟩).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
end
