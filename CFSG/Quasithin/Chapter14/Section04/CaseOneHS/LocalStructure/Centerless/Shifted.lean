module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Preparation
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Transporting the center intersection to the shifted parabolic

An element fixing the displaced point lies in the displaced point
normalizer, hence fixes Z(U)^g. Conjugating the original center-intersection
identity by that element proves Z(I₂^l) = Z(U)^g ∩ Z(U)^l. The proof keeps
right conjugation and the actual original subgroups throughout.

Source: Aschbacher--Smith, 14.3.28(1), printed p.1002. Selecting l with
the additional generation properties and proving part (2) remain source
obligations; no trivial-intersection conclusion is assumed here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Fixing the displaced point preserves its normalizer-span center. -/
theorem shifted_center_fixed (F : InvariantFlag T V 3) (g l : G)
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G)) :
    conjugate (conjugate F.ZU g) l = conjugate F.ZU g := by
  have hn : conjugate F.H g ≤ normalizer (conjugate F.ZU g : Set G) := by
    have hh : F.H ≤ normalizer (F.ZU : Set G) :=
      (le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U))
    simpa only [conjugate, map_equiv_normalizer_eq] using
      map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
  apply (conjugate_eq_iff _ _).mpr
  apply hn
  change l ∈ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
  rw [map_equiv_normalizer_eq]
  exact Subgroup.centralizer_le_normalizer _ hl

/-- Source 14.3.28(1), for any actual l fixing the displaced point.
The remaining selection of l and generation of L are separate source steps. -/
theorem source_shifted_center_intersection (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G)) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
      conjugate F.ZU g ⊓ conjugate F.ZU l := by
  rw [centerIn_conjugate,
    ← (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).1,
    conjugate_inf, shifted_center_fixed F g l hl, inf_comm]

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
