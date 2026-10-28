module

public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.AbsolutelyIrreducible
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry

/-!
# Absolute irreducibility of the original marked symplectic pair

The original moving Sylow actor puts the elementary group in the central
root plane and excludes the root axes and diagonal lines. Its literal
opposite pair is therefore absolutely irreducible over the marked field.
The original-source wrapper retains the component inclusion and the same
pullback of V; it introduces no new representation or root-element witness.

Source: Aschbacher--Smith E.2.7, printed pp.219--220. This discharges the
absolute-irreducibility premise in the binary PSL2 degree-four inspection.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus ChapterB
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The genuine moving-actor source gives absolute irreducibility on the
same four-dimensional space and over the same field. -/
theorem source_moving_pair_absolutelyIrreducible {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU : V≤unipotent)
    (hV : V.map a.val.toMonoidHom=V) (hr : 2<Nat.card V) :
    Representation.IsAbsolutelyIrreducible (pairAction V) := by
  obtain ⟨hc,_,_⟩ := source_moving_pair hF hn a ha V hVU hV hr
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact pairAction_absolutelyIrreducible_of_moving_actor hq a ha V hV hc hr

/-- Absolute irreducibility for the literal component pullback in the
original minimal-parabolic setup, with no extra source premise. -/
theorem source_original_pair_absolutelyIrreducible
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V) :
    Representation.IsAbsolutelyIrreducible
      (pairAction (V.comap (L.subtype.comp e.toMonoidHom))) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,_⟩ := Structure.SymplecticFour.source_geometry
    hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  obtain ⟨t,ht⟩ := Structure.SymplecticFour.exists_moving_sylow_actor
    hF hn T hP L e hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e t,Structure.SymplecticFour.sylow_actor T L e hmark t⟩
  have hWa : W.map a.val.toMonoidHom=W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x)∈V
      rw [show f (a.val x)=t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact pairAction_absolutelyIrreducible_of_moving_actor hq a ht W hWa hc
    (hcard.symm ▸ hr)

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
