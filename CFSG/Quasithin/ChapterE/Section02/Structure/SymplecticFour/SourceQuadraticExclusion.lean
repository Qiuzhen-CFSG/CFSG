module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.QuadraticExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry

/-!
# Quadratic-form exclusion in the original symplectic source geometry

The original minimal parabolic hypotheses place the elementary subgroup in
the simple component and its central root plane. They supply an actual
Sylow actor moving the two diagram types, and normality under the original
Sylow gives setwise stability of the same component pullback. The resulting
quadratic-curve bound excludes an invariant quadratic form already on that
pullback and hence on its literal opposition pair.

This discharges the orthogonal alternative in Aschbacher--Smith E.2.7,
printed p.220, whenever transvection recognition supplies a quadratic form
with the standard symplectic polar form. Recognition itself, the imprimitive
alternative, and coefficient-field markings remain separate source steps.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The moving-actor source pair preserves no quadratic form with the
standard symplectic polar form. -/
theorem source_moving_pair_quadratic_exclusion {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:ActorReduction.stabilizer (F:=F)) (ha:¬PreservesDiagram a.val)
    (V:Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU:V≤unipotent)
    (hV:V.map a.val.toMonoidHom=V) (hr:2<Nat.card V)
    (Q:QuadraticForm F (Vector F)) (hQ:Q.polarBilin=form F) :
    ¬∀g∈oppositePair V,∀x:Vector F,Q (g•x)=Q x := by
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨hc,_,_⟩ := source_moving_pair hF hn a ha V hVU hV hr
  exact oppositePair_not_preserves_quadratic_of_moving_actor hq a ha V hV
    (CentralRootGeometry.parameter_range (F:=F) ▸ hc) hr Q hQ
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus ChapterB
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Already the original elementary image in component coordinates cannot
preserve a quadratic form with the standard symplectic polar form. -/
theorem source_geometry_subgroup_quadratic_exclusion {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (Q:QuadraticForm F (Vector F)) (hQ:Q.polarBilin=form F) :
    ¬∀g∈V.comap (L.subtype.comp e.toMonoidHom),∀x:Vector F,Q (g•x)=Q x := by
  let f:=L.subtype.comp e.toMonoidHom
  let W:=V.comap f
  have hf:Function.Injective f:=L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hcent,_,_⟩ := source_geometry hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr
  have hcard:Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  obtain ⟨t,ht⟩:=exists_moving_sylow_actor hF hn T hP L e hmark hgen
  let a:ActorReduction.stabilizer (F:=F):=
    ⟨extensionAction L e t,sylow_actor T L e hmark t⟩
  have hWa:W.map a.val.toMonoidHom=W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x)∈V
      rw [show f (a.val x)=t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hq:2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  exact not_preserves_quadratic_of_moving_actor hq a ht W hWa
    (CentralRootGeometry.parameter_range (F:=F) ▸ hcent) (hcard.symm ▸ hr) Q hQ

/-- The literal original E.2.7 opposition pair is contained in no orthogonal
group with the standard symplectic polar form. -/
theorem source_geometry_quadratic_exclusion {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (Q:QuadraticForm F (Vector F)) (hQ:Q.polarBilin=form F) :
    ¬∀g∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      ∀x:Vector F,Q (g•x)=Q x := by
  intro hpres
  apply source_geometry_subgroup_quadratic_exclusion hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr Q hQ
  exact fun g hg => hpres g ((show V.comap (L.subtype.comp e.toMonoidHom)≤
    oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) from le_sup_left) hg)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
