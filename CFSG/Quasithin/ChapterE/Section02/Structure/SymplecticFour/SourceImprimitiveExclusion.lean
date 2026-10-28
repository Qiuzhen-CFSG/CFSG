module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.ImprimitiveExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry

/-!
# Imprimitive-plane exclusion in the original symplectic source geometry

The actual minimal-parabolic hypotheses supply a moving Sylow actor and
setwise stability of the original elementary pullback. The resulting
rank-one companions force both generators of its opposition pair to fix
any permuted orthogonal two-plane decomposition. Its proved F-linear
irreducibility rules that out.

This discharges the imprimitive alternative in Aschbacher--Smith E.2.7,
printed p.220. The literal component inclusion and V comap are retained;
no root-in-V, transvection-recognition or marked-model premise is added.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The genuine moving-actor source pair cannot permute two orthogonal planes. -/
theorem source_moving_pair_imprimitive_exclusion {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (a:ActorReduction.stabilizer (F:=F)) (ha:¬PreservesDiagram a.val)
    (V:Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU:V≤unipotent)
    (hV:V.map a.val.toMonoidHom=V) (hr:2<Nat.card V)
    (D:OrthogonalTwoDecomposition F) :
    ¬∀g∈oppositePair V,D.Permutes g := by
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨hc,_,_⟩ := source_moving_pair hF hn a ha V hVU hV hr
  exact moving_pair_not_permute_orthogonal_two hq a ha V hV hc hr D

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus ChapterB
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The same imprimitive exclusion for the literal original E.2.7 pullback pair. -/
theorem source_geometry_imprimitive_exclusion {n:ℕ}
    (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V)
    (D:OrthogonalTwoDecomposition F) :
    ¬∀g∈oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),D.Permutes g := by
  let f:=L.subtype.comp e.toMonoidHom
  let W:=V.comap f
  have hf:Function.Injective f:=L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hcent,_,_⟩ := source_geometry hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr
  let j:W→*V := (f.comp W.subtype).codRestrict V (fun x=>x.property)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective j (by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z:V=>(z:G)) h)))
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
  exact moving_pair_not_permute_orthogonal_two hq a ht W hWa hcent
    (hcard.symm ▸ hr) D

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
