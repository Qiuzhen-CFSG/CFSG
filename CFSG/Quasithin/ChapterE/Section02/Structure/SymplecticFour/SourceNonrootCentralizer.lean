module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MovingPair
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry

/-!
# The nonroot centralizer in the original E.2.7 component

The actual moving diagram actor rules out both central-root axes. The literal
opposite pair therefore contains an involution whose ambient centralizer is
the standard unipotent group, and whose pair centralizer is the marked Sylow
intersection. The final theorem transfers this element through the original
aligned component map and proves C_L(z) = T ∩ L for z in the original V.

These are source applications of the explicit centralizer calculation on
Aschbacher--Smith E.2.7, printed p.220. The subgroup-recognition branches and
their Borel/core models remain separate obligations.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A selected element of the original central subgroup has the literal
marked Sylow intersection as its centralizer in the opposite pair. -/
theorem source_pair_has_marked_nonroot_centralizer {n : ℕ}
    (hF : Nat.card F = 2^n) (V : Subgroup (Sp F))
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hl : ¬V ≤ RootSubgroup.group 0) (hs : ¬V ≤ RootSubgroup.group 4) :
    ∃ z : oppositePair V, (z : Sp F) ∈ V ∧ orderOf z = 2 ∧
      centralizer ({z} : Set (oppositePair V)) =
        (unipotent (F := F)).subgroupOf (oppositePair V) ∧
      IsPGroup 2 (centralizer ({z} : Set (oppositePair V))) := by
  obtain ⟨s,t,hs0,ht0,hv⟩ := exists_upper_nonzero_parameters V
    (CentralRootGeometry.parameter_range (F := F) ▸ hc) hl hs
  have hi : upper s t ∈ oppositePair V :=
    (show V ≤ oppositePair V from le_sup_left) hv
  let z : oppositePair V := ⟨upper s t,hi⟩
  have hz := subgroup_centralizer_upper (oppositePair V) s t hs0 ht0 hi
  refine ⟨z,hv,?_,hz,?_⟩
  · exact (orderOf_injective (oppositePair V).subtype
      (oppositePair V).subtype_injective z).symm.trans (upper_orderOf s t hs0)
  · rw [hz]
    exact (isPGroup_unipotent hF).comap_subtype

/-- The moving-actor source supplies both the faithful irreducible pair
geometry and an actual two-group centralizer with its original marking. -/
theorem source_moving_pair_with_marked_nonroot_centralizer {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU : V≤unipotent)
    (hV : V.map a.val.toMonoidHom = V) (hr : 2<Nat.card V) :
    V≤(center (unipotent (F := F))).map (unipotent (F := F)).subtype ∧
    Representation.IsIrreducible (pairAction V) ∧ pCore 2 (oppositePair V)=⊥ ∧
    ∃ z : oppositePair V, (z : Sp F) ∈ V ∧ orderOf z = 2 ∧
      centralizer ({z} : Set (oppositePair V)) =
        (unipotent (F := F)).subgroupOf (oppositePair V) ∧
      IsPGroup 2 (centralizer ({z} : Set (oppositePair V))) := by
  obtain ⟨hc,hi,hcore⟩ := source_moving_pair hF hn a ha V hVU hV hr
  have hq : 2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hne : V≠⊥ := by intro he; subst V; simp at hr
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ha V hV hne
  exact ⟨hc,hi,hcore,source_pair_has_marked_nonroot_centralizer hF V hc hl hs⟩

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open DiagramAutomorphisms EvenBorelTorus ChapterB
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- In the original core-free E.2.7 source, choose z in V with its exact
component centralizer T ∩ L. No root-placement or centralizer premise remains. -/
theorem source_nonroot_component_centralizer {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V) :
    ∃ z : L, (z : G) ∈ V ∧ orderOf z=2 ∧
      centralizer ({z} : Set L) = (T : Subgroup G).subgroupOf L := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,_⟩ := source_geometry hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  obtain ⟨t,ht⟩ := exists_moving_sylow_actor hF hn T hP L e hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e t,sylow_actor T L e hmark t⟩
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
  have hne : W≠⊥ := by
    intro he
    have hh : Nat.card W=1 := by rw [he]; simp
    omega
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ht W hWa hne
  obtain ⟨s,t,hs0,ht0,hw⟩ := exists_upper_nonzero_parameters W
    (CentralRootGeometry.parameter_range (F := F) ▸ hc) hl hs
  refine ⟨e (upper s t),hw,?_,?_⟩
  · exact (orderOf_injective e.toMonoidHom e.injective (upper s t)).trans
      (upper_orderOf s t hs0)
  · ext x
    rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    calc
      x * e (upper s t) = e (upper s t) * x ↔
          e.symm x * upper s t = upper s t * e.symm x := by
        rw [← e.symm.injective.eq_iff]
        simp only [map_mul, MulEquiv.symm_apply_apply]
      _ ↔ e.symm x ∈ (unipotent (F := F)) := by
        rw [← centralizer_upper_eq_unipotent s t hs0 ht0,
          mem_centralizer_singleton_iff]
      _ ↔ (x : G) ∈ (T : Subgroup G) := by
        rw [←hmark]
        simp only [Subgroup.mem_comap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, Subgroup.coe_subtype]

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
