module
public import Theory.SpecificGroups.SymplecticFour.ScalarRadical
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion

/-!
# The marked symplectic torus in the original A5 point-centralizer argument

A point or plane parabolic marking in the literal central quotient of the
containing component produces an order-three element centralizing L/O₂(L)
but moving W=[V,L]. Triviality of the even symplectic multiplier lifts the
specified quotient map to an equivalence of whole groups. The scalar torus
is fixed-point-free on the full elementary radical; the original source
facts W≠1 and W≤O₂(L) therefore suffice, without replacing W by its natural
central quotient or presupposing W equals the whole radical.

The source embedding inspection must supply the marked image of the original
L in I/Z(I). Both parabolic rows feed the existing original-vector
point-centralizer alternative, including the exact ambient torus element.
Source: Aschbacher–Smith10.2.9, printed pp.750–751.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open Theory.SpecificGroups.SymplecticFour

private theorem scalar_image {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (P : Subgroup H)
    (L W : Subgroup G) (hP : P.map f = L)
    (hW : W ≤ L.pCoreIn 2) (hne : W ≠ ⊥)
    {x : H} (hx : orderOf x = 3) (hn : x ∈ normalizer (P : Set H))
    (hc : ∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2)
    (hfix : ∀ q ∈ P.pCoreIn 2, Commute q x → q = 1) :
    orderOf (f x) = 3 ∧ f x ∈ sectionCentralizer L ∧
      f x ∉ centralizer (W : Set G) := by
  have hcore : (P.pCoreIn 2).map f = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 P f hf, hP]
  refine ⟨(orderOf_injective f hf x).trans hx, ?_, ?_⟩
  · apply (mem_commutatorPreimage_iff (normalizer (L : Set G)) L (L.pCoreIn 2)
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)) (f x)).mpr
    constructor
    · rw [←hP]
      exact P.le_normalizer_map f (mem_map_of_mem f hn)
    · intro b hb
      obtain ⟨a,ha,rfl⟩ := hP.symm ▸ hb
      rw [←hcore, ←map_commutatorElement]
      exact mem_map_of_mem f (hc a ha)
  · intro hcentral
    obtain ⟨w,hwn⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hw : (w : G) ∈ (P.pCoreIn 2).map f := hcore.symm ▸ hW w.property
    obtain ⟨q,hq,hqw⟩ := hw
    have hcomm : Commute q x := by
      apply hf
      simpa only [map_mul,hqw] using (mem_centralizer_iff.mp hcentral w w.property)
    have hw1 : (w : G) = 1 := hqw.symm.trans (by rw [hfix q hq hcomm,map_one])
    exact hwn (Subtype.ext hw1)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A literal point or plane parabolic marking in the containing component's
central quotient supplies the moving cubic required by source10.2.9. -/
theorem source_a5_point_symplectic_moving_torus
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eI : (I ⧸ center I) ≃* Sp F)
    (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
      (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = planeLocal) :
    ∃ x : G, x ∈ I ∧ orderOf x = 3 ∧ x ∈ sectionCentralizer L ∧
      x ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card (f := 2) hF
  obtain ⟨eWhole,heWhole⟩ := CentralCovers.Even.exists_whole_model
    (n := 2) hF (by decide) eI
  have heMap : eWhole.toMonoidHom = eI.toMonoidHom.comp (QuotientGroup.mk' (center I)) := by
    ext i : 1
    exact heWhole i
  let f := I.subtype.comp eWhole.symm.toMonoidHom
  have hf : Function.Injective f := I.subtype_injective.comp eWhole.symm.injective
  have hmark' : (L.subgroupOf I).map eWhole.toMonoidHom = pointLocal ∨
      (L.subgroupOf I).map eWhole.toMonoidHom = planeLocal := by
    rwa [heMap]
  have hmap (P : Subgroup (Sp F)) (hp : (L.subgroupOf I).map eWhole.toMonoidHom = P) :
      P.map f = L := by
    rw [←hp, map_map]
    have he : f.comp eWhole.toMonoidHom = I.subtype := by
      ext i
      simp [f]
    rw [he,map_subgroupOf_eq_of_le hLI]
  have hrow (P : Subgroup (Sp F)) (hp : (L.subgroupOf I).map eWhole.toMonoidHom = P)
      (hx : ∃ x : Sp F, orderOf x = 3 ∧ x ∈ normalizer (P : Set (Sp F)) ∧
        (∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2) ∧
        ∀ q ∈ P.pCoreIn 2, Commute q x → q = 1) :
      ∃ x : G, x ∈ I ∧ orderOf x = 3 ∧ x ∈ sectionCentralizer L ∧
        x ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    obtain ⟨x,hx3,hxN,hxC,hxFix⟩ := hx
    exact ⟨f x, (eWhole.symm x).property,
      scalar_image f hf P L ⁅D.fullModule,L⁆ (hmap P hp)
        (source_full_moved_le_component_core D) (source_full_moved_ne_bot D)
        hx3 hxN hxC hxFix⟩
  rcases hmark' with hp | hp
  · exact hrow pointLocal hp (ScalarRadical.point_cubic_scalar hF)
  · exact hrow planeLocal hp (ScalarRadical.plane_cubic_scalar hF)

/-- The marked Sp4(4) embedding row feeds the original point-centralizer
alternative without a new module, central-lift or radical-size premise. -/
theorem source_a5_point_symplectic_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eI : (I ⧸ center I) ≃* Sp F)
    (hmark : (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
      (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = planeLocal) :
    SourceA5PointComponentAlternative D e t I := by
  obtain ⟨x,_,hx3,hxL,hxW⟩ := source_a5_point_symplectic_moving_torus D I hLI hF eI hmark
  exact .torus x hx3 hxL hxW

end CFSG.Quasithin.Chapter10
