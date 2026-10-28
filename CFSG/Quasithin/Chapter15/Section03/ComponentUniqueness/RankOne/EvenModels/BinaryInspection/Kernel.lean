module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SourceReduction

/-!
# Recovering original subgroups in the binary action quotient

Every binary component here is centerless. In the simple branches this
follows from perfectness; in the transposition branch its two-group center
excludes the source's triple cover. The two exceptional central-cover
branches have field degree two and hence cannot occur at degree one.

Thus the map to I/C_I(L) is injective on every subgroup of L, in particular
on the original Y₊. An A₄ identification in the quotient therefore lifts
through an actual equivalence, without an assumption about the kernel.
The binary local classification and the A₄ identification are separate
results still required for the source-theorem assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501--502, and the binary paragraph of 15.3.43, printed p.1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- The original component is centerless in every binary source alternative. -/
theorem binary_center_eq_bot {z : G} (hm : Model L z 1) : center L = ⊥ := by
  cases hm with
  | simple hs _ _ =>
    let : IsSimpleGroup L := hs
    let : Group.IsPerfect (L.subgroupOf I) := c.component.2.toIsPerfect
    let e := subgroupOfEquivOfLe c.component_le
    let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim
  | linearThreeCover hn _ _ _ => omega
  | g2Cover hn _ _ _ => omega
  | alternatingSix _ hc _ =>
    exact Subgroup.card_eq_one.mp (hc.resolve_right (center_card_ne_three c))

/-- Restrict the faithful component quotient to any subgroup of the component. -/
noncomputable def subgroupImageEquiv (hZ : center L = ⊥)
    (X : Subgroup G) (hXL : X ≤ L) : X ≃* c.toComponentAction.image X := by
  let d := c.toComponentAction
  have hXI : X ≤ I := hXL.trans c.component_le
  let f : X →* d.image X := (d.quotientMap.subgroupMap (X.subgroupOf I)).comp
    (subgroupOfEquivOfLe hXI).symm.toMonoidHom
  have hsurj : Function.Surjective f := (d.quotientMap.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hXI).symm.surjective
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hx
    change d.quotientMap ⟨x, hXI x.property⟩ = 1 at hx
    have hk : (⟨(x : G), hXI x.property⟩ : I) ∈ d.kernel :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hz : (⟨(x : G), hXL x.property⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hk y y.property)
    have hx1 : (⟨(x : G), hXL x.property⟩ : L) = 1 := hZ.le hz
    exact Subtype.ext (congrArg (fun x : L => (x : G)) hx1)
  exact MulEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- The original actor and its quotient image are genuinely isomorphic. -/
noncomputable def actorImageEquiv {z : G} (hm : Model L z 1) :
    Yplus ≃* c.toComponentAction.image Yplus :=
  subgroupImageEquiv c (binary_center_eq_bot c hm) Yplus c.y_le_component

/-- A quotient A₄ identification contradicts the original actor condition. -/
theorem false_of_alternating_four_image {z : G} (hm : Model L z 1)
    (hY : Nonempty (c.toComponentAction.image Yplus ≃* alternatingGroup (Fin 4))) :
    False := by
  obtain ⟨e⟩ := hY
  exact c.not_alternating_four ⟨(actorImageEquiv c hm).trans e⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection
