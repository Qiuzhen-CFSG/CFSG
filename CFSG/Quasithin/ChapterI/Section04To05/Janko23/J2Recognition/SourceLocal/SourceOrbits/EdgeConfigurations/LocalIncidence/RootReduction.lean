module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.KleinFour
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Edges
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdgeIncidence
public import Theory.SpecificGroups.HeisenbergFour.CubicExtension

/-!
# Restricting the inner triple to its four-group centralizer

This reduction has two explicit, independent outstanding inputs: an actual
identification of the pure 2-central four-group centralizer with the concrete
Heisenberg-four cubic extension, and the intrinsic cubic-pair theorem in
that model. It transports the literal three subgroups and their joins, then
applies the model theorem. Neither input is asserted to be proved here.
In particular this conditional reduction is not the completed 47.6(1).

The parent assembles these two inputs with the A₄ intersection calculation.
Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and 47.6(1),
pp.251,257–258,264.
-/

@[expose] public section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
open alternatingGroup.FiveLocalGeometry.CubicEdgeIncidence
variable {G : Type*} [Group G] [Finite G]

/-- The finite-model obligation, kept separate from ambient root recognition. -/
def RootModelCubicGeometry : Prop :=
  ∀ P Q R : Subgroup HeisenbergFour.Model,
    Nat.card P = 3 → Nat.card Q = 3 → Nat.card R = 3 →
    Nonempty (↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)) →
    Nonempty (↥(P ⊔ R) ≃* alternatingGroup (Fin 4)) →
    R ∉ cubicOrbit P Q →
    Nonempty (↥(Q ⊔ R) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

/-- Transport through the actual centralizer equivalence, retaining both join maps. -/
theorem sl2Join_of_root_model (hmodel : RootModelCubicGeometry)
    (D : Seed G) (K : Subgroup G) (e : K ≃* HeisenbergFour.Model)
    (Y U : D.Vertex) (hX : D.X ≤ K) (hY : Y.val ≤ K) (hU : U.val ≤ K)
    (hXY : D.graph.Adj D.base Y) (hXU : D.graph.Adj D.base U)
    (hout : U ∉ endpointOrbit D Y) : sl2Join D Y U := by
  let image (V : D.Vertex) : Subgroup HeisenbergFour.Model :=
    (V.val.subgroupOf K).map e.toMonoidHom
  have card_image (V : D.Vertex) (hV : V.val ≤ K) : Nat.card (image V) = 3 := by
    change Nat.card ((V.val.subgroupOf K).map e.toMonoidHom) = 3
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv, D.vertex_card]
  let joinEquiv (A B : D.Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K) :
      ↥(A.val ⊔ B.val) ≃* ↥(image A ⊔ image B) :=
    (AlternatingFiveGeometry.joinSubgroupOfEquiv K A.val B.val hA hB).symm.trans
      (((A.val.subgroupOf K ⊔ B.val.subgroupOf K).equivMapOfInjective
        e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr (Subgroup.map_sup _ _ _)))
  have ho : image U ∉ cubicOrbit (image D.base) (image Y) := by
    intro hu
    have hr := (mem_cubicOrbit_map_iff e (D.X.subgroupOf K)
      (Y.val.subgroupOf K) (U.val.subgroupOf K)).mp hu
    obtain ⟨x, hx⟩ := hr
    let a : D.X := ⟨(x : K), x.property⟩
    apply hout
    refine ⟨a, Subtype.ext ?_⟩
    change MulAut.conj (x : K) • Y.val.subgroupOf K = U.val.subgroupOf K at hx
    rw [conj_smul_subgroupOf hY (x : K)] at hx
    have hm := congrArg (fun S : Subgroup K => S.map K.subtype) hx
    change ((a : G) • Y).val = U.val
    rw [D.smul_val]
    rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hY (x : K)),
      map_subgroupOf_eq_of_le hU] at hm
    exact hm
  exact ⟨(joinEquiv Y U hY hU).trans
    (hmodel (image D.base) (image Y) (image U)
      (card_image D.base hX) (card_image Y hY) (card_image U hU)
      ⟨(joinEquiv D.base Y hX hY).symm.trans hXY.2.some⟩
      ⟨(joinEquiv D.base U hX hU).symm.trans hXU.2.some⟩ ho).some⟩

/-- The source four-group recognition obligation concerns pure z-class
four-groups, with an actual model equivalence of their full centralizer. -/
def PureFourCentralizerModels (D : Seed G) : Prop :=
  ∀ E : Subgroup G, IsKleinFour E →
    (∀ t ∈ E, t ≠ 1 → IsConj D.z t) →
    Nonempty (centralizer (E : Set G) ≃* HeisenbergFour.Model)

/-- Conditional final transport for the inner branch, including every X-translate.
The two named construction obligations above remain with their producers. -/
theorem inner_sl2Join_of_root_geometry (hmodel : RootModelCubicGeometry)
    (D : Seed G) (hcentralizers : PureFourCentralizerModels D) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (eI : intersection D Y g ≃* alternatingGroup (Fin 4)) (x : D.X) :
    sl2Join D Y ((x : G) • ((g : G) • Y)) := by
  let E := intersectionCore D Y g
  have he : IsKleinFour E := intersectionCore_isKleinFour D Y g eI
  have hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t := by
    intro t ht hne
    have hs : (⟨t, ht⟩ : E) ^ 2 = 1 := by
      simpa only [pow_two] using IsKleinFour.mul_self (⟨t, ht⟩ : E)
    have ho : orderOf t = 2 := orderOf_eq_prime
      (by simpa using congrArg Subtype.val hs) hne
    exact intersectionCore_involutions D Y g hclass t ht ho
  obtain ⟨e⟩ := hcentralizers E he hpure
  let gn : localNormalizer D := ⟨g, centralizer_le_normalizer _ g.property⟩
  have htr := triple_le_intersectionCore_centralizer D Y hF gn x
  have hgY : D.graph.Adj D.base ((g : G) • Y) := by
    have h := D.preserves (g : G) hY
    rwa [normalizer_fixes_base D gn] at h
  have hxU : D.graph.Adj D.base ((x : G) • ((g : G) • Y)) := by
    have h := D.preserves (x : G) hgY
    rwa [normalizer_fixes_base D ⟨x, D.X.le_normalizer x.property⟩] at h
  have hout : (x : G) • ((g : G) • Y) ∉ endpointOrbit D Y := by
    rintro ⟨a, ha⟩
    apply inner_not_endpointOrbit D Y ((g : G) • Y) ⟨g, g.property, hg, rfl⟩
    refine ⟨x⁻¹ * a, ?_⟩
    change ((x : G)⁻¹ * (a : G)) • Y = (g : G) • Y
    change (a : G) • Y = (x : G) • ((g : G) • Y) at ha
    rw [mul_smul, ha, inv_smul_smul]
  exact sl2Join_of_root_model hmodel D _ e Y ((x : G) • ((g : G) • Y))
    (le_sup_left.trans (le_sup_left.trans htr)) (le_sup_right.trans (le_sup_left.trans htr))
    (le_sup_right.trans htr) hY hxU hout

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
