module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.LocalCore
public import Theory.GroupAction.FiveActorTwoCore

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.Five
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.FiveAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.SylowStructure

/-!
# PSU₃(4) Sylow-center control

The genuine torus supplies an element of order five in the component Borel.
The control follows from two intrinsic calculations for the marked
Sylow subgroup P: its central quotient is E₁₆ with P′ = Z(P), and every
five-element of N_L(P) induces an automorphism of order five on P.

The general automorphism-kernel argument carries that order to P/Z(P).
Irreducibility and normal two-group fixed points then make the actor's
two-core fix Z(P). The theorem below transports this actual action to the
specified ambient Sylow image S ∩ L and the specified embedded center W.
It requires no ambient normality of L.

The model contract below discharges both intrinsic calculations through the
genuine standard root coordinates. Its local application supplies the
five-element and center-control inputs to the source intersection-core
argument. The final unitary exclusion remains with its source assembly,
which also needs the orthogonal plane detection calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.40, printed p.1138; Huppert II.10.12 for the unitary model.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

/-- Intrinsic Sylow structure and a faithful five-action imply the exact ambient control. -/
theorem fiveCoreControl_of_sylow_action
    {G : Type*} [Group G] [Finite G] {L S W : Subgroup G} (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWL : W ≤ L)
    (hW : W.subgroupOf L = (center (P : Subgroup L)).map (P : Subgroup L).subtype)
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (hcard : Nat.card (P ⧸ center P) = 16)
    (hderived : commutator P = center P)
    (hfive : ∀ x : normalizer (P : Set L), orderOf x = 5 →
      orderOf ((P : Subgroup L).normalizerMonoidHom x) = 5) :
    FiveCoreControl L (S ⊓ L) W := by
  let U := S ⊓ L
  have hsub : U.subgroupOf L = (P : Subgroup L) := by
    change (S ⊓ L).subgroupOf L = (P : Subgroup L)
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let e : P ≃* U := {
    toFun p := ⟨p.val, by
      change ((p : L) : G) ∈ S ⊓ L
      rw [← hP]
      exact mem_map_of_mem L.subtype p.property⟩
    invFun u := ⟨⟨u.val, u.property.2⟩, by rw [← hsub]; exact u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  intro K hK hex
  let rho : K →* MulAut P :=
    ((MulAut.congr e.symm).toMonoidHom.comp U.normalizerMonoidHom).comp (inclusion hK)
  obtain ⟨x, hx, hx5⟩ := hex
  have hxN : (⟨x, hx.2⟩ : L) ∈ normalizer (P : Set L) := by
    change (⟨x, hx.2⟩ : L) ∈ normalizer ((P : Subgroup L) : Set L)
    rw [← hsub, ← subgroupOf_normalizer_eq (show U ≤ L from inf_le_right)]
    exact hK hx.1
  let a : K := ⟨x, hx.1⟩
  let b : normalizer (P : Set L) := ⟨⟨x, hx.2⟩, hxN⟩
  have hb : orderOf b = 5 := by
    simpa only [Subgroup.orderOf_coe] using
      (show orderOf ((b : L) : G) = 5 from hx5)
  have hrho : rho a = (P : Subgroup L).normalizerMonoidHom b := by
    ext p
    rfl
  have hfix := Theory.GroupAction.FiveActorTwoCore.core_fixes_center
    hcard hderived rho a (by
      rw [hrho]
      exact Theory.GroupAction.FiveActorTwoCore.order_five_on_central_quotient
        P.isPGroup' hderived _ (hfive b hb))
  rintro y ⟨c, hc, rfl⟩ w hw
  have hwL : (⟨w, hWL hw⟩ : L) ∈ W.subgroupOf L := hw
  rw [hW] at hwL
  obtain ⟨z, hz, he⟩ := hwL
  have heG : ((z : L) : G) = w := congrArg Subtype.val he
  have hcz := congrArg (fun p : P => ((p : L) : G)) (hfix c hc z hz)
  change (c : G) * ((z : L) : G) * (c : G)⁻¹ = ((z : L) : G) at hcz
  rw [heG] at hcz
  exact (mul_inv_eq_iff_eq_mul.mp hcz).symm

/-- The actual PSU₃(4) model supplies Sylow-center control for every ambient
normalizer containing a five-element from the component. -/
theorem unitary_four_fiveCoreControl
    {G : Type*} [Group G] [Finite G] {L S W : Subgroup G}
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWL : W ≤ L)
    (hW : W.subgroupOf L = (center (P : Subgroup L)).map (P : Subgroup L).subtype) :
    FiveCoreControl L (S ⊓ L) W := by
  obtain ⟨hel, hcard, hderived⟩ := unitary_four_sylow_structure hm P
  let : IsElementaryAbelian 2 (P ⧸ center P) := hel
  exact fiveCoreControl_of_sylow_action P hP hWL hW hcard hderived
    (unitary_four_normalizer_five_action hm P)

/-- The complete intrinsic model contract for the unitary step in 15.3.40:
the marked Borel contains a five-element, and normalizer two-cores containing
such an element centralize the marked Sylow center. -/
theorem unitary_four_model_core
    {G : Type*} [Group G] [Finite G] {L S W : Subgroup G}
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWL : W ≤ L)
    (hW : W.subgroupOf L = (center (P : Subgroup L)).map (P : Subgroup L).subtype) :
    (∃ x : G, x ∈ ChapterF.Source.borel L S ∧ orderOf x = 5) ∧
      FiveCoreControl L (S ⊓ L) W :=
  ⟨unitary_four_borel_has_five hm P hP, unitary_four_fiveCoreControl hm P hP hWL hW⟩

/-- Application to the literal source intersection core. This discharges both
model premises of `local_core_centralizes_of_five_control`, preserving relative
component normality and the actual Sylow-center embedding. The Borel facts are
supplied by `unitary_four_borel_facts` in the source assembly module. -/
theorem local_core_centralizes_of_unitary_four
    {G : Type*} [Group G] [Finite G]
    (d : CharacteristicTwo.LocalData G) {I L W : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hf : ChapterF.Source.RankOneBorelFacts L d.S)
    (hB : d.M ⊓ L = ChapterF.Source.borel L d.S)
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = d.S ⊓ L)
    (hWL : W ≤ L)
    (hW : W.subgroupOf L = (center (P : Subgroup L)).map (P : Subgroup L).subtype) :
    (d.M ⊓ d.Mc).pCoreIn 2 ⊓ I ≤ centralizer (W : Set G) := by
  obtain ⟨hfive, hcontrol⟩ := unitary_four_model_core hm P hP hWL hW
  exact local_core_centralizes_of_five_control d h hMc hf hB hfive hcontrol

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
