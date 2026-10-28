module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.Linear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.Actor
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import GorensteinWalter.PSL2KleinFourCentralizerEqSelf

/-!
# The two linear component actors in 15.3.40

The Borel calculation forces the PSL₂ field to have four elements. Its
four-group is consequently a whole Sylow subgroup and is self-centralizing.
For PSL₃(2), the actual exceptional isomorphism with PSL₂(7) transports the
self-centralizer theorem for four-groups. In both cases conjugation and the
two-perfectness of O²(Y₊ ∩ L) construct its isomorphism with A₄.

The imported binary comparison retains the attribution and license of the
ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Order168`.

These are conditional branches of Aschbacher--Smith, combined manuscript
(1 March 2004), proof of 15.3.40, printed p.1138. The unitary branch is a
separate obligation before the rank-one alternative can be exhausted.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane

private theorem centralizer_le_of_equiv {H K : Type*} [Group H] [Group K]
    (f : H ≃* K) (W : Subgroup H)
    (hc : centralizer (W.map f.toMonoidHom : Set K) ≤ W.map f.toMonoidHom) :
    centralizer (W : Set H) ≤ W := by
  intro x hx
  have hxf : f x ∈ centralizer (W.map f.toMonoidHom : Set K) := by
    rintro y ⟨w, hw, rfl⟩
    change f w * f x = f x * f w
    exact (map_mul f w x).symm.trans ((congrArg f (hx w hw)).trans (map_mul f x w))
  obtain ⟨w, hw, he⟩ := hc hxf
  exact f.injective he ▸ hw

private theorem ambient_centralizer_le {G : Type*} [Group G] {L W : Subgroup G}
    (hc : centralizer (W.subgroupOf L : Set L) ≤ W.subgroupOf L) :
    L ⊓ centralizer (W : Set G) ≤ W := by
  intro x hx
  show (⟨x, hx.1⟩ : L) ∈ W.subgroupOf L
  apply hc
  intro w hw
  exact Subtype.ext (hx.2 w hw)

private theorem odd_linear_model_plane_selfCentralizing
    {H F : Type*} [Group H] [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (f : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (W : Subgroup H) (hW : IsKleinFour W) : centralizer (W : Set H) ≤ W := by
  apply centralizer_le_of_equiv f W
  have hKm : IsKleinFour (W.map f.toMonoidHom) :=
    GorensteinWalter.isKleinFour_map_of_injective W hW f.toMonoidHom f.injective
  exact (GorensteinWalter.psl2_kleinFour_centralizer_eq_self
    F hF (W.map f.toMonoidHom) hKm).le

/-- Every four-group in the binary degree-three model is self-centralizing. -/
theorem binary_plane_selfCentralizing {G : Type*} [Group G]
    {L W : Subgroup G} [IsKleinFour W]
    (hm : ClassicalGroup.IsPSL L 3 2) (hWL : W ≤ L) :
    L ⊓ centralizer (W : Set G) ≤ W := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply ambient_centralizer_le
  have h7 : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
    simp
  exact odd_linear_model_plane_selfCentralizing (H := L) (F := ZMod 7) h7
    (e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hF)) (W.subgroupOf L)
    (GorensteinWalter.isKleinFour_subgroupOf hWL inferInstance)

/-- Once the linear field has order four, the given four-group is a whole
Sylow subgroup, whose centralizer was computed in arbitrary coordinates. -/
theorem linear_four_plane_selfCentralizing {G : Type*} [Group G] [Finite G]
    {L S W : Subgroup G}
    (hm : ClassicalGroup.IsPSL L 2 4)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hWS : W ≤ S) (hWL : W ≤ L) (hW : Nat.card W = 4) :
    L ⊓ centralizer (W : Set G) ≤ W := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      (show Nat.card F = 2 ^ 2 from hF))
  let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hPi : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hWP : W.subgroupOf L ≤ (P : Subgroup L) := by
    rw [← hPi]
    exact subgroupOf_mono L (le_inf hWS hWL)
  have hcardW : Nat.card (W.subgroupOf L) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv).trans hW
  have hcardP : Nat.card P = 4 := (linear_sylow_card f P).trans hF
  have he : W.subgroupOf L = (P : Subgroup L) :=
    eq_of_le_of_card_ge hWP (by rw [hcardW]; exact hcardP.le)
  intro x hx
  have hxP : (⟨x, hx.1⟩ : L) ∈ (P : Subgroup L) := by
    apply linear_sylow_selfCentralizing f P
    intro y hy
    have hyW : y ∈ W.subgroupOf L := he.symm ▸ hy
    exact Subtype.ext (hx.2 y hyW)
  show (⟨x, hx.1⟩ : L) ∈ W.subgroupOf L
  exact he.symm ▸ hxP

/-- The PSL₃(2) branch yields an equivalence for the actual residual actor. -/
theorem binary_component_actor_alternating {G : Type*} [Group G] [Finite G]
    {Yplus L S W : Subgroup G} [IsKleinFour W]
    (hm : ClassicalGroup.IsPSL L 3 2) (hWS : W ≤ S) (hWL : W ≤ L)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hAN : componentFactor Yplus L ≤ normalizer (W : Set G))
    (hgen : ⁅W, componentFactor Yplus L⁆ = W) :
    Nonempty (componentFactor Yplus L ≃* alternatingGroup (Fin 4)) :=
  component_actor_alternating_of_selfCentralizing hWS hWL hSY hAN hgen
    (binary_plane_selfCentralizing hm hWL)

/-- The PSL₂ branch uses 15.3.33(1) to identify the Borel and restrict the
field before recognizing the residual actor. No small-model premise is used. -/
theorem linear_component_actor_alternating {G : Type*} [Group G] [Finite G]
    {L S M I Yplus W : Subgroup G} [IsKleinFour W] {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hLI : L ≤ I) [(L.subgroupOf I).Normal]
    (hSM : S ≤ M) (hYS : Yplus ⊔ S ≤ M ⊓ I) (hLM : ¬ L ≤ M)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (h33 : ∀ K : Subgroup G, K ≤ L → Yplus ⊔ S ≤ normalizer (K : Set G) →
      Theory.GroupTheory.generalizedFitting K = pCore 2 K → K ≤ M ⊓ I)
    (hWS : W ≤ S) (hWL : W ≤ L)
    (hWN : M ⊓ I ≤ normalizer (W : Set G))
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hgen : ⁅W, componentFactor Yplus L⁆ = W) :
    n = 2 ∧ Nonempty (componentFactor Yplus L ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨_, hn2⟩ := linear_restriction_of_source hn hm hLI hSM hYS hLM P hP h33
    hWS hWL IsKleinFour.card_four hWN
  refine ⟨hn2, component_actor_alternating_of_selfCentralizing hWS hWL hSY ?_ hgen ?_⟩
  · have hy : Yplus ≤ M ⊓ I := le_sup_left.trans hYS
    exact ((componentFactor_le_left Yplus L).trans hy).trans hWN
  · exact linear_four_plane_selfCentralizing (by simpa only [hn2, show (2 : ℕ) ^ 2 = 4 from rfl] using hm)
      P hP hWS hWL IsKleinFour.card_four

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
