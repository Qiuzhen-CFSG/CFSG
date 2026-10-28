module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeCentralizer
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.ThreeSpace

/-!
# The literal hyperplane normalizer and its cubic residual image

In dimension three the full natural action identifies N_L(U ∩ V) with
an index-seven subgroup of L, hence gives its order 192. The residual
normalizes R=C_T(U), and the Sylow supplement shows that this hyperplane
normalizer is exactly N_L(R). Cancelling the central Sylow factor in the
intersection R ∩ L gives order sixteen and an image of order twelve in
N_G(R)/R.

Burnside transfer puts the image of Y=O²(N_L(U ∩ V)) in the odd core.
Its order divides 192, and the full action on U ∩ V gives a cubic divisor,
so the literal image has order three. The source application discharges
the common-centralizer record and retains the original quotient map.
The remaining normalizer recognition and both source branches are owned
by qt-d-12213-local-rigidity; this module does not assume their conclusions.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed pp.805--806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

/-- The literal hyperplane normalizer has index seven in the original L. -/
theorem hyperplane_normalizer_index (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U) :
    (L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)).relIndex L = 7 := by
  let := D.elementary
  let W := (U ⊓ V).subgroupOf V
  let Wlin := BinaryFlagPlaneAction.space W
  let a : L →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    BinaryFixedLine.linearAutEquiv.toMonoidHom.comp
      (V.normalizerMonoidHom.comp (inclusion D.normalizes))
  have ha : Function.Surjective a :=
    BinaryFixedLine.linearAutEquiv.surjective.comp (A.componentAut_surjective D)
  have hV : Module.finrank (ZMod 2) (Additive V) = 3 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hc
    rw [Nat.card_zmod,RigidityKernel.chosen_card A] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  have hW : Module.finrank (ZMod 2) Wlin = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Wlin)
    rw [Nat.card_zmod, ← Nat.card_congr (BinaryFlagPlaneAction.coordinates W).toEquiv] at hc
    change Nat.card W = _ at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ V ≤ V from inf_le_right)).toEquiv,
      C.hyperplane] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  have he : (L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf L =
      (BinaryLinear.parabolic Wlin).comap a := by
    ext g
    change ((g : G) ∈ L ∧ (g : G) ∈ normalizer ((U ⊓ V : Subgroup G) : Set G)) ↔
      ∀ w : Additive V, a g w ∈ Wlin ↔ w ∈ Wlin
    rw [and_iff_right g.property, mem_normalizer_iff]
    constructor
    · intro hg w
      exact (hg w.toMul).symm
    · intro hg x
      constructor
      · intro hx
        exact (hg (Additive.ofMul ⟨x,hx.2⟩)).mpr hx
      · intro hx
        have hxV : x ∈ V := (mem_normalizer_iff.mp (D.normalizes g.property) x).mpr hx.2
        exact (hg (Additive.ofMul ⟨x,hxV⟩)).mp hx
  change ((L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)).subgroupOf L).index = 7
  rw [he,index_comap_of_surjective _ ha]
  exact BinaryLinear.FourParabolicAction.threeSpace_hyperplane_index Wlin hV hW

/-- The literal hyperplane normalizer has order 192. -/
theorem hyperplane_normalizer_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    Nat.card (L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) : Subgroup G) = 192 := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) F L bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hyperplane_normalizer_index D A C,component_card D A B] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 7) hc

/-- The hyperplane normalizer is exactly the component normalizer of R. -/
theorem component_radical_normalizer (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    L ⊓ normalizer (radical T U : Set G) =
      L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hFN : F ≤ normalizer (radical T U : Set G) :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T F hTF).trans
      (sup_le B.residual_normalizes (sylow_normalizes_radical C))
  apply le_antisymm ?_ (le_inf inf_le_left hFN)
  intro g hg
  refine ⟨hg.1, ?_⟩
  change g ∈ normalizer ((U ⊓ V : Subgroup G) : Set G)
  rw [mem_normalizer_iff_map_conj_eq, ← radical_chosen_commutator A C hTV,
    map_commutator, mem_normalizer_iff_map_conj_eq.mp hg.2,
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes hg.1)]

/-- The central Sylow factor cancels from R inside L. -/
theorem radical_inf_component_card (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    Nat.card (radical T U ⊓ L : Subgroup G) = 16 := by
  let R := radical T U
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let S := (T : Subgroup G) ⊓ L
  have hZR : Z ≤ R := le_sup_right.trans B.centralizer_split.symm.le
  have hSZ : Z ≤ normalizer (S : Set G) :=
    (B.component_centralizer_central.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsplit : R = (R ⊓ L) ⊔ Z := by
    apply le_antisymm ?_ (sup_le inf_le_left hZR)
    intro r hr
    have ht : r ∈ S ⊔ Z := B.sylow_split ▸ hr.1
    have hp : r ∈ (S : Set G) * (Z : Set G) := by
      rwa [← coe_mul_of_right_le_normalizer_left S Z hSZ]
    obtain ⟨a,ha,z,hz,rfl⟩ := hp
    have haR : a ∈ R := by
      simpa only [mul_inv_cancel_right] using R.mul_mem hr (R.inv_mem (hZR hz))
    exact mul_mem_sup ⟨haR,ha.2⟩ hz
  have hdis : Disjoint (R ⊓ L) Z := B.sylow_disjoint.mono_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hnorm : Z ≤ normalizer ((R ⊓ L : Subgroup G) : Set G) :=
    (B.component_centralizer_central.trans
      (centralizer_le (inf_le_left.trans inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint (R ⊓ L) Z hnorm hdis
  rw [← hsplit] at hcard
  have hR : Nat.card R = 16 * Nat.card Z := by
    rw [show R = U ⊔ Z from B.centralizer_split,
      card_sup_eq_mul_of_normalizes_of_disjoint U Z
        ((hZR.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)) B.centralizer_disjoint,
      C.dimension]
    rfl
  rw [hR] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard.symm

/-- The component image in the literal radical quotient has order twelve. -/
theorem component_image_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Nat.card (image T U L) = 12 := by
  let N := normalizer (radical T U : Set G)
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hFN : F ≤ N := (component_radical_normalizer D A C B hTV).symm.le.trans inf_le_right
  have he : image T U L = image T U F := by
    apply congrArg (Subgroup.map (quotient T U))
    ext x
    change (x : G) ∈ L ↔ (x : G) ∈ F
    exact ⟨fun hx => (component_radical_normalizer D A C B hTV).le ⟨hx,x.property⟩,
      fun hx => hx.1⟩
  have hRF : radical T U ⊓ F = radical T U ⊓ L := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right
      ((inf_le_left.trans (inf_le_right.trans (centralizer_le inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)))
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (radical T U ⊓ F) F bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hRF,radical_inf_component_card C B,
    show Nat.card F = 192 from hyperplane_normalizer_card D A C B] at hc
  have hi : (radical T U ⊓ L).relIndex F = (radical T U).relIndex F := by
    rw [← hRF,inf_comm,inf_relIndex_left]
  rw [hi] at hc
  rw [he,image_card _ hFN]
  omega

/-- The image of the literal two-residual has order three. -/
theorem residual_image_card (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    Nat.card (image T U (rigidityHyperplaneResidual L U V)) = 3 := by
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  let Y := rigidityHyperplaneResidual L U V
  have hYF : Y ≤ F := map_subtype_le _
  have hd : Nat.card (image T U Y) ∣ 192 := by
    have hYcard : Nat.card (image T U Y) ∣ Nat.card Y := by
      have hh := (Y.subgroupOf (normalizer (radical T U : Set G))).card_map_dvd (quotient T U)
      rwa [Nat.card_congr (subgroupOfEquivOfLe B.residual_normalizes).toEquiv] at hh
    exact (hYcard.trans (card_dvd_of_le hYF)).trans (by rw [hyperplane_normalizer_card D A C B])
  have ho : Odd (Nat.card (image T U Y)) :=
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (card_dvd_of_le (residual_image_le_oddCore D A C B hTV hTI))
  have h3 := three_dvd_residual_image_card D A C B
  have hdiv3 : Nat.card (image T U Y) ∣ 3 :=
    (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd
  exact Nat.dvd_antisymm hdiv3 h3

/-- The normalizer orders and cubic residual for the original source data. -/
theorem source_component_normalizer_orders
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    L ⊓ normalizer (radical T U : Set G) =
        L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) ∧
      (L ⊓ normalizer (radical T U : Set G)).relIndex L = 7 ∧
      Nat.card (L ⊓ normalizer (radical T U : Set G) : Subgroup G) = 192 ∧
      Nat.card (image T U L) = 12 ∧
      Nat.card (image T U (rigidityHyperplaneResidual L U V)) = 3 := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hTV := ((structural G T L h).2.2 V D).1
  have he := component_radical_normalizer D A C B hTV
  exact ⟨he, he.symm ▸ hyperplane_normalizer_index D A C,
    he.symm ▸ hyperplane_normalizer_card D A C B, component_image_card D A C B hTV,
    residual_image_card D A C B hTV hTI⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
