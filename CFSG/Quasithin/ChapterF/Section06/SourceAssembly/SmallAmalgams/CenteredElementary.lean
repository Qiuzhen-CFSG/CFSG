module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.MarkedCases
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterNormalRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.NormalFourObstruction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullElementaryEight
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.GroupTheory.CentralInvolutionMarking
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary normal subgroups at centered exceptional cubic vertices

At a vertex with a central involution, every normal elementary abelian
two-subgroup has order at most eight. The marked G₂ first vertices force
such a subgroup into their distinguished order-two subgroup. Their second
vertices have no central involution, as witnessed by the actual moving
root actor. The native M₁₂ rank bound handles both Mathieu vertices, and
the outer Mathieu normal-rank bound and trivial second center handle its
extension. All transports use the literal marked amalgam isomorphisms.

Source: Aschbacher--Smith F.1.12(I)(3,8,12,13), printed pp.262--263,
and the two-chief exclusion in 15.2.8, p.1110. The G₂ orientation argument
is adapted from Chapter14/Section02/SolvableAmalgam/SmallLocal/Orientation.
The coordinate facts come from the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open GreenBook
variable {G : Type*} [Group G] [Finite G]

private theorem no_central_involution_of_moving
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hc : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z a : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (ha : a ∈ H) (hm : a * z * a⁻¹ ≠ z) :
    ¬ ∃ t : H, t ∈ center H ∧ orderOf t = 2 := by
  rintro ⟨t,ht,ho⟩
  have he := central_involution_marking T H hTH hc t ht ho
  have htC : (t : G) ∈ centralizer (H : Set G) := by
    intro x hx
    exact congrArg H.subtype (mem_center_iff.mp ht ⟨x,hx⟩)
  have hzC : z ∈ centralizer (H : Set G) :=
    (zpowers_le.mpr htC) (he.symm ▸ hz)
  apply hm
  rw [hzC a ha,mul_inv_cancel_right]

private theorem second_g2_no_central_involution :
    ¬ ∃ t : Atlas.G2.BinaryCore.secondParabolic,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair in
    apply no_central_involution_of_moving commonSylow secondParabolic commonSylow_le_second
      (by change Nat.card (((omega₁ (center unipotent) (p := 2)).map (center unipotent).subtype).map unipotent.subtype) = 2
          rw [commonSylow_omega_center]; exact card_distinguished)
      z movingActor ?_ movingActor_mem movingActor_moves
    change z ∈ ((omega₁ (center unipotent) (p := 2)).map (center unipotent).subtype).map unipotent.subtype
    rw [commonSylow_omega_center]
    exact mem_zpowers z

private theorem second_g2_derived_no_central_involution :
    ¬ ∃ t : Atlas.G2.BinaryParabolicPair.derivedSecond,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair in
    apply no_central_involution_of_moving derivedSylow derivedSecond derivedSylow_le_second
      (by change Nat.card (((omega₁ (center (derivedSylow : Subgroup DerivedModel)) (p := 2)).map _).map _) = 2
          rw [derivedSylow_omega_center_in_model]; exact card_derivedDistinguished)
      ⟨z,rootA_one_mem_commutator⟩ ⟨movingActor,movingActor_mem_derived⟩ ?_
      movingActor_mem_derivedSecond movingActor_derived_moves
    change (⟨z,rootA_one_mem_commutator⟩ : DerivedModel) ∈
      ((omega₁ (center (derivedSylow : Subgroup DerivedModel)) (p := 2)).map _).map _
    rw [derivedSylow_omega_center_in_model]
    exact mem_zpowers z

private theorem transfer_central_involution {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ z : A, z ∈ center A ∧ orderOf z = 2) :
    ∃ z : B, z ∈ center B ∧ orderOf z = 2 := by
  obtain ⟨z,hz,ho⟩ := h
  exact ⟨e z,(MulEquivClass.apply_mem_center_iff e).mpr hz,(e.orderOf_eq z).trans ho⟩

private theorem normal_image {A K : Type*} [Group A] [Group K]
    (P : Subgroup K) (e : A ≃* P) (E : Subgroup A) [E.Normal] :
    P ≤ normalizer (E.map (P.subtype.comp e.toMonoidHom) : Set K) := by
  intro p hp
  obtain ⟨a,ha⟩ := e.surjective ⟨p,hp⟩
  have hm := E.le_normalizer_map (P.subtype.comp e.toMonoidHom)
    (mem_map_of_mem (P.subtype.comp e.toMonoidHom)
      (show a ∈ normalizer (E : Set A) from le_normalizer_of_normal (mem_top a)))
  change (e a : K) ∈ _ at hm
  rwa [ha] at hm

private theorem normal_first_card {A : Type*} [Group A] [Finite A]
    (e : A ≃* Atlas.G2.BinaryParabolicPair.derivedFirst)
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  open Atlas.G2.BinaryParabolicPair in
    let j := derivedFirst.subtype.comp e.toMonoidHom
    let W := E.map j
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map j
    have hb := card_le_of_le (elementary_normal_first_le W
      (by rintro x ⟨a,ha,rfl⟩; exact (e a).property) (normal_image _ e E))
    have hi : Function.Injective j := derivedFirst.subtype_injective.comp e.injective
    rw [Nat.card_zpowers,derivedInvolution_order,card_map_of_injective hi] at hb
    exact hb

private theorem normal_full_first_card {A : Type*} [Group A] [Finite A]
    (e : A ≃* Atlas.G2.BinaryParabolicPair.firstParabolic)
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore in
    let j := firstParabolic.subtype.comp e.toMonoidHom
    let W := E.map j
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map j
    have hb := card_le_of_le (elementary_normal_full_first_le W
      (by rintro x ⟨a,ha,rfl⟩; exact (e a).property) (normal_image _ e E))
    have hi : Function.Injective j := firstParabolic.subtype_injective.comp e.injective
    rw [card_distinguished,card_map_of_injective hi] at hb
    exact hb

private theorem m12_vertex_card {A : Type*} [Group A]
    (P : Subgroup Sporadic.Mathieu.M12) (e : A ≃* P)
    (E : Subgroup A) [IsElementaryAbelian 2 E] : Nat.card E ≤ 8 := by
  let j := P.subtype.comp e.toMonoidHom
  let W := E.map j
  have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
    Sporadic.Mathieu.m12_twoRank_le_three W (IsElementaryAbelian.map j)
  have hi : Function.Injective j := P.subtype_injective.comp e.injective
  rwa [card_map_of_injective hi] at hb

/-- In a cubic exceptional marked amalgam, a vertex with a central involution
has no normal elementary abelian subgroup of order sixteen. -/
theorem exceptional_centered_normal_elementary_card_le_eight
    {A B : Subgroup G}
    (hm : ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A)
    (hz : ∃ z : A, z ∈ center A ∧ orderOf z = 2)
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] : Nat.card E ≤ 8 := by
  have hZ : center A ≠ ⊥ := by
    rintro hbot
    obtain ⟨z,hz,ho⟩ := hz
    have he : z = 1 := mem_bot.mp (hbot ▸ hz)
    simp [he] at ho
  rcases hm with hm | hm
  · rcases hm with hm | hm | hm | hm
    · obtain ⟨f⟩ := hm
      exact (normal_first_card f.left E).trans (by decide)
    · obtain ⟨f⟩ := hm
      exact (normal_full_first_card f.left E).trans (by decide)
    · obtain ⟨f⟩ := hm
      exact m12_vertex_card _ (f.trans MathieuTwelve.concreteIso).left E
    · have hr := Mathieu.outer_first_normal_elementary_primeRank_le_three hm E
      have hc := (primeRank_le_iff_elementary_card_le E).mp hr ⊤
        (IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype (⊤ : Subgroup E).subtype_injective)
      simpa only [card_top, Nat.reducePow] using hc
  · rcases hm with hm | hm | hm | hm
    · obtain ⟨f⟩ := hm
      exact False.elim (second_g2_derived_no_central_involution
        (transfer_central_involution f.right hz))
    · obtain ⟨f⟩ := hm
      exact False.elim (second_g2_no_central_involution
        (transfer_central_involution f.right hz))
    · obtain ⟨f⟩ := hm
      exact m12_vertex_card _ (f.trans MathieuTwelve.concreteIso).right E
    · exact False.elim (hZ (Mathieu.outer_second_center_eq_bot hm))

end CFSG.Quasithin.ChapterF.SourceAssembly
