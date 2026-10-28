module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.FromModel
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Exact indices for the favorable cubic orbit pair

The original opposite orbit has elementary image of order at most eight.
An even involution in its six-letter image has a commutator of order five.
Its lift in the actual quotient action has order divisible by five, so
prime-degree displacement and the commutator rank inequality force the
involution to move at least two dimensions. This argument works whether
the action kernel is Q or the retained cubic extension E.

The literal fixed-preimage index is the corresponding power of two. The
strict favorable-pair inequality therefore forces both orbit images to
have order eight and that preimage to have index four, exactly as in MS93
(3.6), printed p.871. CubicOrbit.Source supplies these exact indices to the
remaining intersection, movement and recognition proof on the selected
original pair. Those facts and larger-distance exhaustion remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk

private def testInvolution : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def testPartner : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 3 4
private theorem testInvolution_order : orderOf testInvolution = 2 :=
  orderOf_eq_prime (by decide) (by decide)
private theorem testCommutator_order : orderOf ⁅testInvolution.val,testPartner⁆ = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime <;> decide +kernel

private theorem even_involution_commutator_five
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ alternatingGroup (Fin 6)) (ho : orderOf a = 2) :
    ∃ b : Equiv.Perm (Fin 6), orderOf ⁅a,b⁆ = 5 := by
  let a' : alternatingGroup (Fin 6) := ⟨a,ha⟩
  have ho' : orderOf a' = 2 :=
    (orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.coe_injective a').symm.trans ho
  obtain ⟨c,hc⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj testInvolution a' testInvolution_order ho')
  let f := (MulAut.conj c.val).toMonoidHom
  have hfa : f testInvolution.val = a := congrArg Subtype.val hc
  refine ⟨f testPartner,?_⟩
  rw [←hfa,←map_commutatorElement,orderOf_injective f (MulAut.conj c.val).injective]
  exact testCommutator_order

private theorem fixedCodim_mono_local
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    {A B : Subgroup H} (hab : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hd := Submodule.finrank_mono (fixedSpace_antitone ρ hab)
  have ha := fixedCodim_add_finrank ρ A
  have hb := fixedCodim_add_finrank ρ B
  omega

include h e hz hk in
/-- An even nonidentity involution in the six-letter image moves at least two
dimensions on the actual orbit quotient. An order-five commutator proves
this directly, including when the action kernel is Q and E/Q remains visible. -/
theorem orbit_even_involution_fixedCodim_lower
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) (a : M)
    (ha : π a ∈ alternatingGroup (Fin 6)) (ho : orderOf (π a) = 2) :
    letI := o.quotient_elementary
    2 ≤ fixedCodim (orbitAutomorphismRepresentation h o)
      (zpowers (orbitQuotientAction h o a)) := by
  let := o.quotient_elementary
  let β := orbitQuotientAction h o
  let ρ := orbitAutomorphismRepresentation h o
  obtain ⟨u,hu⟩ := even_involution_commutator_five (π a) ha ho
  obtain ⟨b,hb⟩ := projection_surjective_of_distanceTwo h e hz hk o.distance_two u
  let v := ⁅a,b⁆
  have hv : orderOf (π v) = 5 := by simpa only [v,map_commutatorElement,hb] using hu
  have hdvd : 5 ∣ orderOf (β v) := by
    rw [←hv]
    apply orderOf_dvd_of_pow_eq_one
    rw [←map_pow]
    have hker : v ^ orderOf (β v) ∈ β.ker := by
      change β (v ^ orderOf (β v)) = 1
      rw [map_pow,pow_orderOf_eq_one]
    have hh := (orbitQuotientAction_kernel_bounds h e hz hk o).2 hker
    change v ^ orderOf (β v) ∈ (π).ker
    rwa [projection_kernel]
  let y := β v ^ (orderOf (β v) / 5)
  have hy : orderOf y = 5 := orderOf_pow_orderOf_div (orderOf_pos (β v)).ne' hdvd
  have hlo := prime_order_le_fixedCodim ρ (orbitAutomorphismRepresentation_injective h o)
    (by decide : Nat.Prime 5) (by decide) y hy
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hmon := fixedCodim_mono_local ρ (zpowers_le.mpr
    (show y ∈ zpowers (β v) from pow_mem (mem_zpowers _) _))
  have hhi := fixedCodim_commutator_le_twice ρ (β a) (β b)
  have he : β v = β a * β b * (β a)⁻¹ * (β b)⁻¹ := map_commutatorElement β a b
  rw [←he] at hhi
  change 2 ≤ fixedCodim ρ (zpowers (β a))
  omega

include h in
/-- The graph fixed-preimage index is the fixed codimension of the actual
quotient action, without a permutation-action descent assumption. -/
theorem orbit_actor_fixed_index
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    letI := o.quotient_elementary
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) =
        2 ^ fixedCodim (orbitAutomorphismRepresentation h o)
          ((o.opposite.comap (embedM T)).map (orbitQuotientAction h o)) := by
  let := o.quotient_elementary
  let A := criticalOrbitNative T o.c o.b
  let B := o.opposite.comap (embedM T)
  let q := (orbitQuotientAction h o).comp (⊤ : Subgroup M).subtype
  let ρ := orbitAutomorphismRepresentation h o
  have hcomp : ρ.comp q = orbitRepresentation T o.c o.b := by ext g v; rfl
  have hs : BinaryConjugationSection ⊤ A (orbitLayer T) (ρ.comp q) := by
    rw [hcomp]
    exact orbitSection T o.c o.b o.layer_le
  have hmap : (B.subgroupOf ⊤).map q = B.map (orbitQuotientAction h o) := by
    rw [show q = (orbitQuotientAction h o).comp (⊤ : Subgroup M).subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le (show B ≤ ⊤ from le_top)]
  have hZ : (orbitLayer T).map (embedM T) = Z T (alpha T) := map_comap_eq_self
    ((Z_le_stabilizer T (alpha T)).trans_eq (stabilizer_m_base T))
  have hC := Natural.Exhaustion.DistanceTwo.Recognition.PermutationModel.commutatorPreimage_map_injective
    (embedM T) (embedM_injective T) A B (orbitLayer T) le_normalizer_of_normal
  rw [o.opposite_map,hZ] at hC
  change (commutatorPreimage (A.map (embedM T)) o.opposite (Z T (alpha T))).relIndex
    (A.map (embedM T)) = _
  rw [←hC,relIndex_map_map_of_injective _ _ (embedM_injective T)]
  have hi := BinaryConjugationSection.fixed_index_image ρ q hs B le_top
  rwa [hmap] at hi

private theorem exists_even_ne_one_of_card_gt_two
    (A : Subgroup (Equiv.Perm (Fin 6))) (hcard : 2 < Nat.card A) :
    ∃ a : Equiv.Perm (Fin 6), a ∈ A ∧ a ∈ alternatingGroup (Fin 6) ∧ a ≠ 1 := by
  by_contra! hn
  let f := Equiv.Perm.sign.comp A.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply hn a a.property
    rw [Equiv.Perm.mem_alternatingGroup]
    exact ha
  have hh := Nat.card_le_card_of_injective f hf
  have htwo : Nat.card ℤˣ = 2 := by simp
  rw [htwo] at hh
  omega

include h e hz hk in
/-- The strict favorable-pair comparison has the exact source indices:
both orbit images have order eight and the fixed preimage has index four.
The proof retains both possible kernels of the actual later orbit action. -/
theorem preliminary_orbit_indices
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    (Q T (alpha T)).relIndex o.opposite = 8 ∧
    (Q T o.c).relIndex (criticalOrbit T o.c o.b) = 8 ∧
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) = 4 := by
  let := o.quotient_elementary
  let B := o.opposite.comap (embedM T)
  let C := B.map (orbitQuotientAction h o)
  let A := B.map π
  let ρ := orbitAutomorphismRepresentation h o
  have hCcard : Nat.card C = (Q T (alpha T)).relIndex o.opposite :=
    orbitQuotientAction_opposite_card h e hz hk o
  have hAcard : Nat.card A = (Q T (alpha T)).relIndex o.opposite :=
    opposite_permutation_image_card h e hz hk o
  have hstrict : 2 * 2 ^ fixedCodim ρ C ≤ Nat.card C := by
    rw [hCcard,←orbit_actor_fixed_index h o]
    exact o.strict_index.trans o.ordered_index
  have hCne : C ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hstrict
    have hp : 0 < 2 ^ fixedCodim ρ ⊥ := by positivity
    omega
  have hpos := fixedCodim_pos_of_faithful ρ (orbitAutomorphismRepresentation_injective h o) hCne
  have hpow : 2 ≤ 2 ^ fixedCodim ρ C :=
    show 2^1 ≤ _ from Nat.pow_le_pow_right (by decide) hpos
  have hAgt : 2 < Nat.card A := by rw [hAcard,←hCcard];omega
  obtain ⟨a,haA,haEven,hane⟩ := exists_even_ne_one_of_card_gt_two A hAgt
  let := opposite_permutation_image_elementary h e hz hk o
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a haA) hane
  obtain ⟨b,hb,he⟩ := haA
  have hbEven : π b ∈ alternatingGroup (Fin 6) := he ▸ haEven
  have hbo : orderOf (π b) = 2 := he ▸ hao
  have hlo := orbit_even_involution_fixedCodim_lower h e hz hk o b hbEven hbo
  have hmon := fixedCodim_mono_local ρ (zpowers_le.mpr
    (show orbitQuotientAction h o b ∈ C from mem_map_of_mem _ hb))
  have hfour : 4 ≤ 2 ^ fixedCodim ρ C :=
    show 2^2 ≤ _ from Nat.pow_le_pow_right (by decide) (hlo.trans hmon)
  have hi := orbit_actor_fixed_index h o
  have hbounds := preliminary_orbit_index_bounds h e hz hk o
  have hs := o.strict_index
  have ho := o.ordered_index
  dsimp only [ρ,C,B] at hfour
  omega

include h e hz hk in
/-- The selected original pair has the exact two order-eight images and
index-four fixed preimage required for the remaining whole-orbit argument. -/
theorem selectedOrbitPair_indices (hb : sourceDistance h = 2) :
    let o := selectedOrbitPair h e hz hk hb
    (Q T (alpha T)).relIndex o.opposite = 8 ∧
    (Q T o.c).relIndex (criticalOrbit T o.c o.b) = 8 ∧
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) = 4 :=
  preliminary_orbit_indices h e hz hk _

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
