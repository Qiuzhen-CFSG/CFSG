module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Reduction
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Transporting the finite Omega stabilizer to the original intersection

An isomorphism from the literal NI action image to S₃ gives a surjection
from NI with exactly C_NI(V) as kernel. Order 36 for genuine Omega then
gives index six in M. A fixed point in the original plane outside its
central involution line supplies a complement; identifying its stabilizer
in the action image identifies NI with the original ambient centralizer.

These are transport results. They do not assume an arbitrary quotient of
NI, and they do not prove the missing finite point-stabilizer recognition.

Source: Aschbacher--Smith, 15.2.18(3ii)--19(2), printed p.1113.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- Restriction of the actual M-action, with codomain its actual NI image. -/
@[expose] noncomputable def intersectionAction (h : ChosenSmallSource T M Mc V)
    (I : Subgroup G) : (M ⊓ I : Subgroup G) →* intersectionImage h I where
  toFun n := ⟨action h ⟨n.val,n.property.1⟩,
    mem_map_of_mem (action h) (show (⟨n.val,n.property.1⟩ : M) ∈
      (M ⊓ I).subgroupOf M from n.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext ((action h).map_mul
    (⟨a.val,a.property.1⟩ : M) (⟨b.val,b.property.1⟩ : M))

/-- No image points are lost by using the original NI as domain. -/
theorem intersectionAction_surjective : Function.Surjective (intersectionAction hsource I) := by
  rintro ⟨g,m,hm,rfl⟩
  refine ⟨⟨m.val,hm⟩,?_⟩
  apply Subtype.ext
  rfl

/-- Its kernel is exactly the original centralizer of V inside NI. -/
theorem intersectionAction_ker :
    (intersectionAction hsource I).ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) := by
  ext n
  change intersectionAction hsource I n = 1 ↔ (n : G) ∈ centralizer (V : Set G)
  have hk := SetLike.ext_iff.mp (action_ker (hsource := hsource)) (⟨n.val,n.property.1⟩ : M)
  change action hsource ⟨n.val,n.property.1⟩ = 1 ↔ _ at hk
  constructor
  · intro hn
    exact hk.mp (congrArg Subtype.val hn)
  · intro hn
    exact Subtype.ext (hk.mpr hn)

/-- The faithful S₃ action is constructed from the actual image isomorphism. -/
theorem exists_symmetricThree_action_of_image_equiv
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    ∃ f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3), Function.Surjective f ∧
      f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) := by
  refine ⟨e.toMonoidHom.comp (intersectionAction hsource I),
    e.surjective.comp intersectionAction_surjective,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,intersectionAction_ker]

variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- NI contains the full M-action kernel, so its index is the image index. -/
theorem intersection_index_eq_image (hI : PlaneEscapes Mc ZS I) :
    (M ⊓ I).relIndex M = (intersectionImage hsource I).index := by
  have hk : (action hsource).ker ≤ (M ⊓ I).subgroupOf M := by
    rw [action_ker]
    intro x hx
    exact ⟨x.property,d.module_centralizer_le hI hx⟩
  exact (index_map_eq ((M ⊓ I).subgroupOf M)
    (actionHom M V hsource.prepared.normalized).rangeRestrict_surjective hk).symm

/-- Index six is computed from the genuine Omega and S₃ image orders. -/
theorem intersection_index_six_of_image_equiv (hI : PlaneEscapes Mc ZS I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    (M ⊓ I).relIndex M = 6 := by
  let := hsource.prepared.elementary
  obtain ⟨x,a,hx⟩ := ho.2.2.2.2
  have hD : Nat.card (internalActionImage M V hsource.prepared.normalized) = 36 :=
    (Nat.card_congr a.toEquiv).trans OrthogonalFourBinary.SylowGeometry.omega_card
  have hN : Nat.card (intersectionImage hsource I) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hh := (intersectionImage hsource I).card_mul_index
  rw [hN,hD] at hh
  rw [intersection_index_eq_image d hI]
  omega

omit d in
/-- A point stabilizer in the original faithful action. -/
@[expose] def pointStabilizer (h : ChosenSmallSource T M Mc V) (w : V) :
    Subgroup (internalActionImage M V h.prepared.normalized) where
  carrier a := a.val w = w
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.val (b.val w) = w; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.val.symm w = w
    exact a.val.symm_apply_eq.mpr ha.symm

/-- Equality in the faithful action lifts to the literal point centralizer. -/
theorem intersection_eq_centralizer_of_image (hI : PlaneEscapes Mc ZS I) (w : V)
    (he : intersectionImage hsource I = pointStabilizer hsource w) :
    M ⊓ I = M ⊓ centralizer (zpowers (w : G) : Set G) := by
  have hker : (action hsource).ker ≤ (M ⊓ I).subgroupOf M := by
    rw [action_ker]
    exact fun x hx => ⟨x.property,d.module_centralizer_le hI hx⟩
  have hpre : (pointStabilizer hsource w).comap (action hsource) =
      (M ⊓ I).subgroupOf M := by
    rw [←he,intersectionImage,comap_map_eq,sup_eq_left.mpr hker]
  have hcent (x : M) : x ∈ (pointStabilizer hsource w).comap (action hsource) ↔
      (x : G) ∈ centralizer (zpowers (w : G) : Set G) := by
    change (action hsource x).val w = w ↔ _
    rw [zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hh := congrArg Subtype.val hx
      change (x : G)*(w : G)*(x : G)⁻¹=(w : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hx
      apply Subtype.ext
      change (x : G)*(w : G)*(x : G)⁻¹=(w : G)
      rw [hx,mul_inv_cancel_right]
  ext x
  constructor
  · intro hx
    exact ⟨hx.1,(hcent ⟨x,hx.1⟩).mp (hpre ▸ hx)⟩
  · intro hx
    have hm := (hcent ⟨x,hx.1⟩).mpr hx.2
    rw [hpre] at hm
    exact hm

/-- A noncentral point of ZS gives a genuine complement to Ω₁Z(T) in ZS. -/
theorem plane_complement_of_point (hI : PlaneEscapes Mc ZS I) (w : G)
    (hw : w ∈ ZS) (hwZ : w ∉ centralInvolutions T) :
    zpowers w ≤ ZS ∧ Disjoint (centralInvolutions T) (zpowers w) ∧
      centralInvolutions T ⊔ zpowers w = ZS := by
  let := hsource.prepared.elementary
  have hw2 : w^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) w (d.geometry.plane_le hw)
  have hwc : w ∈ centralizer (centralInvolutions T : Set G) :=
    centralizer_le d.seed_le (d.plane_le_centralizer hw)
  have hcard := card_sup_zpowers_of_normalizing_involution (centralInvolutions T) w hw2 hwZ
    (Subgroup.centralizer_le_normalizer _ hwc)
  rw [(d.escape_index hI).1] at hcard
  have hle : centralInvolutions T ⊔ zpowers w ≤ ZS := sup_le d.seed_le (zpowers_le.mpr hw)
  refine ⟨zpowers_le.mpr hw,?_,eq_of_le_of_card_ge hle (by rw [d.geometry.plane_card,hcard])⟩
  classical
  apply disjoint_def.mpr
  intro z hzZ hzw
  have ho : orderOf w = 2 := orderOf_eq_prime hw2 (fun he => hwZ (he ▸ one_mem _))
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hzw
  obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hzw
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · simpa using hiz.symm
  · have he : w = z := by simpa using hiz
    exact (hwZ (he.symm ▸ hzZ)).elim

/-- The real pushing-up consumer, with the action constructed above. -/
theorem pushingUp_of_image_equiv (hI : PlaneEscapes Mc ZS I)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv e
  exact d.intersection_pushingUpSetup_of_symmetricThree hI f hf hker

/-- The component-selection consumer retains the original residual normalizer. -/
theorem escaping_component_of_image_equiv (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup G, X ∈ Chapter1.cComponentsIn I ∧
      IsQuasisimple (X ⧸ pCore 2 X) ∧ generalizedFitting X = pCore 2 X ∧
      ¬ X ≤ M ⊓ I ∧ (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv e
  exact d.escaping_component_with_residual_normalization hI hfit f hf hker hno

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
