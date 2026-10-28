module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The faithful action of a subgroup normalizer

The quotient N(K)/C(K) acts faithfully on K, and its copy of K is exactly
the inverse image of Inn(K). Commutator generation therefore puts a subgroup
inside that copy whenever the outer action is abelian. A product of three
conjugates of an involution detects distinct involutions in this quotient.

These are the action and four-group calculations in Aschbacher–Smith,
combined manuscript of 1 March 2004, proof of 13.6.6, printed pp.926–927.
No component classification is used here.
-/

@[expose] public section

namespace Subgroup.NormalizerAction
open Subgroup
open scoped IsMulCommutative
variable {H : Type*} [Group H] (K : Subgroup H)

/-- The kernel is the centralizer inside the actual normalizer. -/
abbrev C : Subgroup (normalizer (K : Set H)) :=
  (centralizer (K : Set H)).subgroupOf (normalizer (K : Set H))

/-- The literal normalizer/centralizer quotient. -/
abbrev Star := normalizer (K : Set H) ⧸ C K

def quotient : normalizer (K : Set H) →* Star K := QuotientGroup.mk' (C K)

def action : Star K →* MulAut K :=
  QuotientGroup.lift (C K) K.normalizerMonoidHom (by rw [normalizerMonoidHom_ker])

theorem action_quotient (x : normalizer (K : Set H)) :
    action K (quotient K x) = K.normalizerMonoidHom x := rfl

theorem action_injective : Function.Injective (action K) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker]

theorem quotient_eq_one_iff (x : normalizer (K : Set H)) :
    quotient K x = 1 ↔ (x : H) ∈ centralizer (K : Set H) :=
  QuotientGroup.eq_one_iff x

/-- K*, with its actual embedding in N(K)/C(K). -/
def componentImage : Subgroup (Star K) :=
  (K.subgroupOf (normalizer (K : Set H))).map (quotient K)

def componentMap : K →* Star K := (quotient K).comp (inclusion K.le_normalizer)

theorem componentMap_ker : (componentMap K).ker = center K := by
  ext k
  change quotient K (inclusion K.le_normalizer k) = 1 ↔ k ∈ center K
  rw [quotient_eq_one_iff]
  constructor
  · intro hk
    exact mem_center_iff.mpr fun x => Subtype.ext (mem_centralizer_iff.mp hk x x.property)
  · intro hk
    exact mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (mem_center_iff.mp hk ⟨x, hx⟩)

theorem componentMap_range : (componentMap K).range = componentImage K := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨inclusion K.le_normalizer k, k.property, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The component image is genuinely K/Z(K). This is the equivalence
through which model identifications must be transported. -/
noncomputable def componentCentralQuotientEquiv : (K ⧸ center K) ≃* componentImage K :=
  (QuotientGroup.quotientMulEquivOfEq (componentMap_ker K).symm).trans
    ((QuotientGroup.quotientKerEquivRange (componentMap K)).trans
      (MulEquiv.subgroupCongr (componentMap_range K)))

theorem componentCentralQuotientEquiv_mk (k : K) :
    (componentCentralQuotientEquiv K (QuotientGroup.mk' (center K) k) : Star K) =
      quotient K (inclusion K.le_normalizer k) := rfl

theorem action_map_componentImage :
    (componentImage K).map (action K) = MulAut.innerSubgroup K := by
  rw [componentImage, map_map]
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by ext y; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, K.le_normalizer x.property⟩, x.property, by ext y; rfl⟩

theorem action_mem_inner_iff (x : Star K) :
    action K x ∈ MulAut.innerSubgroup K ↔ x ∈ componentImage K := by
  rw [← action_map_componentImage]
  constructor
  · rintro ⟨y, hy, he⟩
    exact action_injective K he ▸ hy
  · exact mem_map_of_mem _

/-- Innerness passes from D to an element of ZD when Z centralizes K.
All images are under the literal normalizer quotient map. -/
theorem quotient_mem_componentImage_of_central_supplement
    (Z D : Subgroup H) (hZ : Z ≤ centralizer (K : Set H))
    (hD : D ≤ normalizer (K : Set H))
    (himage : (D.subgroupOf (normalizer (K : Set H))).map (quotient K) ≤ componentImage K)
    (x : normalizer (K : Set H)) (hx : (x : H) ∈ Z ⊔ D) :
    quotient K x ∈ componentImage K := by
  let U : Subgroup H := ((componentImage K).comap (quotient K)).map
    (normalizer (K : Set H)).subtype
  have hZU : Z ≤ U := by
    intro z hz
    let zN : normalizer (K : Set H) := ⟨z, (centralizer_le_normalizer _ :
      centralizer (K : Set H) ≤ normalizer (K : Set H)) (hZ hz)⟩
    refine ⟨zN, ?_, rfl⟩
    change quotient K zN ∈ componentImage K
    rw [(quotient_eq_one_iff K zN).mpr (hZ hz)]
    exact one_mem _
  have hDU : D ≤ U := by
    intro d hd
    let dN : normalizer (K : Set H) := ⟨d, hD hd⟩
    exact ⟨dN, himage ⟨dN, hd, rfl⟩, rfl⟩
  obtain ⟨y, hy, he⟩ := (sup_le hZU hDU) hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

/-- Centrality modulo a subgroup centralizing K passes to the faithful
K-action. The first quotient need not itself be an action on K. -/
theorem quotient_commute_of_quotient_commute (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ centralizer (K : Set H))
    (a b : normalizer (K : Set H))
    (hab : Commute (QuotientGroup.mk' Z (a : H))
      (QuotientGroup.mk' Z (b : H))) :
    Commute (quotient K a) (quotient K b) := by
  change quotient K a * quotient K b = quotient K b * quotient K a
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply hZ
  apply QuotientGroup.eq_iff_div_mem.mp
  change QuotientGroup.mk' Z ((a : H) * (b : H)) =
    QuotientGroup.mk' Z ((b : H) * (a : H))
  simpa only [map_mul] using hab.eq

/-- A subgroup generated by commutators has trivial image in an abelian
outer automorphism group. This gives containment in K*, not just a label
asserting that its automorphisms are inner. -/
theorem commutator_generated_image_le
    [IsMulCommutative (MulAut.Outer K)]
    (D T : Subgroup (normalizer (K : Set H))) (hD : ⁅D, T⁆ = D) :
    D.map (quotient K) ≤ componentImage K := by
  let f : normalizer (K : Set H) →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp K.normalizerMonoidHom
  have hf : D.map f = ⊥ := by
    rw [← hD, map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr fun _ _ =>
      mem_centralizer_iff.mpr fun _ _ => mul_comm _ _
  rintro _ ⟨d, hd, rfl⟩
  apply (action_mem_inner_iff K _).mp
  apply (QuotientGroup.eq_one_iff _).mp
  have hh := mem_map_of_mem f hd
  rw [hf] at hh
  exact hh

end Subgroup.NormalizerAction

namespace MonoidHom
variable {H D : Type*} [Group H] [Group D]

/-- Three conjugates whose product is killed cannot have the same image
as an element centralizing the conjugator, unless the involution is killed. -/
theorem map_ne_of_three_conjugate_product (f : H →* D) (a z c : H)
    (hz2 : z * z = 1) (hproduct : f (z * MulAut.conj c z *
      MulAut.conj (c ^ 2) z) = 1)
    (hac : Commute (f a) (f c)) (hz : f z ≠ 1) : f a ≠ f z := by
  intro he
  have hcz : Commute (f c) (f z) := (he ▸ hac).symm
  have hconj : f (MulAut.conj c z) = f z := by
    change f (c * z * c⁻¹) = f z
    rw [map_mul, map_mul, map_inv, hcz.eq, mul_inv_cancel_right]
  have hconj2 : f (MulAut.conj (c ^ 2) z) = f z := by
    change f (c ^ 2 * z * (c ^ 2)⁻¹) = f z
    rw [map_mul, map_mul, map_inv, map_pow, (hcz.pow_left 2).eq,
      mul_inv_cancel_right]
  rw [map_mul, map_mul, hconj, hconj2, ← map_mul, hz2, map_one, one_mul] at hproduct
  exact hz hproduct

end MonoidHom

namespace Subgroup.NormalizerAction
open Subgroup
variable {H : Type*} [Group H] (K : Subgroup H)

/-- The actual image of a two-subgroup intersected with N(K). -/
def sylowImage (T : Subgroup H) : Subgroup (Star K) :=
  (T.subgroupOf (normalizer (K : Set H))).map (quotient K)

/-- The literal subgroup generated by the two action images. -/
def four (a z : normalizer (K : Set H)) : Subgroup (Star K) :=
  closure ({quotient K a, quotient K z} : Set (Star K))

/-- Construct the central four-group from the three-conjugate product,
nontrivial component actions, and the two centrality statements. -/
theorem central_four (T : Subgroup H) (a z c : normalizer (K : Set H))
    (haT : (a : H) ∈ T) (hzT : (z : H) ∈ T)
    (ha2 : a * a = 1) (hz2 : z * z = 1)
    (ha : (a : H) ∉ centralizer (K : Set H))
    (hz : (z : H) ∉ centralizer (K : Set H))
    (hac : Commute (quotient K a) (quotient K c))
    (hproduct : quotient K (z * MulAut.conj c z * MulAut.conj (c ^ 2) z) = 1)
    (haC : ∀ t : normalizer (K : Set H), (t : H) ∈ T →
      Commute (quotient K a) (quotient K t))
    (hzC : ∀ t : normalizer (K : Set H), (t : H) ∈ T →
      Commute (quotient K z) (quotient K t)) :
    IsKleinFour (four K a z) ∧
      four K a z ≤ (center (sylowImage K T)).map (sylowImage K T).subtype := by
  have ha1 : quotient K a ≠ 1 := fun he => ha ((quotient_eq_one_iff K a).mp he)
  have hz1 : quotient K z ≠ 1 := fun he => hz ((quotient_eq_one_iff K z).mp he)
  have hne := (quotient K).map_ne_of_three_conjugate_product a z c hz2 hproduct hac hz1
  refine ⟨isKleinFour_closure_pair _ _
    (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hz2, map_one])
    ha1 hz1 hne (haC z hzT), ?_⟩
  have hin (x : normalizer (K : Set H)) (hxT : (x : H) ∈ T)
      (hxC : ∀ t : normalizer (K : Set H), (t : H) ∈ T →
        Commute (quotient K x) (quotient K t)) :
      quotient K x ∈ (center (sylowImage K T)).map (sylowImage K T).subtype := by
    have hx : quotient K x ∈ sylowImage K T := ⟨x, hxT, rfl⟩
    refine ⟨⟨quotient K x, hx⟩, mem_center_iff.mpr ?_, rfl⟩
    rintro ⟨y, t, ht, rfl⟩
    exact Subtype.ext (hxC t ht).eq.symm
  apply (closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact hin a haT haC
  · exact hx ▸ hin z hzT hzC

end Subgroup.NormalizerAction
