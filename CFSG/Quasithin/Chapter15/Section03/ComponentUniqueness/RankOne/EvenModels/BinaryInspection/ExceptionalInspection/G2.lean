module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.Kernel
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.NormalFourObstruction

/-!
# Excluding the actual binary derived G₂ component

The source involution acts on the centerless component as a nonidentity
involution l. Because it centralizes S, l centralizes and belongs to the
component Sylow subgroup. Moreover C_L(l) lies in M: its elements commute
with the source involution. Consequently C_L(l) normalizes the original
four-group V₂, which lies in C_L(l) since V₂ lies in S.

Under the actual isomorphism with G₂(2)′, the centralizer of l is a conjugate
of the first derived parabolic. Its explicit Q₈ ◦ C₄ two-core and cubic
action rule out a normal four-group. This direct placement uses the retained
source involution, so no index-three classification or extra parabolic
hypothesis is required. All subgroup transports retain the derived carrier.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the n = 1
paragraph of 15.3.43, printed p.1140, and A.2.3--4, p.33. The intrinsic model
calculation and ATLAS attribution are in the imported NormalFourObstruction.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection

open Atlas.G2.BinaryParabolicPair

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The actual G₂(2)′ alternative is incompatible with the reduced source configuration. -/
theorem not_g2_derived (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hs : IsSimpleGroup L)
    (hi : ActsInner L z)
    (iso : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  have hZ : center L = ⊥ := binary_center_eq_bot c
    (.simple hs (.rankTwo (.g2_derived rfl iso)) hi)
  obtain ⟨l, hl⟩ := hi
  have hz2 : z ^ 2 = 1 := hz.order ▸ pow_orderOf_eq_one z
  have hl2 : l ^ 2 = 1 := by
    apply hZ.le
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hc : (l : G) ^ 2 * (x : G) * ((l : G) ^ 2)⁻¹ = x := by
      calc
        _ = (l : G) * ((l : G) * x * (l : G)⁻¹) * (l : G)⁻¹ := by
          simp only [pow_two]; group
        _ = z * ((l : G) * x * (l : G)⁻¹) * z⁻¹ := (hl (l*x*l⁻¹)).symm
        _ = z * (z * x * z⁻¹) * z⁻¹ := by rw [← hl x]
        _ = z ^ 2 * x * (z ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = x := by rw [hz2]; simp
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hc (x : L) : Commute l x ↔ Commute z (x : G) := by
    constructor
    · intro h
      have hh : z * (x : G) * z⁻¹ = x := by
        have he : (l : G) * (x : G) = (x : G) * (l : G) := congrArg Subtype.val h.eq
        rw [hl x, he]
        group
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro h
      apply Subtype.ext
      have hh : (l : G) * (x : G) * (l : G)⁻¹ = x := by
        rw [← hl x, h.eq]
        group
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hlne : l ≠ 1 := by
    intro he
    apply c.component_outside
    intro x hx
    apply hz.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    exact ((hc ⟨x, hx⟩).mp (by rw [he]; exact Commute.one_left _)).eq.symm
  obtain ⟨T, hT⟩ := component_sylow c
  have hlcentral : ∀ x ∈ T, Commute l x := by
    intro x hx
    apply (hc x).mpr
    have hxS : (x : G) ∈ S :=
      (hT.le (mem_map_of_mem L.subtype hx)).1
    exact (hz.central x hxS).symm
  have hlT : l ∈ T := by
    let : IsElementaryAbelian 2 (zpowers l) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hl2
    have hP := (IsElementaryAbelian.isPGroup 2 (zpowers l)).inf_normalizer_sylow T
    apply (hP.le ?_).2
    refine ⟨mem_zpowers _, Subgroup.centralizer_le_normalizer _ ?_⟩
    intro x hx
    exact (hlcentral x hx).eq.symm
  obtain ⟨e⟩ := iso
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let V := V₂.subgroupOf L
  let W := V.map e.toMonoidHom
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf (plane_le_component c)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hW : W ≤ centralizer ({e l} : Set DerivedModel) := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e x * e l = e l * e x
    have hlx : Commute l x := (hc x).mpr
      ((hz.central x (c.plane_two_le hx)).symm)
    simpa only [map_mul] using congrArg e hlx.eq.symm
  have hn : centralizer ({e l} : Set DerivedModel) ≤ normalizer (W : Set DerivedModel) := by
    intro x hx
    have hxl : Commute l (e.symm x) := by
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using (mem_centralizer_singleton_iff.mp hx).symm
    have hxM : (e.symm x : G) ∈ M :=
      hz.centralizer_le (mem_centralizer_singleton_iff.mpr ((hc _).mp hxl).eq.symm)
    have hxN : e.symm x ∈ normalizer (V : Set L) := by
      rw [← subgroupOf_normalizer_eq (plane_le_component c)]
      exact c.plane_two_normalized ⟨hxM, c.component_le (e.symm x).property⟩
    apply V.le_normalizer_map e.toMonoidHom
    exact mem_map.mpr ⟨e.symm x, hxN, e.apply_symm_apply x⟩
  have hcent : ∀ x ∈ T', Commute (e l) x := by
    rintro x ⟨y, hy, rfl⟩
    change e l * e y = e y * e l
    simpa only [map_mul] using congrArg e (hlcentral y hy).eq
  have hcard : Nat.card W = 4 := by
    change Nat.card (V.map e.toMonoidHom) = 4
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe (plane_le_component c)).toEquiv).trans
      c.plane_two_card
  exact no_normal_four_centralizer T' (x := e l)
    (mem_map_of_mem e.toMonoidHom hlT)
    (by rw [← map_pow, hl2, map_one])
    hcent (fun h => hlne (e.injective (h.trans e.map_one.symm))) W hW hn hcard

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection
