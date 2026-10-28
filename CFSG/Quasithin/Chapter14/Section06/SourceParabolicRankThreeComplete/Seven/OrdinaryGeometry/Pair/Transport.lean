module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Inputs
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation

/-!
# Transporting the original pair, plane and central point

A simultaneous permutation relabelling preserves the whole conjugation chart.
The literal moved four-group becomes a transitive binary plane, and a chosen
nonidentity element of the original order-two point stays fixed by the actual
second parabolic. Its fixation excludes the reversed partition orientation.
Finally M = N_G(V) recovers the entire first intersection image from the plane,
while Mc = C_G(Z) supplies the required point fixation.

The two finite recognition contracts remain explicit here. This is their
consumer, not an unconditional proof of the source pair classification.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
universe u
variable {G : Type*} [Group G] {J C W : Subgroup G}

noncomputable def relabel (c : Chart J C W) (g : Equiv.Perm (Fin 7)) : Chart J C W where
  moduleEquiv := c.moduleEquiv.trans
    (LinearEquiv.ofBijective (action g) (action.apply_bijective g)).toAddEquiv.toMultiplicative
  actor := (MulAut.conj g).toMonoidHom.comp c.actor
  normalized := c.normalized
  equivariant := by
    intro j w
    change action g (c.moduleEquiv _).toAdd =
      action (g * c.actor j * g⁻¹) (action g (c.moduleEquiv w).toAdd)
    rw [c.equivariant]
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  component_image := by
    rw [← map_map, c.component_image]
    apply le_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem p hp g
    · intro p hp
      refine ⟨g⁻¹ * p * g, ?_, ?_⟩
      · have hh := (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem p hp g⁻¹
        rw [inv_inv] at hh
        exact hh
      · change g * (g⁻¹ * p * g) * g⁻¹ = p
        group

noncomputable def planeImage (c : Chart J C W) (V : Subgroup G) : Submodule (ZMod 2) Space :=
  AddSubgroup.toZModSubmodule 2 ((V.subgroupOf W).map c.moduleEquiv.toMonoidHom).toAddSubgroup'

lemma mem_planeImage (c : Chart J C W) (V : Subgroup G) (w : W) :
    (c.moduleEquiv w).toAdd ∈ planeImage c V ↔ (w : G) ∈ V := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact c.moduleEquiv.injective he ▸ hu
  · intro hw
    exact ⟨w,hw,rfl⟩

lemma planeImage_card (c : Chart J C W) (V : Subgroup G) (hV : V ≤ W) :
    Nat.card (planeImage c V) = Nat.card V := by
  let D := (V.subgroupOf W).map c.moduleEquiv.toMonoidHom
  have he : Nat.card (planeImage c V) = Nat.card D :=
    Nat.card_congr {
      toFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
      invFun v := ⟨v.val.toAdd,v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact he.trans ((card_map_of_injective c.moduleEquiv.injective).trans
    (Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv))

lemma planeImage_invariant (c : Chart J C W) (A V : Subgroup G)
    (hAV : A ≤ normalizer (V : Set G)) :
    ∀ a ∈ (A.subgroupOf J).map c.actor, ∀ v ∈ planeImage c V,
      action a v ∈ planeImage c V := by
  rintro _ ⟨a,ha,rfl⟩ v ⟨w,hw,he⟩
  refine ⟨⟨a.val * w.val * a.val⁻¹,
    le_normalizer_iff.mp c.normalized a a.property w w.property⟩,
    le_normalizer_iff.mp hAV a ha w hw, ?_⟩
  apply Multiplicative.toAdd.injective
  exact (c.equivariant a w).trans
    (congrArg (action (c.actor a)) (congrArg Multiplicative.toAdd he))

lemma planeImage_transitive [Finite G] (c : Chart J C W)
    (A V R : Subgroup G) (hRJ : R ≤ J) (hRA : R ≤ A)
    (hRV : R ≤ normalizer (V : Set G)) (hVW : V ≤ W)
    (hV : Nat.card V = 4) (hR : IsPPerfect 2 R) (hm : ⁅V,R⁆ = V) :
    ∀ v ∈ planeImage c V, v ≠ 0 → ∀ w ∈ planeImage c V, w ≠ 0 →
      ∃ a ∈ (A.subgroupOf J).map c.actor, action a v = w := by
  let P := planeImage c V
  let τ := action.comp (c.actor.comp (inclusion hRJ))
  have hi (a : R) : ∀ v ∈ P, τ a v ∈ P :=
    planeImage_invariant c R V hRV _ ⟨inclusion hRJ a,a.property,rfl⟩
  let σ := Representation.subrepresentation τ P hi
  have hd : Module.finrank (ZMod 2) P = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
    rw [Nat.card_zmod, planeImage_card c V hVW, hV] at hh
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh.symm
  have hnon : ∃ a, σ a ≠ 1 := by
    by_contra ht
    push Not at ht
    have hc : R ≤ centralizer (V : Set G) := by
      apply le_centralizer_iff.mpr
      intro v hv a ha
      let vW : W := ⟨v,hVW hv⟩
      have hvP : (c.moduleEquiv vW).toAdd ∈ P := ⟨vW,hv,rfl⟩
      have hh := congrArg Subtype.val (LinearMap.congr_fun (ht ⟨a,ha⟩) ⟨_,hvP⟩)
      change action (c.actor ⟨a,hRJ ha⟩) (c.moduleEquiv vW).toAdd =
        (c.moduleEquiv vW).toAdd at hh
      rw [←c.equivariant] at hh
      have he : a * v * a⁻¹ = v := congrArg Subtype.val
        (c.moduleEquiv.injective (Multiplicative.toAdd.injective hh))
      exact mul_inv_eq_iff_eq_mul.mp he
    have hz : V = ⊥ := by
      rw [←hm,commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact hc
    rw [hz,card_bot] at hV
    omega
  intro v hv hv0 w hw hw0
  obtain ⟨a,ha⟩ := Representation.nonzero_orbit_of_twoPerfect_plane hR hd σ hnon
    ⟨v,hv⟩ (fun h => hv0 (congrArg Subtype.val h))
    ⟨w,hw⟩ (fun h => hw0 (congrArg Subtype.val h))
  exact ⟨c.actor (inclusion hRJ a), ⟨inclusion hRJ a,hRA a.property,rfl⟩,
    congrArg Subtype.val ha⟩

lemma fixes_coordinate (c : Chart J C W) (Q Z : Subgroup G)
    (hQ : Q ≤ centralizer (Z : Set G)) (z : W) (hz : (z : G) ∈ Z) :
    (Q.subgroupOf J).map c.actor ≤ pointStabilizer (c.moduleEquiv z).toAdd := by
  rintro _ ⟨q,hq,rfl⟩
  change action (c.actor q) (c.moduleEquiv z).toAdd = (c.moduleEquiv z).toAdd
  rw [←c.equivariant]
  apply congrArg (fun w : W => (c.moduleEquiv w).toAdd)
  apply Subtype.ext
  change q.val * z.val * q.val⁻¹ = z.val
  have hh : z.val * q.val = q.val * z.val := mem_centralizer_iff.mp (hQ hq) z.val hz
  rw [←hh, mul_inv_cancel_right]
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair

public section
open Subgroup BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
universe u
variable {G : Type u} [Group G] [Finite G] {J C W P Q V Z M Mc : Subgroup G}

lemma normalizer_image_of_plane (c : Chart J C W) (hVW : V ≤ W)
    (hp : planeImage c V = Submodule.span (ZMod 2) {firstFour,secondFour})
    (hr : PlaneRecognition) :
    ((J ⊓ normalizer (V : Set G)).subgroupOf J).map c.actor = c.actor.range ⊓ lambda := by
  apply le_antisymm
  · rintro _ ⟨j,hj,rfl⟩
    refine ⟨⟨j,rfl⟩, (hr.stabilizer _).mp ?_⟩
    intro v hv
    rw [←hp] at hv ⊢
    exact planeImage_invariant c (normalizer (V : Set G)) V le_rfl _
      ⟨j,hj.2,rfl⟩ v hv
  · rintro a ⟨⟨j,rfl⟩,hj⟩
    refine ⟨j, ⟨j.property,?_⟩,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨v,hv,rfl⟩
      let vW : W := ⟨v,hVW hv⟩
      have hvP : (c.moduleEquiv vW).toAdd ∈ planeImage c V :=
        (mem_planeImage c V vW).mpr hv
      have hh := (hr.stabilizer _).mpr hj _ (hp ▸ hvP)
      rw [←hp,←c.equivariant] at hh
      exact (mem_planeImage c V _).mp hh
    · exact (card_map_of_injective (MulAut.conj j.val).injective).ge

lemma point_coordinates (c : Chart J C W) (h : LocalData J P Q V Z M Mc)
    (hVW : V ≤ W) :
    ∃ z : W, (z : G) ∈ Z ∧ (c.moduleEquiv z).toAdd ≠ 0 ∧
      (c.moduleEquiv z).toAdd ∈ planeImage c V ∧
      (Q.subgroupOf J).map c.actor ≤ pointStabilizer (c.moduleEquiv z).toAdd ∧
      ((J ⊓ Mc).subgroupOf J).map c.actor ≤ pointStabilizer (c.moduleEquiv z).toAdd := by
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp h.point_card
  let zW : W := ⟨z.val,hVW (h.point_le z.property)⟩
  have hn : (c.moduleEquiv zW).toAdd ≠ 0 := by
    intro he
    have hw : zW = 1 := c.moduleEquiv.injective
      ((Multiplicative.toAdd.injective he).trans (map_one c.moduleEquiv).symm)
    apply hz
    apply Subtype.ext
    exact congrArg (fun w : W => (w : G)) hw
  refine ⟨zW,z.property,hn,(mem_planeImage c V zW).mpr (h.point_le z.property),
    fixes_coordinate c Q Z h.second_fixes zW z.property,?_⟩
  exact fixes_coordinate c (J ⊓ Mc) Z
    (inf_le_right.trans_eq h.centralizer_eq) zW z.property

lemma marked_of_recognitions
    (hc : CubicPairRecognition.{u}) (hr : PlaneRecognition)
    (c : Chart J C W) (h : LocalData J P Q V Z M Mc) (hVW : V ≤ W) :
    ∃ c' : Chart J C W,
      (∀ w : W, (w : G) ∈ V ↔
        (c'.moduleEquiv w).toAdd ∈ Submodule.span (ZMod 2) {firstFour,secondFour}) ∧
      ((J ⊓ M).subgroupOf J).map c'.actor = c'.actor.range ⊓ lambda ∧
      (Q.subgroupOf J).map c'.actor = c'.actor.range ⊓ theta ∧
      ((J ⊓ Mc).subgroupOf J).map c'.actor ≤ pointStabilizer firstFour := by
  have hfull : alternatingGroup (Fin 7) ≤ c.actor.range := by
    rw [←c.component_image]
    exact map_le_range _ _
  obtain ⟨g,hg⟩ := hc J (P.subgroupOf J) (Q.subgroupOf J) h.triple c.actor hfull
  let c' := relabel c g
  change ((P.subgroupOf J).map c'.actor = c'.actor.range ⊓ lambda ∧
      (Q.subgroupOf J).map c'.actor = c'.actor.range ⊓ theta) ∨
    ((P.subgroupOf J).map c'.actor = c'.actor.range ⊓ theta ∧
      (Q.subgroupOf J).map c'.actor = c'.actor.range ⊓ lambda) at hg
  have hfull' : alternatingGroup (Fin 7) ≤ c'.actor.range := by
    rw [←c'.component_image]
    exact map_le_range _ _
  have hn : P ≤ normalizer (V : Set G) := h.first_le_M.trans_eq h.normalizer_eq
  obtain ⟨R,hRP,hR,hm⟩ := h.seed
  have htrans : TransitivePlane ((P.subgroupOf J).map c'.actor) (planeImage c' V) :=
    ⟨planeImage_invariant c' P V hn,
      planeImage_transitive c' P V R (hRP.trans h.first_le) hRP (hRP.trans hn)
        hVW h.plane_card hR hm⟩
  obtain ⟨z,hz,hne,hmem,hQz,hMcz⟩ := point_coordinates c' h hVW
  have hcard := (planeImage_card c' V hVW).trans h.plane_card
  rcases hg with ⟨hP,hQ⟩ | ⟨hP,hQ⟩
  · rw [hP] at htrans
    rw [hQ] at hQz
    obtain ⟨hp,hpoint⟩ := hr.lambda_plane c'.actor.range (planeImage c' V)
      (c'.moduleEquiv z).toAdd hfull' hcard htrans hmem hne
      ((inf_le_inf_right theta inf_le_left).trans hQz)
    refine ⟨c',?_,?_,hQ,?_⟩
    · intro w
      rw [←hp]
      exact (mem_planeImage c' V w).symm
    · rw [h.normalizer_eq]
      exact normalizer_image_of_plane c' hVW hp hr
    · rwa [hpoint] at hMcz
  · rw [hP] at htrans
    rw [hQ] at hQz
    have hpoint := hr.theta_point c'.actor.range (planeImage c' V)
      (c'.moduleEquiv z).toAdd hfull' hcard htrans hmem hne (inf_le_left.trans hQz)
    rw [hpoint] at hQz
    exact (reversed_orientation_impossible c'.actor.range hfull' hQz).elim

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
