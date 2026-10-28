module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.SixInspection.Actor
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Automorphisms
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.ActionTransport

/-!
# The whole symmetric-six action quotient

Choose A₆ coordinates carrying the original V₂ to the marked four-group.
Relative normality in M ∩ I makes S preserve that four-group. Its automorphism
stabilizer lies in the natural S₆, so I = LS acts through this S₆. The action
contains Inn(A₆). It is larger than Inn(A₆), since V₁ centralizes Y₊, acts
nontrivially on L, and C_L(Y₊) = 1. The index-two inclusion A₆ < S₆ therefore
identifies the whole action image.

The conjugation kernel is proved to be exactly C_I(L), giving an actual
isomorphism from I/C_I(L), without any lifting or splitting assumption.
The final A₄ obstruction is not used. The stronger retained plane data makes
an additional parabolic classification unnecessary in this particular branch.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.43,
printed p.1140; the concrete A₆ four-group geometry is developed on pp.567--570.
-/

public section

open Subgroup AlternatingSix AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.FourNormalizers
open AlternatingSix.OuterInvolutionExtension
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.SixInspection
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

private def action (e : L ≃* A6) : I →* AutA6 :=
  (normalizerAction e).comp (inclusion c.normalizes)

private theorem action_on_component (e : L ≃* A6) (l : L) :
    action c e ⟨l, c.component_le l.property⟩ = MulAut.conj (e l) :=
  normalizerAction_on_inner e l

private theorem action_ker (e : L ≃* A6) : (action c e).ker = c.toComponentAction.kernel := by
  ext x
  change MulAut.congr e (L.normalizerMonoidHom ⟨x, c.normalizes x.property⟩) = 1 ↔ _
  rw [← (MulAut.congr e).map_one, (MulAut.congr e).injective.eq_iff]
  change (⟨x, c.normalizes x.property⟩ : normalizer (L : Set G)) ∈
    L.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

include c in
private theorem exists_standard_coordinates (e : L ≃* A6) :
    ∃ f : L ≃* A6, (V₂.subgroupOf L).map f.toMonoidHom = standardFour := by
  let K := V₂.subgroupOf L
  let eK : K ≃* V₂ := subgroupOfEquivOfLe (plane_le_component c)
  let eF := eK.symm.trans (e.subgroupMap K)
  let : IsKleinFour (K.map e.toMonoidHom) :=
    ⟨(Nat.card_congr eF.toEquiv).symm.trans (plane_isKleinFour c).card_four,
      (Monoid.exponent_eq_of_mulEquiv eF.symm).trans (plane_isKleinFour c).exponent_two⟩
  obtain ⟨α, hα⟩ := exists_map_standardFour (K.map e.toMonoidHom)
  refine ⟨e.trans α.symm, ?_⟩
  change K.map (α.symm.toMonoidHom.comp e.toMonoidHom) = standardFour
  rw [← map_map, ← hα, map_map]
  simp

private theorem action_preserves_plane (e : L ≃* A6) (s : S) :
    ((V₂.subgroupOf L).map e.toMonoidHom).map
      (action c e ⟨s, (sylow_le_local c s.property).2⟩).toMonoidHom =
        (V₂.subgroupOf L).map e.toMonoidHom := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨L.normalizerMonoidHom
      ⟨s, c.normalizes (sylow_le_local c s.property).2⟩ v, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp
        (c.plane_two_normalized (sylow_le_local c s.property)) v).mp hv
    · change e _ = e (L.normalizerMonoidHom _ (e.symm (e v)))
      simp only [e.symm_apply_apply]
      rfl
  · exact (Nat.card_congr ((action c e _).subgroupMap
      ((V₂.subgroupOf L).map e.toMonoidHom)).toEquiv).le

private theorem inner_le_action_range (e : L ≃* A6) : ShadowLocal.inner ≤ (action c e).range := by
  rintro _ ⟨a, rfl⟩
  refine ⟨⟨e.symm a, c.component_le (e.symm a).property⟩, ?_⟩
  rw [action_on_component, e.apply_symm_apply]

private theorem action_range_le_natural (e : L ≃* A6)
    (he : (V₂.subgroupOf L).map e.toMonoidHom = standardFour) :
    (action c e).range ≤ natural := by
  have hL : L ≤ ((natural.comap (normalizerAction e)).map
      (normalizer (L : Set G)).subtype) := by
    intro l hl
    refine ⟨⟨l, L.le_normalizer hl⟩, ?_, rfl⟩
    change normalizerAction e ⟨l, L.le_normalizer hl⟩ ∈ natural
    rw [normalizerAction_on_inner e ⟨l, hl⟩]
    exact inner_le_natural ⟨_, rfl⟩
  have hS : S ≤ ((natural.comap (normalizerAction e)).map
      (normalizer (L : Set G)).subtype) := by
    intro s hs
    refine ⟨⟨s, c.normalizes (sylow_le_local c hs).2⟩, ?_, rfl⟩
    apply standard_stabilizer_le_natural
    have h := action_preserves_plane c e ⟨s, hs⟩
    rwa [he] at h
  have hI := sup_le hL hS
  rw [← c.generated] at hI
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hI x.property
  have hyx : y = ⟨x, c.normalizes x.property⟩ := Subtype.ext hxy
  change normalizerAction e y ∈ natural at hy
  change normalizerAction e ⟨x, c.normalizes x.property⟩ ∈ natural
  exact hyx ▸ hy

private theorem natural_eq_of_inner_lt {H : Subgroup AutA6}
    (hi : ShadowLocal.inner ≤ H) (hn : H ≤ natural)
    (hne : ¬ H ≤ ShadowLocal.inner) : H = natural := by
  have hidx : ShadowLocal.inner.relIndex natural = 2 := by
    have h := relIndex_mul_index inner_le_natural
    rw [inner_index, GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at h
    omega
  have hdiv := relIndex_dvd_of_le_left natural hi
  rw [hidx] at hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
  · exact le_antisymm hn (relIndex_eq_one.mp h)
  · have hh := relIndex_mul_relIndex ShadowLocal.inner H natural hi hn
    rw [hidx, h] at hh
    have he : ShadowLocal.inner.relIndex H = 1 := by omega
    exact (hne (relIndex_eq_one.mp he)).elim

private theorem action_range_not_le_inner (e : L ≃* A6)
    (hc : L ⊓ centralizer (Yplus : Set G) = ⊥) :
    ¬ (action c e).range ≤ ShadowLocal.inner := by
  intro hinner
  apply c.plane_one_acts
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  have hvI : v ∈ I := (sylow_le_local c (c.plane_one_le hv)).2
  obtain ⟨a, ha⟩ := hinner (show action c e ⟨v, hvI⟩ ∈ (action c e).range from ⟨_, rfl⟩)
  let l := e.symm a
  have hact : L.normalizerMonoidHom ⟨v, c.normalizes hvI⟩ = MulAut.conj l := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact ha.symm
  have hvY : v ∈ centralizer (Yplus : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp c.plane_one_centralizes hv
  have hlY : (l : G) ∈ centralizer (Yplus : Set G) := by
    intro y hy
    have heq := congrArg (fun f : MulAut L =>
      (f ⟨y, c.y_le_component hy⟩ : G)) hact
    change v * y * v⁻¹ = (l : G) * y * (l : G)⁻¹ at heq
    rw [← hvY y hy, mul_inv_cancel_right] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq.symm).symm
  have hl1 : l = 1 := Subtype.ext (hc.le ⟨l.property, hlY⟩)
  have ha1 : a = 1 := by
    have h := congrArg e hl1
    simpa only [l, e.apply_symm_apply, map_one] using h
  have hvker : (⟨v, hvI⟩ : I) ∈ (action c e).ker := by
    change action c e ⟨v, hvI⟩ = 1
    rw [← ha, ha1, map_one]
  rw [action_ker] at hvker
  exact hvker

private theorem quotient_symmetric_six_of_actor_centralizer
    (e : L ≃* A6) (hc : L ⊓ centralizer (Yplus : Set G) = ⊥) :
    Nonempty (c.toComponentAction.Quotient ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨f, hf⟩ := exists_standard_coordinates c e
  have hr := natural_eq_of_inner_lt (inner_le_action_range c f)
    (action_range_le_natural c f hf) (action_range_not_le_inner c f hc)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (action_ker c f).symm).trans
    (QuotientGroup.quotientKerEquivRange (action c f))).trans
    ((MulEquiv.subgroupCongr hr).trans
      GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms.symm)⟩

/-- The entire action quotient is S₆. The component plane and the nontrivial
centralizing action already suffice; no parabolic classification is assumed. -/
theorem quotient_symmetric_six [Finite G]
    (h6 : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    Nonempty (c.toComponentAction.Quotient ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨e⟩ := h6
  exact quotient_symmetric_six_of_actor_centralizer c e (actor_centralizer c e)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.SixInspection
