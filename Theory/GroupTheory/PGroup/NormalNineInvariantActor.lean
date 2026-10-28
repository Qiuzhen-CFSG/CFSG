module
public import Theory.GroupAction.InvariantCubicLift
public import Theory.GroupAction.SubgroupConjugation
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two-invariant actors on a normal elementary nine-group

If a normal three-group acts nontrivially on a normal elementary group of
order nine, the action image has order three: it is a nontrivial three-subgroup
of GL₂(3), whose order is 48. Conjugation by a two-group preserves the action
kernel. An invariant lift through this cubic quotient supplies a nontrivial
actor whose cyclic subgroup is normalized by the entire two-group.

The actor is a three-element; its order need not be three. The literal
conjugation kernel is retained throughout.

Source application: the T-invariant enlargement in Aschbacher–Smith,
14.5.20, printed p.1019, refs/quasithin.pdf. The actual local application
is SourceConstruction.LocalReduction.SolvableNineEnlargement.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- A nontrivial three-core actor can be selected with a two-invariant cyclic subgroup. -/
theorem normal_nine_normalized_actor (P N S : Subgroup D)
    [P.Normal] [N.Normal] [IsElementaryAbelian 3 N]
    (hP : IsPGroup 3 P) (hS : IsPGroup 2 S) (h9 : Nat.card N = 9)
    (hmove : ¬ P ≤ centralizer (N : Set D)) :
    ∃ y : D, y ∈ P ∧ y ∉ centralizer (N : Set D) ∧
      S ≤ normalizer (zpowers y : Set D) := by
  classical
  let a := (MulAut.conjNormal : D →* MulAut N).comp P.subtype
  let K := a.ker
  have hK : K = (centralizer (N : Set D)).subgroupOf P := by
    ext p
    change (MulAut.conjNormal (p : D) : MulAut N) = 1 ↔
      (p : D) ∈ centralizer (N : Set D)
    exact SetLike.ext_iff.mp (MulAut.conjNormal_ker_eq_centralizer N) (p : D)
  obtain ⟨c,e,he⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
    (show Nat.card N = 3 ^ 2 by simpa using h9)
  have hAut : Nat.card (MulAut N) = 48 := by
    rw [Nat.card_congr e.toEquiv,Matrix.card_GL_field]
    decide
  have hdiv : Nat.card a.range ∣ 48 := hAut ▸ a.range.card_subgroup_dvd_card
  have hpim := hP.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  obtain ⟨n,hn⟩ := hpim.exists_card_eq
  have hnlt : n < 2 := by
    by_contra! hn2
    have hd : 3 ^ 2 ∣ 48 := (Nat.pow_dvd_pow 3 hn2).trans (hn ▸ hdiv)
    norm_num at hd
  have hn0 : n ≠ 0 := by
    intro hn0
    have hbot : a.range = ⊥ := card_eq_one.mp (by simpa [hn0] using hn)
    apply hmove
    intro p hp
    have hk : (⟨p,hp⟩ : P) ∈ K := by
      change a ⟨p,hp⟩ = 1
      exact mem_bot.mp (hbot ▸ (show a ⟨p,hp⟩ ∈ a.range from ⟨⟨p,hp⟩,rfl⟩))
    exact (show (⟨p,hp⟩ : P) ∈ (centralizer (N : Set D)).subgroupOf P from hK ▸ hk)
  have hc : Nat.card (P ⧸ K) = 3 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv,hn,
      show n = 1 by omega,pow_one]
  let : MulDistribMulAction S P := conjMulDistribMulActionOfLeNormalizer S P le_normalizer_of_normal
  have hi : IsInvariant S P K := by
    rw [hK]
    constructor
    intro s p
    change (p : D) ∈ centralizer (N : Set D) ↔
      (s : D) * (p : D) * (s : D)⁻¹ ∈ centralizer (N : Set D)
    exact mem_normalizer_iff.mp (le_normalizer_of_normal (H := centralizer (N : Set D)) s.property) _
  let : MulDistribMulAction S (P ⧸ K) := quotientMulDistribMulAction K hi
  obtain ⟨y,hy,hs⟩ := Theory.GroupAction.invariant_cubic_lift hS hP hc
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) (fun _ _ => rfl)
  have hnot : (y : D) ∉ centralizer (N : Set D) := by
    intro hmem
    exact hy ((QuotientGroup.eq_one_iff y).mpr (hK ▸ hmem))
  refine ⟨y,y.property,hnot,?_⟩
  intro s hsm
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  change zpowers (s * (y : D) * s⁻¹) = zpowers (y : D)
  rcases hs ⟨s,hsm⟩ with hh | hh
  · have hh' := congrArg P.subtype hh
    change s * (y : D) * s⁻¹ = (y : D) at hh'
    rw [hh']
  · have hh' := congrArg P.subtype hh
    change s * (y : D) * s⁻¹ = (y : D)⁻¹ at hh'
    rw [hh',zpowers_inv]

end Subgroup
