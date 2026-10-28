module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.MixedAlignment
public import Theory.GroupTheory.PPerfectHom

/-!
# Excluding outer/outer and outer/trivial actions in the crossing pair

The outer fixed subgroup on the first factor is nonabelian odd dihedral.
It acts faithfully on Kᵍ through a two-group kernel. The second fixed
factor commutes with its image, hence has image of exponent at most two
by the full prime-field automorphism centralizer calculation.

If the second action is outer, its own odd-dihedral fixed subgroup also
acts faithfully, contradicting this exponent bound. If the action is
trivial, the perfect second factor has a two-group image, so that image
vanishes; the two-group action kernel then makes the factor trivial.
Together with the mixed case, this excludes every outer first-factor
action. This strengthens the rank argument in the source using the same
actual action and the already established full automorphism bound.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

private theorem conjugate_mark_square (d : Incoming κ G p) (g : G) :
    (g⁻¹ * d.t * g) ^ 2 = 1 := by
  have ht : d.t ^ 2 = 1 := by rw [← d.t_order]; exact pow_orderOf_eq_one d.t
  simpa only [map_pow, MulAut.conj_apply, inv_inv, map_one] using congrArg (MulAut.conj g⁻¹) ht

/-- An outer action on K forces the commuting action of its other fixed
factor on Kᵍ to have exponent at most two. -/
theorem outer_left_right_fixed_action_square (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hout : d.K.normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiK⟩ ∉
      (MulAut.conj : d.K →* MulAut d.K).range)
    (b : (conjugate d.K d.x ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G)) :
    ((conjugate d.K g).normalizerMonoidHom
      ⟨b, d.conjugate_normalized g b.property.2⟩) ^ 2 = 1 := by
  obtain ⟨n, hn, hlarge, ⟨e⟩⟩ := Theory.PSL2.prime_outer_relative_centralizer_dihedral
    (by have := d.prime_ge; omega) d.K d.model _ hiK (conjugate_mark_square d g) hout
  apply d.mixed_action_centralizer_square g hn (by omega) e
  rintro _ ⟨c, rfl⟩
  let N := normalizer (conjugate d.K g : Set G)
  have hcomm : Commute (⟨c, d.conjugate_normalized g c.property.2⟩ : N)
      ⟨b, d.conjugate_normalized g b.property.2⟩ := by
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp d.commuting
      c.property.1 b.val b.property.1).symm
  exact (hcomm.map (conjugate d.K g).normalizerMonoidHom).eq

/-- Both outer fixed subgroups would act faithfully and commute in
Aut(Kᵍ). The full PGL₂ centralizer bound makes the second image abelian,
contradicting its nonabelian odd-dihedral model. -/
theorem false_of_outer_outer_actions (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hiL : g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G))
    (houtK : d.K.normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiK⟩ ∉
      (MulAut.conj : d.K →* MulAut d.K).range)
    (houtL : (conjugate d.K d.x).normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiL⟩ ∉
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range) : False := by
  let L := conjugate d.K d.x
  let B := L ⊓ centralizer ({g⁻¹ * d.t * g} : Set G)
  let eL : L ≃* PSL(2, ZMod p) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
  obtain ⟨n, hn, hlarge, ⟨e⟩⟩ := Theory.PSL2.prime_outer_relative_centralizer_dihedral
    (by have := d.prime_ge; omega) L eL _ hiL (conjugate_mark_square d g) houtL
  let f : B →* MulAut (conjugate d.K g) :=
    (conjugate d.K g).normalizerMonoidHom.comp
      (inclusion (inf_le_right.trans (d.conjugate_normalized g)))
  have hinj := d.odd_dihedral_action_injective g B inf_le_right hn (by omega) e
  have hnot := odd_dihedral_range_not_commutative hn (by omega) e f hinj
  have hs (b : f.range) : b ^ 2 = 1 := by
    obtain ⟨b', hb'⟩ := b.property
    apply Subtype.ext
    change (b : MulAut (conjugate d.K g)) ^ 2 = 1
    rw [← hb']
    exact d.outer_left_right_fixed_action_square g hiK houtK b'
  have hi (b : f.range) : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs b)
  apply hnot
  exact IsMulCommutative.of_comm (fun a b => by
    calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b * a := by rw [_root_.mul_inv_rev, hi, hi])

/-- If the outer involution centralizes the other factor, that perfect factor
has a two-group image and then lies in the two-group action kernel. This
would make the factor trivial, contradicting its marked involution. -/
theorem false_of_outer_trivial_actions (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hout : d.K.normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiK⟩ ∉
      (MulAut.conj : d.K →* MulAut d.K).range)
    (htriv : g⁻¹ * d.t * g ∈ centralizer (conjugate d.K d.x : Set G)) : False := by
  let L := conjugate d.K d.x
  let I := centralizer ({g⁻¹ * d.t * g} : Set G)
  have hLI : L ≤ I := fun b hb => mem_centralizer_singleton_iff.mpr (htriv b hb)
  let f : L →* MulAut (conjugate d.K g) :=
    (conjugate d.K g).normalizerMonoidHom.comp (inclusion (hLI.trans (d.conjugate_normalized g)))
  have hs (b : L) : f b ^ 2 = 1 :=
    d.outer_left_right_fixed_action_square g hiK hout ⟨b, b.property, hLI b.property⟩
  have hp : IsPGroup 2 f.range := by
    intro b
    obtain ⟨b', hb'⟩ := b.property
    refine ⟨1, Subtype.ext ?_⟩
    change (b : MulAut (conjugate d.K g)) ^ (2 ^ 1) = 1
    rw [pow_one, ← hb']
    exact hs b'
  have hKp := isPPerfect_embedded_pResidual 2 (centralizer ({d.t} : Set G))
  rw [d.twoResidual_eq] at hKp
  let eL : d.K ≃* L := (MulAut.conj d.x⁻¹).subgroupMap d.K
  have hLp : IsPPerfect 2 L := hKp.of_surjective eL.toMonoidHom eL.surjective
  have hf : f.rangeRestrict = 1 := hLp.hom_eq_one_of_isPGroup hp f.rangeRestrict
  let C := I ⊓ centralizer (conjugate d.K g : Set G)
  have hLC : L ≤ C := by
    intro b hb
    refine ⟨hLI hb, ?_⟩
    have hf1 : f ⟨b, hb⟩ = 1 := by
      have hh := congrArg (fun y : f.range => (y : MulAut (conjugate d.K g)))
        (DFunLike.congr_fun hf (⟨b, hb⟩ : L))
      exact hh
    have hk : inclusion (hLI.trans (d.conjugate_normalized g)) ⟨b, hb⟩ ∈
        (conjugate d.K g).normalizerMonoidHom.ker := hf1
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  have hL2 : IsPGroup 2 L := (d.conjugate_relative_centralizer_isTwoGroup g).of_injective
    (inclusion hLC) (inclusion_injective _)
  have hid := hLp.hom_eq_one_of_isPGroup hL2 (MonoidHom.id L)
  have ht1 : d.t = 1 := congrArg Subtype.val (DFunLike.congr_fun hid ⟨d.t, d.mark_mem⟩)
  have := d.t_order
  simp [ht1] at this

/-- All action cases with an outer first-factor action are impossible. -/
theorem inner_left_of_normalizing_factors (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hiL : g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G)) :
    d.K.normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiK⟩ ∈
      (MulAut.conj : d.K →* MulAut d.K).range := by
  by_contra hout
  by_cases htriv : g⁻¹ * d.t * g ∈ centralizer (conjugate d.K d.x : Set G)
  · exact d.false_of_outer_trivial_actions g hiK hout htriv
  by_cases hin : (conjugate d.K d.x).normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiL⟩ ∈
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range
  · exact d.false_of_mixed_actions g hiK hiL hout hin htriv
  · exact d.false_of_outer_outer_actions g hiK hiL hout hin

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
