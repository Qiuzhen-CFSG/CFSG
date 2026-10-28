module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.ThompsonCoordinates
public import Theory.Representation.BinaryFourPlus.Thompson
/-!
# The Thompson rigidity step in the S₆ extension branch

The actual plus-four action of H on Q_H/Z(Q_H) has no nontrivial
elementary offender: an actor subgroup times its fixed space has order
at most eight. If K ≤ H has squares and commutators in Z(Q_H), its action
image is elementary and its kernel modulo Z(Q_H) embeds in that fixed
space. A nontrivial image therefore forces |K| < 64. Since |Q_H| = 64,
every such K of order at least 64 equals Q_H.

This is the precise consequence of Q_H/Z(Q_H) = J(T/Z(Q_H)) used by the
source to compare two mutually normalizing conjugates with the same
center. The proof retains the original quaternion quotient coordinates
and the original faithful starred action; no abstract Ω₄⁺(2) recognition
is substituted for its natural module.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921, the
weak-closure paragraph following the Ω₄⁺(2) action.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

private theorem card_eq_range_mul_ker {R S : Type*} [Group R] [Group S]
    [Finite R] (f : R →* S) : Nat.card R = Nat.card f.range * Nat.card f.ker := by
  have hh := f.ker.card_mul_index
  rw [index_ker] at hh
  simpa only [Nat.mul_comm] using hh.symm

private theorem order_bound {R : Type*} [Group R] [Finite R]
    (f : R →* BinaryFourPlus.Wreath)
    (c : f.ker →* Multiplicative BinaryFourPlus.V)
    (hker : Nat.card c.ker ≤ 4)
    (hfixed : ∀ v : c.range, ∀ a : f.range,
      (BinaryFourPlus.wreathToIsometry a.val).val v.val.toAdd = v.val.toAdd)
    (hbound : Nat.card f.range * Nat.card {v : BinaryFourPlus.V //
      ∀ a : f.range, (BinaryFourPlus.wreathToIsometry a.val).val v = v} < 16) :
    Nat.card R < 64 := by
  let j : c.range → {v : BinaryFourPlus.V //
      ∀ a : f.range, (BinaryFourPlus.wreathToIsometry a.val).val v = v} :=
    fun v => ⟨v.val.toAdd, hfixed v⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Multiplicative.ofAdd (congrArg
      (fun z : {v : BinaryFourPlus.V // ∀ a : f.range,
        (BinaryFourPlus.wreathToIsometry a.val).val v = v} => z.val) hxy)
  have hc := Nat.card_le_card_of_injective j hj
  rw [card_eq_range_mul_ker f, card_eq_range_mul_ker c]
  calc
    _ ≤ Nat.card f.range * (Nat.card c.range * 4) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hker)
    _ ≤ Nat.card f.range * (Nat.card {v : BinaryFourPlus.V //
      ∀ a : f.range, (BinaryFourPlus.wreathToIsometry a.val).val v = v} * 4) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
    _ < 64 := by
      simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hbound (by decide : 0 < 4)

private theorem range_elementary (K : Subgroup G) (hKH : K ≤ D.H)
    (hsq : ∀ x ∈ K, x ^ 2 ∈ (center D.QH).map D.QH.subtype) :
    IsElementaryAbelian 2
      (closureOrthogonalAction K hKH (SourceOrthogonal.quaternion d h e hseed hn hU)).range := by
  let α := closureOrthogonalAction K hKH (SourceOrthogonal.quaternion d h e hseed hn hU)
  have hk : α.ker = D.QH.subgroupOf K :=
    h.closureOrthogonalAction_ker K hKH _ (SourceOrthogonal.center_map d h e hseed hn hU)
  have hs (x : α.range) : x ^ 2 = 1 := by
    obtain ⟨k,hk'⟩ := x.property
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [←hk', ←map_pow]
    apply α.mem_ker.mp
    rw [hk]
    exact (map_subtype_le (center D.QH)) (hsq k k.property)
  have hi (x : α.range) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc
        x*y = (x*y)⁻¹ := (hi _).symm
        _ = y*x := by rw [mul_inv_rev,hi,hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

private theorem range_le_original_normalizer (K : Subgroup G) (hKH : K ≤ D.H) :
    (closureOrthogonalAction K hKH (SourceOrthogonal.quaternion d h e hseed hn hU)).range ≤
      normalizer (SourceOrthogonalWitness.localCubic d h e hseed hn hU : Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨k,rfl⟩
  apply SourceOrthogonalWitness.range_normalizes_local d h e hseed hn hU
  refine ⟨QuotientGroup.mk' (pCore 2 D.H) (inclusion hKH k), ?_⟩
  rw [SourceOrthogonal.starEmbedding_mk]
  rfl

include d h e hseed hn hU in
theorem core_card (b : Conclusions D M 6 g)
    (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6))) :
    Nat.card D.QH = 64 := by
  have hQ : D.LT.pCoreIn 2 = D.V := by
    rw [← b.seven.1]
    exact b.seven.2.symm
  have hc := SourcePointCoreGeometry.point_core_central_quotient_card d h e hseed hn hU hQ
  rw [← b.six.1] at hc
  change Nat.card (D.QH ⧸ center D.QH) = 16 at hc
  have hh := (center D.QH).card_mul_index
  rw [index_eq_card, hc, extension_center_card d h e hseed hn hU b hS] at hh
  omega

private theorem unique_large_of_coordinates
    (b : Conclusions D M 6 g)
    (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))
    (c : D.QH →* Multiplicative BinaryFourPlus.V)
    (hc : c.ker = center D.QH)
    (hconj : ∀ (x : D.H) (u : D.QH),
      (c (seedConjugation D.H D.QH (H_normalizes_QH (D := D)) x u)).toAdd =
        (BinaryFourPlus.wreathToIsometry
          (SourceOrthogonal.starEmbedding d h e hseed hn hU
            (QuotientGroup.mk' (pCore 2 D.H) x))).val (c u).toAdd)
    (K : Subgroup G) (hKH : K ≤ D.H)
    (hsq : ∀ x ∈ K, x ^ 2 ∈ (center D.QH).map D.QH.subtype)
    (hcomm : ⁅K,K⁆ ≤ (center D.QH).map D.QH.subtype)
    (hcard : 64 ≤ Nat.card K) : K = D.QH := by
  let α := closureOrthogonalAction K hKH (SourceOrthogonal.quaternion d h e hseed hn hU)
  have hk : α.ker = D.QH.subgroupOf K :=
    h.closureOrthogonalAction_ker K hKH _ (SourceOrthogonal.center_map d h e hseed hn hU)
  have hKQ : K ≤ D.QH := by
    by_contra hnot
    have hne : α.range ≠ ⊥ := by
      intro hz
      have hα : α.ker = ⊤ := by
        apply top_unique
        intro k _
        exact α.mem_ker.mpr ((show α k ∈ (⊥ : Subgroup BinaryFourPlus.Wreath) from
          hz ▸ (show α k ∈ α.range from ⟨k,rfl⟩)))
      apply hnot
      intro k hkK
      have hh : (⟨k,hkK⟩ : K) ∈ α.ker := hα ▸ mem_top _
      have hh' := hk ▸ hh
      exact hh'
    let : IsElementaryAbelian 2 α.range := range_elementary d h e hseed hn hU K hKH hsq
    obtain ⟨_,hA,_,s,_,hs,_,hss,hsc⟩ :=
      SourceOrthogonalWitness.exists_original_cubic_normalizer_witness d h e hseed hn hU
    have hbound := BinaryFourPlus.CubicNormalizer.elementary_fixed_card_lt
      (SourceOrthogonalWitness.localCubic d h e hseed hn hU) hA s hs hss hsc
      α.range (range_le_original_normalizer d h e hseed hn hU K hKH) hne
    let ι : α.ker →* D.QH := {
      toFun x := ⟨x.val.val, show x.val ∈ D.QH.subgroupOf K from hk ▸ x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hι : Function.Injective ι := by
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : D.QH => z.val) hh
    let β := c.comp ι
    have hβker : Nat.card β.ker ≤ 4 := by
      let j : β.ker → center D.QH := fun x => ⟨ι x.val, by
        rw [←hc]
        exact x.property⟩
      have hj : Function.Injective j := by
        intro x y hh
        exact Subtype.ext (hι (congrArg Subtype.val hh))
      have hb := Nat.card_le_card_of_injective j hj
      rwa [extension_center_card d h e hseed hn hU b hS] at hb
    have hfix : ∀ v : β.range, ∀ a : α.range,
        (BinaryFourPlus.wreathToIsometry a.val).val v.val.toAdd = v.val.toAdd := by
      rintro ⟨v,k,rfl⟩ ⟨a,t,rfl⟩
      let x : D.H := inclusion hKH t
      let u := ι k
      let y := seedConjugation D.H D.QH (H_normalizes_QH (D := D)) x u
      have hz : y / u ∈ center D.QH := by
        have hh : ((y/u : D.QH) : G) ∈ (center D.QH).map D.QH.subtype := by
          change (((t : G) * (k.val : G) * (t : G)⁻¹) / (k.val : G)) ∈ _
          simpa only [div_eq_mul_inv, commutatorElement_def] using
            hcomm (commutator_mem_commutator t.property k.val.property)
        obtain ⟨z,hz,hz'⟩ := hh
        have he : z = y/u := Subtype.ext hz'
        exact he ▸ hz
      have he : c y = c u := by
        apply div_eq_one.mp
        rw [←map_div]
        exact c.mem_ker.mp (hc.symm ▸ hz)
      have hh := hconj x u
      rw [he] at hh
      exact hh.symm
    have hsmall := order_bound α β hβker hfix hbound
    omega
  exact eq_of_le_of_card_ge hKQ (by rw [core_card d h e hseed hn hU b hS]; exact hcard)

include d h e hseed hn hU in
/-- The actual core is the unique subgroup of H of order at least 64 whose
squares and commutators lie in Z(Q_H). This is the precise rigidity
needed by the Thompson-subgroup step of 13.5.16. -/
theorem core_unique_large
    (b : Conclusions D M 6 g)
    (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))
    (K : Subgroup G) (hKH : K ≤ D.H)
    (hsq : ∀ x ∈ K, x ^ 2 ∈ (center D.QH).map D.QH.subtype)
    (hcomm : ⁅K,K⁆ ≤ (center D.QH).map D.QH.subtype)
    (hcard : 64 ≤ Nat.card K) : K = D.QH := by
  exact unique_large_of_coordinates d h e hseed hn hU b hS
    (coreCoordinates d h e hseed hn hU b)
    (coreCoordinates_ker d h e hseed hn hU b)
    (coreCoordinates_conj d h e hseed hn hU b) K hKH hsq hcomm hcard

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
