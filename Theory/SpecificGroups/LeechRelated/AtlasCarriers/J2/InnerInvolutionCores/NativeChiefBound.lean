module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalModule
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
public import Theory.Representation.BinaryPermutation.GroupIrreducible
public import Theory.GroupTheory.NoncentralChiefRefinement.OneNoncentralLayer
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Native J₂ fixed-residual chief bounds

The central representative's centralizer is perfect. Its marked involution
is central, and its radical modulo that involution is a chief section:
normal intermediate subgroups map to invariant subgroups of the binary
five-letter augmentation module under the literal five-block action.
The terminal A₅ quotient has no binary chief factors, leaving at most one
noncentral binary chief factor in any complete series.

The other representative has centralizer E₄ × A₅. Its projection to A₅
restricts to a central surjection on the two-residual, so the count is zero.
The native involution-fusion theorem and actual fixed-subgroup equivalences
then cover every inner involutory automorphism, without a Sylow-fixation
hypothesis or a covering-group restriction assumption.

Source: GLS3, Table 5.3g, classes 2A and 2B. This is the intrinsic J₂ input
used by Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088.
All ATLAS identities are supplied by the imported, kernel-checked native
carrier modules; their original attribution and license remain there.
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.NativeChiefBound
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic
open RadicalModule QuotientActions

private theorem perfect_residual_eq_top {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : pResidual 2 H = ⊤ := by
  apply (pResidual_eq_top_iff 2 H).mpr
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

private theorem marked_central : marked ∈ center l₁ := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  change x.val * z = z * x.val
  exact mem_centralizer_singleton_iff.mp
    (show x.val ∈ centralizer ({z} : Set Carrier) from x.property)

private theorem Z_central : zpowers marked ≤ center l₁ :=
  (zpowers_le).mpr marked_central

private instance Z_normal : (zpowers marked).Normal where
  conj_mem n hn g := by
    have he := mem_center_iff.mp (Z_central hn) g
    simpa only [he, mul_inv_cancel_right] using hn

private def Z : NormalNode l₁ := ⟨zpowers marked, inferInstanceAs (zpowers marked).Normal⟩
private def Q : NormalNode l₁ := ⟨pCore 2 l₁, inferInstanceAs (pCore 2 l₁).Normal⟩

private theorem Z_le_Q : Z ≤ Q := by
  apply zpowers_le.mpr
  obtain ⟨r, hr, he⟩ := CoverSquareOrbit.exists_core_square
  change marked ∈ pCore 2 l₁
  rw [show marked = CoverSquareOrbit.tL from rfl, ← he]
  exact pow_mem hr 2

private theorem Z_chief_Q : Z ⋖ Q := by
  have hne : ¬ Q ≤ Z := by
    intro h
    have hx : enum 1 ∈ b.ker := by
      rw [b_ker]
      exact h (enum 1).property
    have hz := congrArg (fun v : Multiplicative (BinaryPermutation.core (Fin 5)) =>
      v.toAdd.val (1 : Fin 5)) (MonoidHom.mem_ker.mp hx)
    rw [show (b (enum 1)).toAdd = vector 1 from b_enum 1] at hz
    have hn : (vector 1).val (1 : Fin 5) ≠ 0 := by decide +kernel
    exact hn hz
  refine ⟨lt_of_le_not_ge Z_le_Q hne, ?_⟩
  intro N hZN hNQ
  let E := (N.val.subgroupOf (pCore 2 l₁)).map b
  have hE : ∀ g : alternatingGroup (Fin 5), ∀ v ∈ E,
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) g.val v.toAdd) ∈ E := by
    intro g v hv
    obtain ⟨k, rfl⟩ := innerAction_surjective g
    obtain ⟨x, hx, rfl⟩ := hv
    have hb : Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) (innerAction k).val (b x).toAdd) =
        b (MulAut.conjNormal k x) := by
      exact congrArg Multiplicative.ofAdd (b_equivariant k x).symm
    rw [hb]
    apply mem_map_of_mem
    exact N.property.conj_mem x.val hx k
  rcases BinaryPermutation.fiveCore_invariant_subgroup E hE with hz | ht
  · apply hZN.ne
    apply Subtype.ext
    apply le_antisymm (show Z.val ≤ N.val from hZN.le)
    intro x hx
    have hxQ : x ∈ pCore 2 l₁ := hNQ.le hx
    have hb : b ⟨x, hxQ⟩ ∈ E := mem_map_of_mem b hx
    rw [hz] at hb
    have hk : (⟨x, hxQ⟩ : pCore 2 l₁) ∈ b.ker := hb
    rw [b_ker] at hk
    exact hk
  · have hk : b.ker ≤ N.val.subgroupOf (pCore 2 l₁) := by
      rw [b_ker]
      exact comap_mono hZN.le
    have ht' : N.val.subgroupOf (pCore 2 l₁) = ⊤ := by
      have hc := congrArg (Subgroup.comap b) ht
      rw [comap_map_eq, sup_eq_left.mpr hk, comap_top] at hc
      exact hc
    exact hNQ.ne (Subtype.ext (le_antisymm hNQ.le (subgroupOf_eq_top.mp ht')))

private theorem a5_no_two : HasNoTwoChiefFactors (alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  apply noTwoChiefFactors_of_simple
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  exact (by norm_num : ¬ 3 ∣ 2) ((Nat.prime_three.dvd_of_dvd_pow hd))

/-- The central representative has at most one noncentral binary chief factor. -/
theorem central_count (s : ChiefSeries l₁) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  apply s.noncentralTwoCount_le_one_of_central_chief Z Q ?_ Z_chief_Q ?_ h0 h1
  · rw [isCentral_iff_commutator_le, commutator_le]
    intro x _ y hy
    exact (commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (Z_central hy) x))
  · obtain ⟨e⟩ := l₁_quotient
    exact a5_no_two.of_equiv e

/-- The central representative is perfect, so its two-residual is the whole centralizer. -/
theorem central_residual_count (s : ChiefSeries (pResidual 2 l₁))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  let := CoverSquareOrbit.l₁_isPerfect
  let e : pResidual 2 l₁ ≃* l₁ :=
    (MulEquiv.subgroupCongr perfect_residual_eq_top).trans topEquiv
  obtain ⟨ht0, ht1⟩ := s.mapActor_complete e h0 h1
  simpa only [ChiefSeries.mapActor_noncentralTwoCount] using central_count (s.mapActor e) ht0 ht1

/-- The other native centralizer has a central projection to A₅, including on
its two-residual; it therefore has no noncentral binary chief factor. -/
theorem noncentral_residual_count
    (s : ChiefSeries (pResidual 2
      (centralizer ({GeneratorPair.a} : Set Carrier))))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount = 0 := by
  let C := centralizer ({GeneratorPair.a} : Set Carrier)
  let e := InnerInvolutionCores.a_centralizer_equiv
  let f : C →* alternatingGroup (Fin 5) := (MonoidHom.snd _ _).comp e.toMonoidHom
  have hf : Function.Surjective f := fun x => ⟨e.symm (1, x), by simp [f]⟩
  have hk : f.ker ≤ center C := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    apply Prod.ext
    · exact mul_comm _ _
    · have hx' : (e x).2 = 1 := hx
      change (e y).2 * (e x).2 = (e x).2 * (e y).2
      rw [hx', mul_one, one_mul]
  let := CoverSquareOrbit.l₁_isPerfect
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.IsPerfect.ofSurjective innerAction_surjective
  let fR : pResidual 2 C →* alternatingGroup (Fin 5) := f.comp (pResidual 2 C).subtype
  have hfR : Function.Surjective fR := by
    have hm := map_pResidual_of_surjective 2 f hf
    rw [perfect_residual_eq_top (H := alternatingGroup (Fin 5))] at hm
    intro y
    obtain ⟨x, hx, he⟩ := hm.ge (mem_top y)
    exact ⟨⟨x, hx⟩, he⟩
  have hkR : fR.ker ≤ center (pResidual 2 C) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hx) y.val)
  obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries
    (⊥ : NormalNode (alternatingGroup (Fin 5))) ⊤ bot_le
  rw [ChiefSeries.noncentralTwoCount_eq_of_central_surjective fR hfR hkR s t h0 h1 ht0 ht1]
  exact t.noncentralTwoCount_eq_zero_of_noTwo a5_no_two

/-- Both native involution classes satisfy the bound on their actual fixed residual. -/
theorem inner_fixed_residual_count (β : MulAut Carrier) (hβ : orderOf β = 2)
    (hi : ∃ x : Carrier, β = MulAut.conj x)
    (s : ChiefSeries (pResidual 2 β.fixedSubgroup))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  rcases InnerInvolutionCores.inner_fixed_representatives β hβ hi with ha | ht
  · obtain ⟨e⟩ := ha
    let eR := (e.subgroupMap (pResidual 2 β.fixedSubgroup)).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e))
    obtain ⟨ht0, ht1⟩ := s.mapActor_complete eR h0 h1
    have h := noncentral_residual_count (s.mapActor eR) ht0 ht1
    rw [ChiefSeries.mapActor_noncentralTwoCount] at h
    omega
  · obtain ⟨e⟩ := ht
    let eR := (e.subgroupMap (pResidual 2 β.fixedSubgroup)).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e))
    obtain ⟨ht0, ht1⟩ := s.mapActor_complete eR h0 h1
    rw [← s.mapActor_noncentralTwoCount eR]
    exact central_residual_count (s.mapActor eR) ht0 ht1

end Sporadic.LeechRelated.J2.NativeChiefBound
