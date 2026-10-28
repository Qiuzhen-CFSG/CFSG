module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Representation.SL2SevenCentralProductOffenders
public import Theory.Representation.BinaryPrimeDegree

/-!
# The faithful M11 exclusion in B.1.13

An FF offender in the full linear normalizer supplies an involution of fixed
codimension at most two. Faithful central-quotient descent and Out(M11) = 1
make its action on the image inner. The binary Schur argument then puts the
involution in that image. Three conjugates generate the perfect central cover,
so their displacement spaces span the irreducible module and its dimension
is at most six. But eleven divides the order of the cover, forcing binary
dimension at least ten.

This proves the exclusion for every finite quasisimple cover and every
faithful irreducible binary representation. No multiplier classification,
small-module recognition, or restriction to inner normalizers is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
printed pp.73–74 / PDF pp.84–85, combined 1 March 2004 manuscript. The
argument here proves this Mathieu branch directly, rather than assuming the
Guralnick–Malle classification cited there.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open _root_.Sporadic.Mathieu
universe u v

private theorem commutator_full {A W : Type*} [Group A] [Nontrivial A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let U := subspaceCommutator ρ ⊤ ⊤
  let C : Subrepresentation ρ :=
    { toSubmodule := U
      apply_mem_toSubmodule g := by
        change U ≤ U.comap (ρ g)
        apply Submodule.span_le.mpr
        rintro _ ⟨h, _, v, _, rfl⟩
        have h₁ : ρ (g * h) v - v ∈ U :=
          Submodule.subset_span ⟨g * h, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩
        have h₂ : ρ g v - v ∈ U :=
          Submodule.subset_span ⟨g, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩
        have he : ρ g (ρ h v - v) = (ρ (g * h) v - v) - (ρ g v - v) := by
          rw [map_sub, map_mul, Module.End.mul_apply]
          abel
        change ρ g (ρ h v - v) ∈ U
        rw [he]
        exact U.sub_mem h₁ h₂ }
  rcases eq_bot_or_eq_top C with h | h
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    apply ha
    apply hf
    have hz : subspaceCommutator ρ ⊤ ⊤ = ⊥ :=
      congrArg Subrepresentation.toSubmodule h
    ext v
    simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] using
      ((subspaceCommutator_eq_bot_iff ρ ⊤ ⊤).mp hz)
        Submodule.mem_top ⟨a, Subgroup.mem_top a⟩
  · exact congrArg Subrepresentation.toSubmodule h

/-- No faithful irreducible binary action of a finite quasisimple M11 cover
has an FF full linear normalizer. -/
theorem faithfulExclusion_m11 : FaithfulExclusion.{u,v} .m11 := by
  intro L W _ _ _ _ _ _ σ hf hirr he hff
  obtain ⟨e⟩ := he
  have hk : σ.ker ≤ center L := by
    intro x hx
    have hx' : σ x = σ 1 := (show σ x = 1 from hx).trans σ.map_one.symm
    exact (hf hx') ▸ (center L).one_mem
  let := actionImage_quasisimple_of_central_kernel σ hk
  let := actionImage_nontrivial_of_central_kernel σ hk
  let e' : actionImage σ ⧸ center (actionImage σ) ≃* M11 :=
    (simpleQuotientEquivImage σ hk).symm.trans e
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) W)ˣ W := Units.coeHom _
  let : Representation.IsIrreducible (τ.comp (actionImage σ).subtype) :=
    imageRepresentation_isIrreducible σ hirr
  let : Finite (actionImage σ) :=
    Finite.of_surjective (actionHom σ) σ.asGroupHom.rangeRestrict_surjective
  have hτ : Function.Injective τ := fun _ _ h => Units.ext h
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_displacement_involution σ hirr hff
  have hr := automorphism_primeRank_le_quotient_center (E := actionImage σ) 2
  rw [primeRank_equiv 2 (MulAut.congr e')] at hr
  have hd2 : fixedCodim (normalizerRepresentation σ) (zpowers t) ≤ 2 :=
    hd.trans (hr.trans m11_automorphism_twoRank_le_two)
  have hinner : ∃ a : actionImage σ,
      (actionImage σ).normalizerMonoidHom t = MulAut.conj a := by
    apply (MulAut.centralQuotientAction_inner_iff e' _).mp
    obtain ⟨a, ha⟩ := m11_automorphism_inner
      (MulAut.centralQuotientAction e' ((actionImage σ).normalizerMonoidHom t))
    exact ⟨a, ha.symm⟩
  have htm := involution_mem_of_inner τ (actionImage σ) hτ t
    (congrArg (fun x : linearNormalizer σ => x.val) ht2) hinner
  let t' : actionImage σ := ⟨t, htm⟩
  have ht' : t' ≠ 1 := fun h => ht (Subtype.ext (congrArg (fun x : actionImage σ => x.val) h))
  have ht2' : t' ^ 2 = 1 :=
    Subtype.ext (congrArg (fun x : linearNormalizer σ => x.val) ht2)
  have hZ (z : actionImage σ) (hz : z ∈ center (actionImage σ)) (hz2 : z ^ 2 = 1) :
      z = 1 := by
    apply Subtype.ext
    apply Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      τ (actionImage σ) hτ (congrArg Subtype.val hz2)
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨a, ha⟩)
  obtain ⟨g, h, hgen⟩ := m11_cover_three_involution_conjugates e' hZ t' ht' ht2'
  let : (imageRepresentation σ).IsIrreducible := imageRepresentation_isIrreducible σ hirr
  have hdim := SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    (imageRepresentation σ) ⊤ (commutator_full (imageRepresentation σ)
      (imageRepresentation_injective σ)) t' g h hgen.ge
  have hdisp : fixedCodim (imageRepresentation σ) (zpowers t') =
      fixedCodim (normalizerRepresentation σ) (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [hdisp] at hdim
  have h11 : 11 ∣ Nat.card L := by
    have hq : 11 ∣ Nat.card (L ⧸ center L) := by
      rw [Nat.card_congr e.toEquiv]
      change 11 ∣ Nat.card M11
      rw [m11_order]
      norm_num
    exact hq.trans (center L).card_quotient_dvd_card
  have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) h11
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  omega
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
