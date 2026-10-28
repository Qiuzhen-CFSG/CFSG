module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSOuterClosure
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

/-!
# Symmetric outer involutions move at least six dimensions

For the literal symmetric outer automorphism r, the element r(b)b⁻¹ has
order four, as checked on the 100 letters. Compatible component coordinates
transport it to [t,y] in the original group. Its square is a nonidentity
inner involution, so it moves at least eight dimensions in degree twenty.

For N⁴ = 0, successive image-kernel dimension formulas give
3 rank(N²) ≤ 2 rank(N). Apply this to N = ρ([t,y]) − 1, and use the
commutator bound rank(ρ([t,y]) − 1) ≤ 2 rank(ρ(t) − 1). This proves
rank(ρ(t) − 1) ≥ 6 without a representation comparison or a filtration.

This discharges the involution field of the symmetric outer interface.
The rank-four and rank-five actor bounds are still required separately.
The final application reduces every cubic witness on the original module to
those two symmetric cases. The marked S8 centralizer is also constructed with
the precise action required by the remaining moved-space and homology factors.
Source: GM02 Proposition 5.1, HS paragraph, author-preprint pp.16–17;
Aschbacher–Smith K.4, printed p.457/PDF p.468. The certified word uses the
existing ATLAS HSG1-p100B0 carrier, with its source attribution.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HigmanSims Twenty
open Sporadic.LeechRelated.HS (Carrier)
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
namespace HSOuterCalculations
open Sporadic.LeechRelated.HS.FiveSubgroup
private def symmetricCommutator : Carrier :=
  Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.symmetricNormalizer b * b⁻¹
private theorem symmetricCommutator_four : symmetricCommutator ^ 4 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel
private theorem symmetricCommutator_square_ne : symmetricCommutator ^ 2 ≠ 1 := by
  intro he
  have hh := congrArg (fun x : Carrier => x.val 0) he
  have hn : (symmetricCommutator ^ 2).val 0 ≠ (1 : Carrier).val 0 := by decide +kernel
  exact hn hh

open Module
namespace SymmetricLinear
section
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
private theorem rank_step (N : Module.End F V) (j : ℕ) :
    finrank F (N ^ (j+1)).range + finrank F ((N^j).range ⊓ N.ker : Submodule F V) =
      finrank F (N^j).range := by
  have h := (N.domRestrict (N^j).range).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq (N^j).range, Submodule.map_comap_subtype] at h
  rw [← LinearMap.range_comp] at h
  rw [pow_succ']
  exact h

omit [FiniteDimensional F V] in
private theorem range_pow_antitone (N : Module.End F V) {i j : ℕ} (hij : i ≤ j) :
    (N^j).range ≤ (N^i).range := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  exact LinearMap.range_comp_le_range _ _

private theorem square_rank (N : Module.End F V) (hN : N^4 = 0) :
    3 * finrank F (N^2).range ≤ 2 * finrank F N.range := by
  have h1 := rank_step N 1
  have h2 := rank_step N 2
  have h3 := rank_step N 3
  change finrank F (N^3).range + finrank F ((N^2).range ⊓ N.ker : Submodule F V) =
    finrank F (N^2).range at h2
  have hk2 := Submodule.finrank_mono (inf_le_inf_right N.ker
    (range_pow_antitone N (by decide : 1 ≤ 2)))
  have hk3 := Submodule.finrank_mono (inf_le_inf_right N.ker
    (range_pow_antitone N (by decide : 2 ≤ 3)))
  change finrank F (N^2).range + finrank F (N.range ⊓ N.ker : Submodule F V) =
    finrank F N.range at h1
  change finrank F ((N^2).range ⊓ N.ker : Submodule F V) ≤
    finrank F (N.range ⊓ N.ker : Submodule F V) at hk2
  change finrank F ((N^3).range ⊓ N.ker : Submodule F V) ≤
    finrank F ((N^2).range ⊓ N.ker : Submodule F V) at hk3
  rw [show 3+1=4 by rfl, hN, LinearMap.range_zero, finrank_bot, zero_add] at h3
  omega

end
section
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
private theorem displacement_square (x : Module.End (ZMod 2) V) (h4 : x^4=1) :
    3 * finrank (ZMod 2) (x^2-1).range ≤ 2 * finrank (ZMod 2) (x-1).range := by
  nontriviality V
  let : CharP (Module.End (ZMod 2) V) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  have hN2 : (x-1)^2=x^2-1 := by
    simpa only [one_pow] using sub_pow_char_of_commute 2 (Commute.one_right x)
  have hN4 : (x-1)^4=0 := by
    have hh := sub_pow_char_pow_of_commute 2 2 (Commute.one_right x)
    simpa only [show 2^2=4 by decide,one_pow,h4,sub_self] using hh
  have hb := square_rank (x-1) hN4
  rw [hN2] at hb
  exact hb
end
end SymmetricLinear

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- A symmetric outer action has an inner commutator of order four. -/
theorem symmetric_order_four_commutator (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} (htS : IsSymmetricOuter e t) :
    ∃ y : G, let x := t * y * t⁻¹ * y⁻¹
      x ∈ generalizedFitting G ∧ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  obtain ⟨c, f, _htc, hfact, _hfinner⟩ := normalizedComponent h e htS
  let y := f.symm b
  let x : generalizedFitting G := MulAut.conjNormal t y * y⁻¹
  have hfx : f x = symmetricCommutator := by
    change f (MulAut.conjNormal t y * y⁻¹) = _
    rw [map_mul, hfact, map_inv, f.apply_symm_apply]
    rfl
  have hx4 : x ^ 4 = 1 := by
    apply f.injective
    rw [map_pow, hfx, symmetricCommutator_four, map_one]
  have hx2 : x ^ 2 ≠ 1 := by
    intro he
    apply symmetricCommutator_square_ne
    rw [← hfx, ← map_pow, he, map_one]
  refine ⟨y, x.property, congrArg Subtype.val hx4, ?_⟩
  intro he
  apply hx2
  exact Subtype.ext he
/-- The actual inner centralizer has S8 coordinates with exactly the marking
action required by the symmetric moved-space and homology factors. -/
theorem symmetric_marked_centralizer (h : HigmanSims.SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} (htS : IsSymmetricOuter e t) :
    ∃ (c : MulAut Carrier) (k : Symmetric.innerCentralizer t ≃* Symmetric.Models.S8),
      quotientAction e t = c *
        (show MulAut Carrier from Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
          HSOuter.symmetricNormalizer) * c⁻¹ ∧
      ∀ x : Symmetric.innerCentralizer t, quotientAction e (x : G) =
        MulAut.conj (c (HSOuter.SymmetricCentralizer.embedding (k x)).val) := by
  obtain ⟨c, f, htc, hfact, hfinner⟩ := normalizedComponent h e htS
  let r := Sporadic.LeechRelated.HS.generated.normalizerMonoidHom HSOuter.symmetricNormalizer
  let ec : Symmetric.innerCentralizer t ≃* HSOuter.permutationCentralizer HSOuter.symmetricPermutation :=
    (centralizerEquiv f r hfact).trans
      (MulEquiv.subgroupCongr (HSOuter.fixedSubgroup_eq_permutationCentralizer
        HSOuter.symmetricNormalizer))
  have hsurj : Function.Surjective HSOuter.SymmetricCentralizer.embedding :=
    (HSOuter.SymmetricCentralizer.embedding_injective.bijective_of_nat_card_le
      (Nat.card_congr HSOuter.symmetricCentralizerEquiv.toEquiv).le).2
  let em : Symmetric.Models.S8 ≃* HSOuter.permutationCentralizer HSOuter.symmetricPermutation :=
    MulEquiv.ofBijective HSOuter.SymmetricCentralizer.embedding
      ⟨HSOuter.SymmetricCentralizer.embedding_injective, hsurj⟩
  let k := ec.trans em.symm
  refine ⟨c, k, htc, ?_⟩
  intro x
  have hx : (HSOuter.SymmetricCentralizer.embedding (k x)).val = f ⟨x, x.property.2⟩ := by
    calc
      _ = (ec x).val := congrArg Subtype.val (em.apply_symm_apply (ec x))
      _ = _ := centralizerEquiv_apply f r hfact x
  rw [hx]
  exact hfinner ⟨x, x.property.2⟩

end HSOuterCalculations

open Module
universe u v
/-- The symmetric outer involution moves at least six dimensions, without
identifying the representation or its centralizer constituents. -/
theorem higmanSims_symmetric_outer_involution_bound
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}
    (h : HigmanSims.SourceHypotheses ρ) (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {t : G} (htS : IsSymmetricOuter e t) :
    6 ≤ fixedCodim ρ (zpowers t) := by
  obtain ⟨y, hxL, hx4, hx2⟩ := HSOuterCalculations.symmetric_order_four_commutator h e htS
  let x := t * y * t⁻¹ * y⁻¹
  have hlow := (higmanSims_inner_estimates h hd).involution (x^2)
    ((generalizedFitting G).pow_mem hxL 2) hx2 (by
      rw [← pow_mul]
      exact hx4)
  have hhigh := fixedCodim_commutator_le_twice ρ t y
  change fixedCodim ρ (zpowers x) ≤ 2 * fixedCodim ρ (zpowers t) at hhigh
  have hlinear := HSOuterCalculations.SymmetricLinear.displacement_square (ρ x) (by
    rw [← map_pow, hx4, map_one])
  have hh : 3 * fixedCodim ρ (zpowers (x^2)) ≤ 2 * fixedCodim ρ (zpowers x) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rw [map_pow]
    exact hlinear
  omega


/-- Every degree-twenty cubic source actor contains a symmetric outer involution
and has rank four or five. The elementary centralizer closure is discharged
on the same actor, without any remaining outer-calculation premise. -/
theorem higmanSims_cubic_symmetric_actor
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}
    (h : HigmanSims.SourceHypotheses ρ) (hd : Module.finrank (ZMod 2) V = 20)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* Carrier)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ t ∈ A, IsSymmetricOuter e t ∧ (rank A = 4 ∨ rank A = 5) := by
  let := hA.2
  have hs : ∃ t ∈ A, IsSymmetricOuter e t := by
    rcases higmanSims_cubic_outer_cases h hd e hA hsmall with
      ⟨hr, _hc, t, htA, htE, hn⟩ | ⟨t, htA, _ht2, htS⟩
    · rcases HSOuterCalculations.elementary_rank_five_cases h e hA hr htA htE with
        ⟨x, hxC, hxL, hx5⟩ | hs
      · exact (hn x hxC hxL hx5).elim
      · exact hs
    · exact ⟨t, htA, htS⟩
  obtain ⟨t, htA, htS⟩ := hs
  have hmono {x : G} (hx : x ∈ A) : fixedCodim ρ (zpowers x) ≤ fixedCodim ρ A := by
    have hm := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hx))
    have h1 := fixedCodim_add_finrank ρ (zpowers x)
    have h2 := fixedCodim_add_finrank ρ A
    omega
  have hsix := (higmanSims_symmetric_outer_involution_bound h hd e htS).trans (hmono htA)
  have hr2 : 2 ≤ rank A := by omega
  obtain ⟨x, hxA, hxL, hx1, hx2⟩ := exists_inner_involution h hA hr2
  have height := ((higmanSims_inner_estimates h hd).involution x hxL hx1 hx2).trans (hmono hxA)
  have hr5 := hA.rank_le_of_primeRank_le h.twoRank_le_five
  exact ⟨t, htA, htS, by omega⟩

end CFSG.Quasithin.ChapterK.SporadicCatalogue
