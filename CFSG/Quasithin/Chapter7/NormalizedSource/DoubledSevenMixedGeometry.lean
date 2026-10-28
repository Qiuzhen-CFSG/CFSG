module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenOddElements
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenMixedPermutations


/-!
# Mixed centralizer images on the actual conjugate pair

An involution and a cubic cannot have a common fixed three-space on the
full H.8 pair. An odd actor interchanges the summands, and dimension in
either summand bounds its common fixed space by two. For inner actors,
a common fixed three-space would contain a plane in one summand. The
regular four-group and equality of involution fixed planes then force
the cubic's conjugate of the standard involution to commute with the
crossed involution. The permutation theorem supplies an odd transposition
centralizing the first involution. Transport through that transposition
forces the other summand's common fixed vectors to be fixed by a single
three-cycle, hence to vanish. This contradicts the proposed three-space.

Thus every image containing both an involution and a cubic has fixed
codimension at least six. The argument applies to every actual Pair and
uses both of its original summands, without the false assertion that an
individual cubic plane has cyclic pointwise stabilizer.
The original chosen-orbit consumer is NonFFSourceDoubledSevenBounds.
Source: Aschbacher--Smith, 7.5.5 and H.8, printed pp.701,389.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair
open Representation.AlternatingSevenConjugatePair.FixedFamily
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private def reversePair (D : Pair V) : Pair V where
  representation := D.representation
  faithful := D.faithful
  first := D.second
  second := D.first
  complementary := D.complementary.symm
  first_dim := D.second_dim
  second_dim := D.first_dim
  first_irreducible := D.second_irreducible
  second_irreducible := D.first_irreducible
  inequivalent := fun ⟨e⟩ => D.inequivalent ⟨e.symm⟩
  swap_first := D.swap_second
  swap_second := D.swap_first

private theorem first_commute (D : Pair V) (s t : S7)
    (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hse : s ∈ alternatingGroup (Fin 7)) (hte : t ∈ alternatingGroup (Fin 7))
    (he : D.firstFixedSpace (zpowers s) = D.firstFixedSpace (zpowers t)) :
    s * t = t * s := by
  let a : alternatingGroup (Fin 7) := ⟨s,hse⟩
  let b : alternatingGroup (Fin 7) := ⟨t,hte⟩
  have hfix : fixedSpace D.first.toRepresentation (zpowers a) =
      fixedSpace D.first.toRepresentation (zpowers b) := by
    ext v
    have hmem (z : alternatingGroup (Fin 7)) :
        v ∈ fixedSpace D.first.toRepresentation (zpowers z) ↔
          (v : V) ∈ D.firstFixedSpace (zpowers z.val) := by
      rw [mem_fixedSpace_zpowers_iff]
      constructor
      · intro hz
        exact ⟨v.property, (mem_fixedSpace_zpowers_iff _ _ _).mpr
          (congrArg Subtype.val hz)⟩
      · intro hz
        exact Subtype.ext ((mem_fixedSpace_zpowers_iff D.representation z.val (v : V)).mp hz.2)
    rw [hmem a,hmem b]
    change (v : V) ∈ D.firstFixedSpace (zpowers s) ↔ (v : V) ∈ D.firstFixedSpace (zpowers t)
    rw [he]
  have hh := commute_of_same_involution_fixedSpace D.first.toRepresentation
    D.first_faithful a b
    (Subtype.ext (show s ^ 2 = 1 by simpa only [hs] using pow_orderOf_eq_one s))
    (Subtype.ext (show t ^ 2 = 1 by simpa only [ht] using pow_orderOf_eq_one t)) hfix
  exact congrArg Subtype.val hh

private theorem cross_first_fixed (D : Pair V) :
    D.firstFixedSpace (zpowers crossSwap) = D.firstFixedSpace (zpowers centralInvolution) := by
  have hreg := (regularFour_dimensions D D.involution_fixedCodim).1
  have ht := (summand_involution_dimensions D D.involution_fixedCodim
    centralInvolution centralInvolution_order centralInvolution_mem.1.2).1
  have hk := (summand_involution_dimensions D D.involution_fixedCodim
    crossSwap crossSwap_order crossSwap_mem_regularFour.2).1
  have he (t : S7) (ht : t ∈ regularFour)
      (hd : Module.finrank (ZMod 2) (D.firstFixedSpace (zpowers t)) = 2) :
      D.firstFixedSpace regularFour = D.firstFixedSpace (zpowers t) :=
    Submodule.eq_of_le_of_finrank_eq
      (inf_le_inf_left _ (fixedSpace_antitone _ (zpowers_le.mpr ht))) (hreg.trans hd.symm)
  exact (he crossSwap crossSwap_mem_regularFour hk).symm.trans
    (he centralInvolution centralInvolution_mem.2 ht)

private theorem conjugate_commutes_cross (D : Pair V) (B : Subgroup S7)
    (ht : centralInvolution ∈ B) (s : S7) (hs : s ∈ B)
    (hd : Module.finrank (ZMod 2) (D.firstFixedSpace B) = 2) :
    crossSwap * (s * centralInvolution * s⁻¹) =
      (s * centralInvolution * s⁻¹) * crossSwap := by
  have htfix := (summand_involution_dimensions D D.involution_fixedCodim
    centralInvolution centralInvolution_order centralInvolution_mem.1.2).1
  have he : D.firstFixedSpace B = D.firstFixedSpace (zpowers centralInvolution) :=
    Submodule.eq_of_le_of_finrank_eq
      (inf_le_inf_left _ (fixedSpace_antitone _ (zpowers_le.mpr ht))) (hd.trans htfix.symm)
  let z := s * centralInvolution * s⁻¹
  have hz2 : orderOf z = 2 :=
    (orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
      centralInvolution).trans centralInvolution_order
  have hze : z ∈ alternatingGroup (Fin 7) :=
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem
      centralInvolution centralInvolution_mem.1.2 s
  have hzf := (summand_involution_dimensions D D.involution_fixedCodim z hz2 hze).1
  have hle : D.firstFixedSpace (zpowers centralInvolution) ≤ D.firstFixedSpace (zpowers z) := by
    intro v hv
    have hvB : v ∈ D.firstFixedSpace B := he.symm ▸ hv
    refine ⟨hv.1, (mem_fixedSpace_zpowers_iff _ _ _).mpr ?_⟩
    change D.representation (s * centralInvolution * s⁻¹) v = v
    simp only [map_mul, Module.End.mul_apply]
    have hi : D.representation s⁻¹ v = v := hvB.2 ⟨s⁻¹,B.inv_mem hs⟩
    have hsfix : D.representation s v = v := hvB.2 ⟨s,hs⟩
    rw [hi, (mem_fixedSpace_zpowers_iff _ _ _).mp hv.2, hsfix]
  have hez := Submodule.eq_of_le_of_finrank_eq hle (htfix.trans hzf.symm)
  exact first_commute D crossSwap z crossSwap_order hz2 crossSwap_mem_regularFour.2 hze
    ((cross_first_fixed D).trans hez)

private theorem second_fixed_zero (D : Pair V) (B : Subgroup S7)
    (ht : centralInvolution ∈ B) (s : S7) (hs : s ∈ B)
    (hd : Module.finrank (ZMod 2) (D.firstFixedSpace B) = 2)
    (g : S7) (hgo : g ∉ alternatingGroup (Fin 7)) (hg2 : g * g = 1)
    (hgt : centralInvolution * g = g * centralInvolution)
    (hthree : (s * (g*s*g)).IsThreeCycle) : D.secondFixedSpace B = ⊥ := by
  have htfix := (summand_involution_dimensions D D.involution_fixedCodim
    centralInvolution centralInvolution_order centralInvolution_mem.1.2).1
  have he : D.firstFixedSpace B = D.firstFixedSpace (zpowers centralInvolution) :=
    Submodule.eq_of_le_of_finrank_eq
      (inf_le_inf_left _ (fixedSpace_antitone _ (zpowers_le.mpr ht))) (hd.trans htfix.symm)
  apply bot_unique
  intro v hv
  change v = 0
  have hgv : D.representation g v ∈ D.firstFixedSpace (zpowers centralInvolution) := by
    refine ⟨D.swap_second g hgo v hv.1, (mem_fixedSpace_zpowers_iff _ _ _).mpr ?_⟩
    have htv : D.representation centralInvolution v = v := hv.2 ⟨centralInvolution,ht⟩
    rw [← Module.End.mul_apply, ← map_mul, hgt, map_mul, Module.End.mul_apply, htv]
  have hgB : D.representation g v ∈ D.firstFixedSpace B := he.symm ▸ hgv
  have hgg : D.representation g (D.representation g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, hg2, map_one]
    rfl
  apply SourceLineGeometry.threeCycle_fixedPointFree D _ hthree v
  simp only [map_mul, Module.End.mul_apply]
  have hsg : D.representation s (D.representation g v) = D.representation g v := hgB.2 ⟨s,hs⟩
  have hsv : D.representation s v = v := hv.2 ⟨s,hs⟩
  rw [hsg, hgg, hsv]

/-- An odd actor and an odd prime actor have at most a plane of common fixed vectors. -/
theorem doubledSeven_outer_mixed_fixed (D : Pair V) (B : Subgroup S7)
    (s : S7) (hs : s ∈ B) (hp : (orderOf s).Prime) (ho : orderOf s ≠ 2)
    (he : s ∈ alternatingGroup (Fin 7)) (hB : ¬ B ≤ alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (fixedSpace D.representation B) ≤ 2 := by
  obtain ⟨g,hg,hgo⟩ : ∃ g ∈ B, g ∉ alternatingGroup (Fin 7) := by
    by_contra hn
    exact hB (by intro g hg; by_contra hgo; exact hn ⟨g,hg,hgo⟩)
  have hdis : Disjoint (fixedSpace D.representation B) (D.firstFixedSpace (zpowers s)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hvf
    have hsecond : v ∈ D.second.toSubmodule :=
      (hv ⟨g,hg⟩) ▸ D.swap_first g hgo v hvf.1
    exact Submodule.disjoint_def.mp D.complementary.disjoint v hvf.1 hsecond
  have hle : fixedSpace D.representation B ⊔ D.firstFixedSpace (zpowers s) ≤
      fixedSpace D.representation (zpowers s) :=
    sup_le (fixedSpace_antitone _ (zpowers_le.mpr hs)) inf_le_right
  have hsum := (fixedSpace D.representation B).finrank_sup_add_finrank_inf_eq
    (D.firstFixedSpace (zpowers s))
  rw [hdis.eq_bot,finrank_bot,add_zero] at hsum
  have hmono := Submodule.finrank_mono hle
  have hsplit := D.finrank_fixedSpace (zpowers s) (zpowers_le.mpr he)
  let a : alternatingGroup (Fin 7) := ⟨s,he⟩
  have ha : orderOf a = orderOf s := (Subgroup.orderOf_coe a).symm
  have hc := two_le_fixedCodim_of_odd_prime D.second.toRepresentation D.second_faithful
    a (ha ▸ hp) (ha ▸ ho)
  have heq := (cyclicSummandFixedEquiv D.representation D.second a).finrank_eq
  have hr := fixedCodim_add_finrank D.second.toRepresentation (zpowers a)
  rw [D.second_dim] at hr
  change _ = Module.finrank (ZMod 2) (D.secondFixedSpace (zpowers s)) at heq
  omega

private theorem canonical_inner_fixed (D : Pair V) (B : Subgroup S7)
    (hB : B ≤ alternatingGroup (Fin 7)) (ht : centralInvolution ∈ B)
    (s : S7) (hs : s ∈ B) (hst : s.cycleType = {3,3})
    (hperm : ∀ q : S7, q.cycleType = {3,3} →
      crossSwap * (q * centralInvolution * q⁻¹) = (q * centralInvolution * q⁻¹) * crossSwap →
      ∃ g : S7, g ∉ alternatingGroup (Fin 7) ∧ g*g = 1 ∧
        centralInvolution*g = g*centralInvolution ∧ (q*(g*q*g)).IsThreeCycle) :
    Module.finrank (ZMod 2) (fixedSpace D.representation B) ≤ 2 := by
  have hd := summand_involution_dimensions D D.involution_fixedCodim
    centralInvolution centralInvolution_order centralInvolution_mem.1.2
  have hle := fixedSpace_antitone D.representation (zpowers_le.mpr ht)
  have hfirst := (Submodule.finrank_mono (inf_le_inf_left D.first.toSubmodule hle)).trans_eq hd.1
  have hsecond := (Submodule.finrank_mono (inf_le_inf_left D.second.toSubmodule hle)).trans_eq hd.2
  change Module.finrank (ZMod 2) (D.firstFixedSpace B) ≤ 2 at hfirst
  change Module.finrank (ZMod 2) (D.secondFixedSpace B) ≤ 2 at hsecond
  have hsum := D.finrank_fixedSpace B hB
  by_contra hn
  have hcases : Module.finrank (ZMod 2) (D.firstFixedSpace B) = 2 ∨
      Module.finrank (ZMod 2) (D.secondFixedSpace B) = 2 := by omega
  have kill (P : Pair V) (hd : Module.finrank (ZMod 2) (P.firstFixedSpace B) = 2) :
      P.secondFixedSpace B = ⊥ := by
    obtain ⟨g,hgo,hg2,hgt,hthree⟩ := hperm s hst (conjugate_commutes_cross P B ht s hs hd)
    exact second_fixed_zero P B ht s hs hd g hgo hg2 hgt hthree
  rcases hcases with hc | hc
  · have hz := kill D hc
    rw [hz,finrank_bot] at hsum
    omega
  · have hz : D.firstFixedSpace B = ⊥ := kill (reversePair D) hc
    rw [hz,finrank_bot] at hsum
    omega

/-- A centralizer image containing an involution and a cubic moves at
least six dimensions on the full conjugate pair. Both summands are essential. -/
theorem doubledSeven_mixed_fixedCodim (D : Pair V) (B : Subgroup S7)
    (t s : S7) (htB : t ∈ B) (hsB : s ∈ B) (ht : orderOf t = 2) (hs : orderOf s = 3)
    : 6 ≤ fixedCodim D.representation B := by
  by_contra hn
  have hc : fixedCodim D.representation B < 6 := by omega
  have hst := (doubledSeven_small_odd_prime D s (hs ▸ Nat.prime_three)
    (by omega) ((by
      have hmono := Submodule.finrank_mono (fixedSpace_antitone D.representation (zpowers_le.mpr hsB))
      have h1 := fixedCodim_add_finrank D.representation (zpowers s)
      have h2 := fixedCodim_add_finrank D.representation B
      omega : fixedCodim D.representation (zpowers s) < 6))).2
  have he : s ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_of_cycleType,hst]
    decide
  have hdim := fixedCodim_add_finrank D.representation B
  rw [D.finrank_eq_eight] at hdim
  by_cases hB : B ≤ alternatingGroup (Fin 7)
  · obtain ⟨g,hg⟩ := doubledSeven_even_involution_conjugate t ht (hB htB)
    let C := B.map (MulAut.conj g).toMonoidHom
    have hC : C ≤ alternatingGroup (Fin 7) := by
      rintro _ ⟨b,hb,rfl⟩
      exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem b (hB hb) g
    have htC : centralInvolution ∈ C := hg ▸ mem_map_of_mem _ htB
    have hsC : g*s*g⁻¹ ∈ C := mem_map_of_mem _ hsB
    have hstC : (g*s*g⁻¹).cycleType = {3,3} := Equiv.Perm.cycleType_conj.trans hst
    have hb := canonical_inner_fixed D C hC htC _ hsC hstC doubledSeven_mixed_transposition
    have hdC := fixedCodim_add_finrank D.representation C
    rw [D.finrank_eq_eight] at hdC
    have hcod : fixedCodim D.representation C = fixedCodim D.representation B :=
      fixedCodim_map_conj D.representation B g
    omega
  · have hb := doubledSeven_outer_mixed_fixed D B s hsB (hs ▸ Nat.prime_three)
      (by omega) he hB
    omega

end CFSG.Quasithin.Chapter7.NormalizedSource
