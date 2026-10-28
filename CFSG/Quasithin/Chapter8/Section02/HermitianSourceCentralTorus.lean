module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSaturatedTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds

/-!
# Centrality suffices for the selected Hermitian torus

The original intersection Z = V intersect V^i is central in I, hence fixed
by every element of the relative automizer. Its rank gives a torus fixed
space larger than 3n whenever k < 2n. The large actor lies in the inner
Hermitian image, so the normalizing torus has order dividing 2^(4n)-1.
For odd k this forces k to divide n and excludes k > n. No E.2.14(9)
fixed-space equality is required.

At saturation k = w = n, the original intersection is the full actor-fixed
plane. The same torus therefore fixes that plane pointwise. In the actual
Hermitian coordinates it is an odd congruence whose determinant norm has
order 2^n-1. The Chapter 12 consumer uses the original SQTK normalizer to
exclude this torus and thereby closes the selected Suzuki alternative.
The calculation retains half-degree one; the final field-four exclusion
and source-family existence remain separate obligations.

Source: Aschbacher–Smith E.2.10(1), H.4.4 and 8.2.2–4,
printed pp.222,381,714–716 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

/-- Every element of the actual relative automizer fixes the original central
intersection. No assertion that these are all its fixed points is needed. -/
theorem selected_intersection_le_torus_fixed
    (s : Selected H T M V I k i S) (x : Automizer V)
    (hx : x ∈ inducedAutomizer V (M ⊓ I)) :
    V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≤
      automizerFixedGroup V (zpowers x) := by
  have hz : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≤
      automizerFixedGroup V (inducedAutomizer V (M ⊓ I)) := by
    rw [automizerFixedGroup_induced V (M ⊓ I) (s.normalizer_eq ▸ inf_le_right)]
    refine le_inf inf_le_left ?_
    rintro z hz a ha
    obtain ⟨w,hw,rfl⟩ := s.intersection_central hz
    exact congrArg I.subtype ((mem_center_iff.mp hw) (⟨a,ha.2⟩ : I))
  intro v hv
  obtain ⟨w,hw,rfl⟩ := hz hv
  refine ⟨w,?_,rfl⟩
  exact ChapterE.fixedSpace_antitone (automizerRepresentation V) (zpowers_le.mpr hx) hw

/-- Centrality alone supplies the large torus fixed space when k < 2n. -/
theorem selected_torus_fixed_rank_lower
    (s : Selected H T M V I k i S) (n : ℕ)
    (hdim : rank V = 9*n) (hrank : primeRank 2 (Automizer V) ≤ 4*n)
    (hkn : k < 2*n) (x : Automizer V)
    (hx : x ∈ inducedAutomizer V (M ⊓ I)) :
    3*n < Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hb := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  have hi := selected_actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hi
  have hl := selected_intersection_le_torus_fixed s x hx
  have hrl : rank (V ⊓ W) ≤ rank (automizerFixedGroup V (zpowers x)) :=
    Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hl) (inclusion_injective hl))
  rw [fixedGroup_rank] at hrl
  omega

/-- An odd selected parameter is at most the half-field degree. The torus
centralizes the original intersection, and its normalization of the large
inner actor forces k to divide 4n, hence n. -/
theorem selected_odd_parameter_le_half_degree
    (s : Selected H T M V I k i S) (hodd : Odd k)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) : k ≤ n := by
  have hu := selected_parameter_le_twice_half_degree s n j hj
  have hkn : k < 2*n := by
    have hne : k ≠ 2*n := fun hh => hodd.not_two_dvd_nat (hh ▸ dvd_mul_right 2 n)
    omega
  by_contra! hnk
  obtain ⟨_,x,_,_,_,hx,ho⟩ := selected_exists_automizer_torus s (by have hp := NeZero.pos n; omega)
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hm : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [←MonoidHom.map_zpowers,
      ←fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hlarge := selected_torus_fixed_rank_lower s n hdim hrank hkn x hx
  have hox : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by have hp := s.positive; omega)) odd_one
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,_⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hoj (hm ▸ hlarge)
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hsum := (selected_actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2
  change 5*n ≤ k + rank (inducedAutomizer V A) at hsum
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  have hBr : 2*n+1 < rank B := by
    rw [rank_map_injective f hfi]
    have hn := NeZero.pos n
    omega
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hBN hBr
  have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
    (inducedAutomizer V A).le_normalizer_map f
      (mem_map_of_mem f (selected_normalizes_actor s hx))
  have hd := odd_order_dvd_of_large_inner_actor n B hBL (by omega)
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hl hnorm
  rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd s.positive).mp hd
  have hc : Nat.Coprime k 4 := by simpa using hodd.coprime_two_right.pow_right 2
  have hknDiv := hc.dvd_of_dvd_mul_left hkdiv
  exact (not_le_of_gt hnk) (Nat.le_of_dvd (NeZero.pos n) hknDiv)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
private theorem fixedSpace_le_of_fixedGroup_le
    (X Y : Subgroup (Automizer V))
    (h : automizerFixedGroup V X ≤ automizerFixedGroup V Y) :
    fixedSpace (automizerRepresentation V) X ≤ fixedSpace (automizerRepresentation V) Y := by
  intro v hv
  have hv' : v.toMul.val ∈ automizerFixedGroup V X := ⟨v.toMul,hv,rfl⟩
  obtain ⟨w,hw,he⟩ := h hv'
  have hwv : w = v.toMul := Subtype.ext he
  subst w
  exact hw

/-- Saturation identifies the original central intersection with the actor
fixed plane. The torus fixes this plane, forcing its full order to survive
in the determinant norm. The full torus fixed-space equality is unnecessary. -/
theorem selected_saturated_torus_det_norm_of_centrality
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (ho : orderOf x = 2^k-1) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ (c : Cover n) (g : Matrix.GeneralLinearGroup (Fin 3) (E n)),
      ((inducedAutomizer V A).map ((binaryNormalizer n).subtype.comp j)).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n ∧
      binaryCongruence n g = (MulAut.conj (binaryActionHom n c)) (j x).val ∧
      Odd (orderOf g) ∧ orderOf (g.val.det * sigma n g.val.det) = 2^n-1 := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  obtain ⟨hkn,_,_,hA,hAT,ha,hu,hU,_,_,_,_⟩ :=
    selected_saturated_fixed_subgroup s hT n e j hj he hw hk hr
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hT.normalizes
  have hfixed : automizerFixedGroup V (inducedAutomizer V A) ≤
      automizerFixedGroup V (zpowers x) := by
    rw [automizerFixedGroup_induced V A hAN,hU]
    exact selected_intersection_le_torus_fixed s x hx
  have hspace := fixedSpace_le_of_fixedGroup_le _ _ hfixed
  have haf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) = 4*n := by
    rw [←fixedGroup_rank,automizerFixedGroup_induced V A hAN]
    exact hu
  have hxf : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) := by
    have hh := Submodule.finrank_mono hspace
    have hn := NeZero.pos n
    omega
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 (inducedAutomizer V A) := by
    change A = offenderNormalizer V i.val⁻¹ at hA
    rw [hA]
    exact offender_inducedAutomizer_elementary V i.val⁻¹
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBr : rank B = 4*n :=
    (rank_map_injective f ((binaryNormalizer n).subtype_injective.comp hj) _).trans ha
  have hm (Y : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) Y).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (Y.map f) :=
    fixedSpace_map_equivariant _ _ f e he Y
  have hBf : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) B) = 4*n := by
    rw [←hm,LinearEquiv.finrank_map_eq]
    exact haf
  obtain ⟨c,hc⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.saturated_actor_plane n B hBN hBr hBf
  have hxrank : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [←MonoidHom.map_zpowers,
      ←fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hodd : Odd (orderOf (j x)) := by
    rw [orderOf_injective j hj,ho]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by have hp := s.positive; omega)) odd_one
  obtain ⟨hlin,_⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hodd (hxrank ▸ hxf)
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hlin
  have hgo := OddExponent.odd_orderOf_of_odd_binaryCongruence n g
    (by rw [hg,Subgroup.orderOf_coe]; exact hodd)
  let u := binaryActionHom n c
  let z := (MulAut.conj u).toMonoidHom
  let g' := (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)) g
  have hg' : binaryCongruence n g' = z (j x).val := by
    change binaryCongruence n (Matrix.SpecialLinearGroup.toGL c * g *
      (Matrix.SpecialLinearGroup.toGL c)⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryCongruence_toGL,hg]
    rfl
  have hz : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBspace : fixedSpace (UnipotentRadicals.ambientAction n) B ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) := by
    rw [←hz,←hm,←hm]
    exact Submodule.map_mono hspace
  have hez (a : BinaryAut n) (v : Space n) :
      u (UnipotentRadicals.ambientAction n a v) =
        UnipotentRadicals.ambientAction n (z a) (u v) := by
    change u (a v) = u (a (u.symm (u v)))
    rw [u.symm_apply_apply]
  have hmz (Y : Subgroup (BinaryAut n)) := fixedSpace_map_equivariant
    (UnipotentRadicals.ambientAction n) (UnipotentRadicals.ambientAction n) z u hez Y
  have hplane : fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g')) := by
    rw [hg',←MonoidHom.map_zpowers,←hc,←hmz,←hmz]
    exact Submodule.map_mono hBspace
  have hord : orderOf (binaryCongruence n g') = 2^n-1 := by
    rw [hg',orderOf_injective z (MulAut.conj u).injective,Subgroup.orderOf_coe,
      orderOf_injective j hj,ho,hkn]
  have hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g' X = X := fun X hX =>
    (mem_fixedSpace_zpowers_iff _ _ _).mp (hplane hX)
  refine ⟨c,g',hc,hg',?_,plane_fixed_det_norm_order n g' hfix hord⟩
  exact (orderOf_injective (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).toMonoidHom
    (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).injective g).symm ▸ hgo

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
