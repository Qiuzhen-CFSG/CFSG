module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessTorus
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceCentralTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessRanks
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSaturatedTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceCentralTorus

/-!
# Saturation of the original geometric Hermitian witnesses

Attainment of the weak-closure minimum identifies the actual core actor with
the canonical offender. Hermitian saturation identifies its rank-four-n plane,
its central intersection and its normality relative to the original Sylow.
Centrality makes every relative torus fix this plane pointwise, forcing its
full odd order into the determinant norm. For odd witness degree, the plane
exponent also bounds that degree by the half-field degree.

The Chapter 12 consumer uses these calculations in the original SQTK normalizer.
No ambient generation-parameter divisibility or torus fixed-space callback is
assumed. Half-degree one is retained; its ambient endgame remains separate.
Source: Aschbacher--Smith E.3.27--28, H.4.4 and 8.2.2--5,
pp.236--237,381,714--717, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

theorem offender_of_parameter_bound
    (s : GeometricSelected H T M V I k i S) (hT : HypothesisE322 V T)
    (hw : (k : ℕ∞) ≤ globalW V T) :
    globalW V T = k ∧ IsWOffenderAt V T i.val⁻¹ ∧
      offenderNormalizer V i.val⁻¹ =
        V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      offenderNormalizer V i.val⁻¹ ≤ T ∧
      offenderNormalizer V i.val⁻¹ ⊓ centralizer (V : Set G) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨hAT,hAC,hcor,hker,hupper⟩ := core_actor_data s hT
  have hew := le_antisymm hupper hw
  obtain ⟨he,hOff⟩ := normalizer_eq_of_attaining_corank hT i.val⁻¹ _
    (le_inf inf_le_left (hAT.trans hT.normalizes)) hAC (by rw [hcor]; exact hew)
  exact ⟨hew,hOff,he.symm,he ▸ hAT,he ▸ hker⟩

theorem hermitian_parameters
    (s : GeometricSelected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ)
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n) :
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧
      offenderNormalizer V i.val⁻¹ ≤ T ∧
      offenderNormalizer V i.val⁻¹ ⊓ centralizer (V : Set G) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  have hupper := (core_actor_data s hT).2.2.2.2
  have hnk : n ≤ k := ENat.natCast_le_natCast.mp (hw.trans hupper)
  have he : k = n := le_antisymm hk hnk
  obtain ⟨hew,hOff,_,hAT,hker⟩ := offender_of_parameter_bound s hT (he ▸ hw)
  exact ⟨he,hew.trans (congrArg (fun x : ℕ => (x : ℕ∞)) he),hOff,hAT,hker⟩

theorem hermitian_fixed_subgroup
    (s : GeometricSelected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3*n ≤ rank A → 5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) :
    let A := offenderNormalizer V i.val⁻¹
    let U := V ⊓ centralizer (A : Set G)
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧ A ≤ T ∧
      A = V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      ⁅⁅⁅V,A⁆,A⁆,A⁆ = ⊥ ∧ rank (inducedAutomizer V A) = 4*n ∧ rank U = 4*n ∧
      globalR V ≤ ((5*n : ℕ) : ℕ∞) ∧
      U = A ⊓ centralizer (V : Set G) ∧ U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) := by
  obtain ⟨hkn,hew,hOff,hAT,hker⟩ := hermitian_parameters s hT n hw hk
  have hkw : (k : ℕ∞) ≤ globalW V T := by rw [hkn,hew]
  have hA := (offender_of_parameter_bound s hT hkw).2.2.1
  obtain ⟨ha,hu,_,hrupper⟩ := offender_parameters_of_coordinates V T n e j hj he
    hgeometry i.val⁻¹ hT hOff hew hr hker
  obtain ⟨huA,huZ,huT,huN,hIC⟩ := offender_fixed_normal_of_coordinates V T n e j hj he
    hgeometry i.val⁻¹ hT hOff hew hr hker hAT
  have hc := selected_actor_cubic I M V (s.generate ▸ le_sup_left) S i s.twoConjugate
  rw [← hA] at hc
  rw [s.generate] at hIC
  exact ⟨hkn,hew,hOff,hAT,hA,hc,ha,hu,hrupper,huA,huZ,huT,huN,hIC⟩

theorem saturated_fixed_subgroup
    (s : GeometricSelected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := V ⊓ centralizer (A : Set G)
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧
      A = offenderNormalizer V i.val⁻¹ ∧ A ≤ T ∧
      rank (inducedAutomizer V A) = 4*n ∧ rank U = 4*n ∧
      U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR V ≤ ((5*n : ℕ) : ℕ∞) := by
  obtain ⟨hkn,hew,hOff,hAT,hA,_,ha,hu,hr',_,hU,hn,hN,hI⟩ :=
    hermitian_fixed_subgroup s hT n e j hj he
      (large_actor_geometry n) hw hk hr
  rw [hA] at hAT ha hu hU hn hN hI
  exact ⟨hkn,hew,hOff,hA.symm,hAT,ha,hu,hU,hn,hN,hI,hr'⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
theorem intersection_le_torus_fixed
    (s : GeometricSelected H T M V I k i S) (x : Automizer V)
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

theorem torus_fixed_rank_lower
    (s : GeometricSelected H T M V I k i S) (n : ℕ)
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
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hb := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  have hi := actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hi
  have hl := intersection_le_torus_fixed s x hx
  have hrl : rank (V ⊓ W) ≤ rank (automizerFixedGroup V (zpowers x)) :=
    Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hl) (inclusion_injective hl))
  rw [fixedGroup_rank] at hrl
  omega

theorem odd_parameter_le_half_degree
    (s : GeometricSelected H T M V I k i S) (hodd : Odd k)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) : k ≤ n := by
  have hu := parameter_le_twice_half_degree s n j hj
  have hkn : k < 2*n := by
    have hne : k ≠ 2*n := fun hh => hodd.not_two_dvd_nat (hh ▸ dvd_mul_right 2 n)
    omega
  by_contra! hnk
  obtain ⟨_,x,_,_,_,hx,ho⟩ := exists_automizer_torus s (by have hp := NeZero.pos n; omega)
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
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
  have hlarge := torus_fixed_rank_lower s n hdim hrank hkn x hx
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
  have hsum := (actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2
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
      (mem_map_of_mem f (normalizes_actor s hx))
  have hd := odd_order_dvd_of_large_inner_actor n B hBL (by omega)
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hl hnorm
  rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd s.positive).mp hd
  have hc : Nat.Coprime k 4 := by simpa using hodd.coprime_two_right.pow_right 2
  have hknDiv := hc.dvd_of_dvd_mul_left hkdiv
  exact (not_le_of_gt hnk) (Nat.le_of_dvd (NeZero.pos n) hknDiv)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

theorem saturated_torus_det_norm_of_centrality
    (s : GeometricSelected H T M V I k i S) (hT : HypothesisE322 V T)
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
    saturated_fixed_subgroup s hT n e j hj he hw hk hr
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hT.normalizes
  have hfixed : automizerFixedGroup V (inducedAutomizer V A) ≤
      automizerFixedGroup V (zpowers x) := by
    rw [automizerFixedGroup_induced V A hAN,hU]
    exact intersection_le_torus_fixed s x hx
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

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
