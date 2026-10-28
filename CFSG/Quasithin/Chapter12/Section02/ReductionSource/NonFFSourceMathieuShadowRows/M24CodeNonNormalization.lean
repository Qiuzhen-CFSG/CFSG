module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeOddInvolution
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeExtension
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSolvable
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeInvolutions

/-!
# The original M24-code pair is not normalized by T

The same full original sextet map restricts to a cover of the even hexacode
group, with kernel exactly O₂(L_U). Under hypothetical normalization of
O²(I), the source identity I = O²(I)V makes T normalize I and its two-core.
The original odd involution therefore extends the literal tensor action.
Cubic inversion transfers through the retained kernel, and the checked
D10 fixed-rank contradiction excludes this extension.

Thus source 8.2.8(6) holds for the unchanged original pair. Its application
to the actual H/O₂(H) rules out a prime-order two-residual. The complete
solvable parabolic list and five-rank bound then rule out solvable H.
The nonsolvable sieve in 8.2.9 and the final code exclusion remain to be
proved; these results do not select M24 cocode.

The internal imports expose only the existing original component/join
conjugation maps for their literal comparison. Public boundaries are
unchanged. Source: Aschbacher--Smith 8.2.8(6)--8.2.9, printed pp.719--720,
refs/quasithin.pdf. Native model attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Restriction of the same full original sextet covering to L_U covers
3.A6 with exactly its intrinsic two-core as kernel. -/
theorem sourceOrbit_m24_code_full_residual_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    (U : Subgroup G) (hUW : U ≤ D.sourceOrbit) (c : M24)
    (hspace : ∀ w : D.sourceOrbit, (w : G) ∈ U ↔
      codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet)
    (f : ((L ⊔ (T : Subgroup G)) ⊓ normalizer (U : Set G) : Subgroup G) →*
      sextetStabilizer standardSextet)
    (hval : ∀ n, (f n).val = c * a (D.mathieuJoinAutomizer ⟨n,n.property.1⟩) * c⁻¹) :
    let R := localResidual L U
    let N := (L ⊔ (T : Subgroup G)) ⊓ normalizer (U : Set G)
    ∃ hRN : R ≤ N, ∃ p : R →* HexEvenAutomorphisms,
      Function.Surjective p ∧ p.ker = pCore 2 R ∧
      ∀ r, nativeQuotient standardSextet (f (inclusion hRN r)) = (p r).val := by
  let W := D.sourceOrbit
  let J := L ⊔ (T : Subgroup G)
  let N := J ⊓ normalizer (U : Set G)
  let q₀ : J →* M24 := a.toMonoidHom.comp D.mathieuJoinAutomizer
  let q : J →* M24 := (MulAut.conj c).toMonoidHom.comp q₀
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (codeRepresentation.asGroupHom c))
  let qL : L →* M24 := q.comp (inclusion (show L ≤ J from le_sup_left))
  have hqL : Function.Surjective qL := (MulAut.conj c).surjective.comp
    (a.surjective.comp (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq)))
  have hFL (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom
        ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        codeRepresentation (qL l) (F (Additive.ofMul w)) := by
    change codeRepresentation c (E (automizerRepresentation W
      (D.mathieuComponentAutomizer l) (Additive.ofMul w))) =
      codeRepresentation (c * a (D.mathieuComponentAutomizer l) * c⁻¹)
        (codeRepresentation c (E (Additive.ofMul w)))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  obtain ⟨fL,hfL,hfkL,hvalL,_⟩ := CodeNormalizer.marked_normalizer_action W L U
    D.sourceOrbit_component_normalizes hUW qL hqL F hFL standardSextet hspace
  obtain ⟨_,hk₀⟩ := D.sourceOrbit_m24_join_cover h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq a
  have hkL : IsPGroup 2 fL.ker := by
    have heq : qL.ker = q₀.ker.comap (inclusion (show L ≤ J from le_sup_left)) := by
      ext l
      exact (MulAut.conj c).map_eq_one_iff
    rw [hfkL,heq]
    exact (hk₀.comap_of_injective (inclusion (show L ≤ J from le_sup_left))
      (inclusion_injective _)).comap_of_injective _ (inclusion_injective _)
  obtain ⟨r,hrange,hrker,hrcore,hrval⟩ :=
    CodeNormalizer.marked_residual_core_action L U standardSextet fL hfL hkL
  obtain ⟨p,hp,hpval⟩ := Chapter7.NormalizedSource.MathieuSextet.marked_even_quotient
    standardSextet r hrange
  let R := localResidual L U
  have hRN : R ≤ N := le_inf
    (((localResidual_le L U).trans inf_le_left).trans le_sup_left)
    ((localResidual_le L U).trans inf_le_right)
  have hpk : p.ker = pCore 2 R := by
    have he : p.ker = (nativeQuotient standardSextet).ker.comap r := by
      ext x
      change p x = 1 ↔ nativeQuotient standardSextet (r x) = 1
      rw [←hpval]
      exact Subtype.ext_iff
    rw [he,←hrcore]
    exact Subgroup.comap_map_eq_self (le_sSup ⟨inferInstance,hrker⟩)
  refine ⟨hRN,p,hp,hpk,?_⟩
  intro x
  rw [hpval,hrval]
  apply congrArg (nativeQuotient standardSextet)
  apply Subtype.ext
  rw [hval,hvalL]
  rfl

/-- Source 8.2.8(6) on the original code pair: T cannot normalize its
embedded two-residual. The actual odd involution and both action kernels
are constructed from the unchanged Chapter12 hypotheses and marking. -/
theorem sourceOrbit_m24_code_nonnormalized_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5) ∧
      ¬ (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) := by
  obtain ⟨I,i,S,s,hfix,hIC,hr,hu,hcomm,hp,hnat,hm,hD,hTU,c,f,hspace,hf,hfk,hval,
    t,ht2,htodd,htinv,htout⟩ :=
    D.sourceOrbit_m24_code_odd_tensor_pair_of_many h hmany hV hq hnon a E hE hH
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let N := (L ⊔ (T : Subgroup G)) ⊓ normalizer (U : Set G)
  obtain ⟨hRN,p,hpSurj,hpk,hpval⟩ := D.sourceOrbit_m24_code_full_residual_cover
    h hmany hV hq hnon a E hE U inf_le_left c hspace f hval
  refine ⟨I,i,S,s,hD,?_⟩
  intro hTX
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) := by
    rw [←embedded_twoResidual_sup I W i.val i.property s.generate]
    exact (le_inf hTX D.sourceOrbit_weakClosure_setup.normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    normalizes_localResidual L U T D.sylow_normalizes_component hTU
  let K := (R ⊔ I) ⊔ (T : Subgroup G)
  have hRK : R ≤ K := le_sup_left.trans le_sup_left
  have hIK : I ≤ K := le_sup_right.trans le_sup_left
  have hpCopy := hp
  obtain ⟨hYP,hYU,_⟩ := hpCopy
  have hKP : K ≤ normalizer (I.pCoreIn 2 : Set G) := sup_le hYP
    (hTI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hKU : K ≤ normalizer (U : Set G) := sup_le hYU hTU
  exact code_pair_odd_extension_impossible hp hnat hm hD hRN hRK hIK hKP hKU
    p hpSurj hpk ((nativeQuotient standardSextet).comp f) hpval t
    ⟨mem_sup_right t.property,hTU t.property⟩ (mem_sup_right t.property)
    (hTR t.property) (hTI t.property)
    (by have he := pow_orderOf_eq_one t; rw [ht2] at he; exact congrArg Subtype.val he) htodd

/-- The same M24-code hypotheses force the original parabolic's two-core
quotient residual to have nonprime order. Thus the remaining source 8.2.9
sieve needs only its actual prime-order conclusion, not an assumed normalization. -/
theorem sourceOrbit_m24_code_parabolic_residual_not_prime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ (Nat.card (pResidual 2 (H ⧸ pCore 2 H))).Prime := by
  intro hprime
  obtain ⟨I,i,S,s,⟨eD⟩,hnorm⟩ :=
    D.sourceOrbit_m24_code_nonnormalized_pair_of_many h hmany hV hq hnon a E hE hH
  have hIH := s.family.le_ambient
  let eI : I.subgroupOf H ≃* I := subgroupOfEquivOfLe hIH
  let eQ := eI.toMonoidHom.pCoreQuotientEquiv (p := 2) eI.surjective
    (IsPGroup.ker_isPGroup_of_injective eI.injective)
  have hdiv : 5 ∣ Nat.card ((I.subgroupOf H) ⧸ pCore 2 (I.subgroupOf H)) := by
    rw [Nat.card_congr (eQ.trans eD).toEquiv,DihedralGroup.nat_card]
    decide
  have hcover := ParabolicReduction.RankSieve.quotient_cover_of_prime_residual_of_intrinsic_divisor
    (I.subgroupOf H) (by decide : Nat.Prime 5) (by decide) hprime hdiv
  exact hnorm (selected_one_conclusions_of_quotient_cover s hH
    D.sourceOrbit_weakClosure_setup.normalizes hcover).2.1

/-- The complete solvable minimal-parabolic list would force a cyclic
quintic residual, contradicting the original code tensor pair. This leaves
only the nonsolvable source sieve in the M24-code row. -/
theorem sourceOrbit_m24_code_parabolic_not_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ Group.IsSolvable H := by
  intro hsol
  obtain ⟨h28,_⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  obtain ⟨t,ht,htP,htM⟩ := h28.minimal
  have hVH := h28.le_sylow.trans h28.le_ambient
  have hout : ¬ (ChapterB.minimalParabolicMax t htP).pCoreIn 2 ≤ pCore 2 H := by
    intro hc
    apply D.sourceOrbit_m24_not_le_HStar_core h
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq hH
    intro v hv
    have hvmax : (⟨v,hVH hv⟩ : H) ∈ (ChapterB.minimalParabolicMax t htP).pCoreIn 2 := by
      rw [←htM]
      obtain ⟨x,hx,he⟩ := h28.le_local_core hv
      exact ⟨x,hx,Subtype.ext he⟩
    exact ⟨⟨v,hVH hv⟩,hc hvmax,rfl⟩
  obtain ⟨I,i,S,s,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h3,h5,_⟩ :=
    D.sourceOrbit_m24_code_parabolic_pair_of_many h hmany hV hq hnon a E hE hH
  obtain ⟨J,j,Q,sJ,⟨eD⟩,_⟩ :=
    D.sourceOrbit_m24_code_nonnormalized_pair_of_many h hmany hV hq hnon a E hE hH
  have hdivJ : 5 ∣ Nat.card J := by
    have hd : 5 ∣ Nat.card (J ⧸ pCore 2 J) := by
      rw [Nat.card_congr eD.toEquiv,DihedralGroup.nat_card]
      decide
    exact hd.trans (card_quotient_dvd_card (pCore 2 J))
  have hc := solvable_parabolic_residual_card h28.sqtk t htP hsol hout
    (by decide : Nat.Prime 5) (by decide)
    (hdivJ.trans (card_dvd_of_le sJ.family.le_ambient)) h5
  exact D.sourceOrbit_m24_code_parabolic_residual_not_prime h hmany hV hq hnon a E hE hH
    (hc ▸ (by decide : Nat.Prime 5))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
