module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeOddInvolution
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeTensor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeInvolutions
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeInvolutions
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24-code tensor pair and its odd involution

The full original LT action restricts to a covering of the sextet stabilizer
at the marked four-space. Sylow conjugacy and genuine involution lifting
produce an order-two element of the same original T with odd hexacode image.
The original relative-normalizer residual covers the full even group 3.A6;
together with that odd element it covers the full hexacode group. The latter
has trivial two-core, so the involution escapes L_U O₂(L_U T), with the whole
source two-core retained. Its native image inverts the central cubic.

The application retains the same selected pair, its full product action,
faithful multiplicity plane and D10 quotient. It supplies the involution
selection in 8.2.8(6); the contradiction under T-normalization of O²(I) and
the ensuing code exclusion are subsequent obligations.

Source: Aschbacher--Smith 8.2.8(4--6), printed pp.718--719,
refs/quasithin.pdf. The imported native sextet models retain their ATLAS
attribution and license in LICENSES/ATLAS.txt. The internal imports expose
only the original conjugation formulas for comparing the covering maps.
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

/-- A Sylow-invariant original code four-space supplies a genuine odd
involution, outside the original residual times its full join two-core. -/
theorem sourceOrbit_m24_code_odd_involution_of_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    (U : Subgroup G) (hUW : U ≤ D.sourceOrbit)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (c : M24)
    (hspace : ∀ w : D.sourceOrbit, (w : G) ∈ U ↔
      codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet) :
    let J := L ⊔ (T : Subgroup G)
    let N := J ⊓ normalizer (U : Set G)
    ∃ f : N →* sextetStabilizer standardSextet,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      (∀ n, (f n).val = c * a (D.mathieuJoinAutomizer ⟨n,n.property.1⟩) * c⁻¹) ∧
      ∃ t : T, orderOf t = 2 ∧
        hexSign (nativeQuotient standardSextet
          (f ⟨t,mem_sup_right t.property,hTU t.property⟩)) = -1 ∧
        (t : G) ∉ localResidual L U ⊔
          (localResidual L U ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  let W := D.sourceOrbit
  let J := L ⊔ (T : Subgroup G)
  let N := J ⊓ normalizer (U : Set G)
  let q₀ : J →* M24 := a.toMonoidHom.comp D.mathieuJoinAutomizer
  let q : J →* M24 := (MulAut.conj c).toMonoidHom.comp q₀
  obtain ⟨hq₀,hk₀⟩ := D.sourceOrbit_m24_join_cover h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq a
  have hJW : J ≤ normalizer (W : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (codeRepresentation.asGroupHom c))
  have hF (j : J) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨j,hJW j.property⟩ w)) =
        codeRepresentation (q j) (F (Additive.ofMul w)) := by
    change codeRepresentation c (E (automizerRepresentation W
      (D.mathieuJoinAutomizer j) (Additive.ofMul w))) =
      codeRepresentation (c * a (D.mathieuJoinAutomizer j) * c⁻¹)
        (codeRepresentation c (E (Additive.ofMul w)))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  obtain ⟨f,hf,hfk,hval,hpoint⟩ := CodeNormalizer.marked_normalizer_action W J U hJW
    hUW q ((MulAut.conj c).surjective.comp hq₀) F hF standardSextet hspace
  have hk : IsPGroup 2 f.ker := by
    rw [hfk,MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective]
    exact hk₀.comap_of_injective _ (inclusion_injective _)
  have hTN : (T : Subgroup G) ≤ N := le_inf le_sup_right hTU
  let P : Sylow 2 (sextetStabilizer standardSextet) :=
    (T.subtype hTN).mapSurjective hf
  obtain ⟨y,hy,hy2,hyodd⟩ := NormalizedShadowRows.CodeInvolutions.sextet_sylow_odd_involution standardSextet P
  obtain ⟨n,hn,hny⟩ := hy
  let x := (MulAut.conj c).symm y.val
  have hx2 : orderOf x = 2 :=
    ((MulAut.conj c).symm.orderOf_eq _).trans ((orderOf_injective
      (sextetStabilizer standardSextet).subtype (Subtype.val_injective) y).trans hy2)
  have hnx : q₀ ⟨n,n.property.1⟩ = x := by
    apply (MulAut.conj c).injective
    exact (hval n).symm.trans ((congrArg Subtype.val hny).trans
      ((MulAut.conj c).apply_symm_apply y.val).symm)
  have hxT : x ∈ ((T : Subgroup G).subgroupOf J).map q₀ :=
    ⟨⟨n,n.property.1⟩,hn,hnx⟩
  obtain ⟨t,ht,ht2⟩ := D.sourceOrbit_m24_code_sylow_involution_lifts
    h hmany hV hq hnon a E hE x hx2 hxT
  have hty : f ⟨t,mem_sup_right t.property,hTU t.property⟩ = y := by
    apply Subtype.ext
    rw [hval]
    change (MulAut.conj c) (q₀ ⟨t,mem_sup_right t.property⟩) = y.val
    rw [ht]
    exact (MulAut.conj c).apply_symm_apply y.val
  have htodd : hexSign (nativeQuotient standardSextet
      (f ⟨t,mem_sup_right t.property,hTU t.property⟩)) = -1 := hty ▸ hyodd
  let NL := L ⊓ normalizer (U : Set G)
  let qL : L →* M24 := q.comp (inclusion (show L ≤ J from le_sup_left))
  have hqL : Function.Surjective qL := (MulAut.conj c).surjective.comp
    (a.surjective.comp (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq)))
  have hFL (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom
        ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        codeRepresentation (qL l) (F (Additive.ofMul w)) :=
    hF (inclusion (show L ≤ J from le_sup_left) l) w
  obtain ⟨fL,hfL,hfkL,hvalL,_⟩ := CodeNormalizer.marked_normalizer_action W L U
    D.sourceOrbit_component_normalizes hUW qL hqL F hFL standardSextet hspace
  have hkL : IsPGroup 2 fL.ker := by
    have heq : qL.ker = q₀.ker.comap (inclusion (show L ≤ J from le_sup_left)) := by
      ext l
      exact (MulAut.conj c).map_eq_one_iff
    rw [hfkL,heq]
    exact (hk₀.comap_of_injective (inclusion (show L ≤ J from le_sup_left))
      (inclusion_injective _)).comap_of_injective _ (inclusion_injective _)
  obtain ⟨r,hrange,_,_,hrval⟩ := CodeNormalizer.marked_residual_core_action
    L U standardSextet fL hfL hkL
  obtain ⟨e,he,heval⟩ := Chapter7.NormalizedSource.MathieuSextet.marked_even_quotient
    standardSextet r hrange
  let R := localResidual L U
  let JRT := R ⊔ (T : Subgroup G)
  have hRN : R ≤ N := le_inf
    (((localResidual_le L U).trans inf_le_left).trans le_sup_left)
    ((localResidual_le L U).trans inf_le_right)
  have hRTN : JRT ≤ N := sup_le hRN hTN
  let g : JRT →* HexAutomorphisms :=
    (nativeQuotient standardSextet).comp (f.comp (inclusion hRTN))
  have hRval (b : R) : g (inclusion (show R ≤ JRT from le_sup_left) b) = (e b).val := by
    rw [heval,hrval]
    apply congrArg (nativeQuotient standardSextet)
    apply Subtype.ext
    simp only [MonoidHom.comp_apply]
    rw [hval,hvalL]
    rfl
  have himage : (R.subgroupOf JRT).map g = hexSign.ker := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      have hv := hRval ⟨b,hb⟩
      change g b = _ at hv
      change g b ∈ hexSign.ker
      rw [hv]
      exact (e ⟨b,hb⟩).property
    · intro hx
      obtain ⟨b,hb⟩ := he ⟨x,hx⟩
      refine ⟨inclusion (show R ≤ JRT from le_sup_left) b,b.property,?_⟩
      exact (hRval b).trans (congrArg Subtype.val hb)
  let tRT : JRT := ⟨t,mem_sup_right t.property⟩
  have htRT : hexSign (g tRT) = -1 := htodd
  have hg : Function.Surjective g :=
    NormalizedShadowRows.CodeInvolutions.hex_surjective_of_even_and_odd g
      (himage.symm ▸ (show (R.subgroupOf JRT).map g ≤ g.range from Subgroup.map_le_range g _))
      tRT htRT
  have hnot := NormalizedShadowRows.CodeInvolutions.odd_not_mem_even_sup_core
    g hg (R.subgroupOf JRT) himage.le tRT htRT
  have hout : (t : G) ∉ R ⊔ JRT.pCoreIn 2 := by
    have hm : (R.subgroupOf JRT ⊔ pCore 2 JRT).map JRT.subtype = R ⊔ JRT.pCoreIn 2 := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show R ≤ JRT from le_sup_left)]
      rfl
    intro htmem
    rw [←hm] at htmem
    obtain ⟨b,hb,hbt⟩ := htmem
    have heq : b = tRT := Subtype.ext hbt
    exact hnot (heq ▸ hb)
  exact ⟨f,hf,hk,hval,t,ht2,htodd,hout⟩

/-- The original tensor pair and its actual odd Sylow involution, with
both covering kernels and the cubic hexacode quotient retained. -/
theorem sourceOrbit_m24_code_odd_tensor_pair_of_many
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
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let R := localResidual L U
      let J := L ⊔ (T : Subgroup G)
      let N := J ⊓ normalizer (U : Set G)
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 6 ∧ rank U = 4 ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      CodePairProductAction R I D.sourceOrbit U ∧
      CodePairNaturalAction R I D.sourceOrbit U i ∧
      CodePairMultiplicityAction R I D.sourceOrbit U i ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5) ∧
      ∃ hTU : (T : Subgroup G) ≤ normalizer (U : Set G),
        ∃ (c : M24) (f : N →* sextetStabilizer standardSextet),
          (∀ w : D.sourceOrbit, (w : G) ∈ U ↔
            codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet) ∧
          Function.Surjective f ∧ IsPGroup 2 f.ker ∧
          (∀ n, (f n).val = c * a (D.mathieuJoinAutomizer ⟨n,n.property.1⟩) * c⁻¹) ∧
          ∃ t : T, orderOf t = 2 ∧
            hexSign (nativeQuotient standardSextet
              (f ⟨t,mem_sup_right t.property,hTU t.property⟩)) = -1 ∧
            nativeQuotient standardSextet (f ⟨t,mem_sup_right t.property,hTU t.property⟩) *
              hexZ * (nativeQuotient standardSextet
                (f ⟨t,mem_sup_right t.property,hTU t.property⟩))⁻¹ = hexZ⁻¹ ∧
            (t : G) ∉ R ⊔ (R ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,hjoin,hmeet,hBA,hUU,hIK,hsec,
    hp,hpair,hm,hD,hfive,hcubic,hrest⟩ :=
    D.sourceOrbit_m24_code_tensor_pair_of_many h hmany hV hq hnon a E hE hH
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let Abar := inducedAutomizer W A
  let U := W ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 Abar := offender_inducedAutomizer_elementary W i.val⁻¹
  let : IsElementaryAbelian 2 (Abar.map a.toMonoidHom) := IsElementaryAbelian.map _
  have hcor := fixedCodim_inducedAutomizer W A
    (show A ≤ normalizer (W : Set G) from inf_le_right)
  have ht := fixedCodim_map_equivariant (automizerRepresentation W)
    codeRepresentation a.toMonoidHom E hE Abar
  have hv : rank W = 11 :=
    (Chapter7.log_card_eq_finrank W).trans (E.finrank_eq.trans finrank_code)
  have hsum := offender_corank_add (W := W) (A := U) (B := ⊥) bot_le inf_le_left
  have hsum' : rank W = subgroupCorank W U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
  have hseven : subgroupCorank W U = 7 := by
    change rank U = 4 at hu
    rw [hv,hu] at hsum'
    omega
  have hcod : fixedCodim codeRepresentation (Abar.map a.toMonoidHom) ≤ 7 := by
    rw [←ht,hcor]
    exact hseven.le
  obtain ⟨c,hc⟩ := NormalizedShadowRows.CodeRank.sextet_marking (Abar.map a.toMonoidHom)
    ((rank_map_injective a.toMonoidHom a.injective Abar).trans hr) hcod
  obtain ⟨hspace,_⟩ := D.sourceOrbit_m24_code_normalizer_of_sextet h hmany hV hq hnon
    a E hE A inf_le_right c hc
  obtain ⟨f,hf,hfk,hval,t,ht2,htodd,hout⟩ := D.sourceOrbit_m24_code_odd_involution_of_marking
    h hmany hV hq hnon a E hE U inf_le_left hTU c hspace
  exact ⟨I,i,S,s,hfix,hIC,hr,hu,hcomm,hp,hpair,hm,hD,hTU,c,f,hspace,hf,hfk,hval,
    t,ht2,htodd,hex_conjugation_odd _ htodd,hout⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
