module
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeComponent
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSection
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePairAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizerRange
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
/-!
# The original M22-code five-space and ten-space actions

The original degree-one pair has its literal B/U identified with the
five-dimensional quintet kernel. The perfect residual R = L_U acts through
A5 with kernel exactly O₂(R), displacement rank four and coinvariant rank
one. The N_L(U) marking retains the entire original component-map kernel.
It also records the full native affine image of R together with its
compatible global M22 quotient and the same whole-code coordinates.

The two original conjugates of B generate P = O₂(I). Their quotient actions
extend the residual kernel to P/U and identify (RI)/O₂(RI) with the product
of the two original two-core quotients. The resulting rank-ten section is
two copies of the same quintet module. The marking records the literal B/U
inclusion, the chosen inverse conjugator, and the same five-part quotient
of the original quintet map. All premises are discharged on the unchanged
pair supplied by the original Chapter12 hypotheses.

This supplies the M22-code action and kernel assertions used in 8.2.8(4--5).
The deduction I/O₂(I) ≅ L₂(2), the tensor action, R = K_U, and the later
8.2.9--13 exclusion and unconditional M24-cocode selection remain separate
source obligations.

Source: Aschbacher--Smith 8.2.8, printed pp.718--719, and H.16.3(3),
printed p.403, refs/quasithin.pdf. Native code attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency true in
/-- Mark the literal B/U on any original degree-one quintet pair.
The full N_L(U) covering kernel is retained, separately from the residual two-core. -/
theorem sourceOrbit_m22_code_five_section_full
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hA : offenderNormalizer D.sourceOrbit i.val⁻¹ =
      D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)
    (hAT : offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T)
    (hfix : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hfour : rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) = 4)
    (hfive : rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)) = 5) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
    let B := D.sourceOrbit ⊓ I.pCoreIn 2
    let N := L ⊓ normalizer (U : Set G)
    let R := localResidual L U
    ∃ f : N →* M22Quintet.Q,
      f.ker = D.orbitComponentHom.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
      M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) ∧
      (f.comp (inclusion (localResidual_le L U))).range = M22ChapterH.Quintet.naturalActor ∧
      ∃ (p : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer)
        (q : L →* M22) (F : Additive D.sourceOrbit ≃ₗ[ZMod 2] M22Code),
        Function.Injective p ∧ Function.Surjective q ∧ q.ker = D.orbitComponentHom.ker ∧
        (∀ b v, F (automizerRepresentation D.sourceOrbit b v) =
          m22OuterCodeRepresentation (p b) (F v)) ∧
        (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)).map p =
          M22Quintet.K ∧
        (∀ l : L, m22ToPairStabilizer (q l) = p
          (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
            (inclusion D.sourceOrbit_component_normalizes l))) ∧
        (∀ n : N, (f n).val = m22ToPairStabilizer (q ⟨n,n.property.1⟩)) := by
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let B := W ⊓ I.pCoreIn 2
  let R := localResidual L U
  let N := L ⊓ normalizer (U : Set G)
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have hex := @sourceOrbit_m22_code_full_automizer G _ _ T L V D h d
  rcases hex with ⟨a,hinj,hE,haval,_⟩
  let : IsElementaryAbelian 2 (inducedAutomizer W A) := offender_inducedAutomizer_elementary W i.val⁻¹
  let : IsElementaryAbelian 2 ((inducedAutomizer W A).map a) := IsElementaryAbelian.map _
  have hm : rank ((inducedAutomizer W A).map a) = 5 :=
    (rank_map_injective a hinj (inducedAutomizer W A)).trans hfive
  have hc0 : ∃ c : MathieuCode.m22PairStabilizer,
      ((inducedAutomizer W A).map a).map (MulAut.conj c).toMonoidHom =
        MathieuCode.m22OuterQuintetKernel MathieuCode.m22SourceSextet :=
    NormalizedShadowRows.M22CodeQuintet.quintet_marking ((inducedAutomizer W A).map a) hm
  rcases hc0 with ⟨c,hc⟩
  have hAN : A ≤ normalizer (W : Set G) := hAT.trans D.sourceOrbit_weakClosure_setup.normalizes
  have hexr := @sourceOrbit_m22_code_fourSpace_residual G _ _ T L V D h d A hAN hfour a hE c hc
  rcases hexr with ⟨f,eU,r,hp,hfk,hval,hrsur,hrc,hrk,hrval,hract,_⟩
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (m22OuterCodeRepresentation.asGroupHom c))
  let p : Automizer W →* MathieuCode.m22PairStabilizer := (MulAut.conj c).toMonoidHom.comp a
  have hF (b : Automizer W) (v : Additive W) :
      F (automizerRepresentation W b v) = m22OuterCodeRepresentation (p b) (F v) := by
    change m22OuterCodeRepresentation c (E (automizerRepresentation W b v)) =
      m22OuterCodeRepresentation (c*a b*c⁻¹) (m22OuterCodeRepresentation c (E v))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hmark : (inducedAutomizer W A).map p = M22Quintet.K := by
    rw [←map_map]
    exact hc
  have hmark0 := hmark
  have hAN' : W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ≤ normalizer (W : Set G) := hA ▸ hAN
  have hfix' := hfix
  have hfour' := hfour
  dsimp only [W,A] at hmark
  rw [hA] at hmark hfix' hfour'
  have hcoords := @selected_m22_code_section_coordinates G _ _ D.sourceOrbit _ T H
    (normalizer (L : Set G)) I i S s F p hF hAN' hfix' hmark hfour'
  rcases hcoords with ⟨hU,hB⟩
  have hU' (v : Additive W) : (v.toMul : G) ∈ U ↔ F v ∈ M22Quintet.V4 := by
    change (v.toMul : G) ∈ W ⊓ centralizer (A : Set G) ↔ _
    dsimp only [W,A]
    rw [hA]
    exact hU v
  let fR : R →* M22Quintet.Q := f.comp (inclusion (localResidual_le L U))
  have hRV : R ≤ normalizer (W : Set G) :=
    ((localResidual_le L U).trans inf_le_left).trans D.sourceOrbit_component_normalizes
  have hRU : R ≤ normalizer (U : Set G) := (localResidual_le L U).trans inf_le_right
  have hfR (x : R) (v : Additive W) :
      F (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
        m22OuterCodeRepresentation (fR x).val (F v) := by
    let l : L := ⟨x,(localResidual_le L U x.property).1⟩
    rw [hF]
    apply congrArg (fun g : MathieuCode.m22PairStabilizer => m22OuterCodeRepresentation g (F v))
    change c * a (W.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) * c⁻¹ = _
    have ha : a (W.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) =
        m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l)) := haval l
    rw [ha]
    exact (hval (inclusion (localResidual_le L U) x)).symm
  let j : L →* MathieuCode.m22PairStabilizer := m22ToPairStabilizer.comp
    (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom)
  let q : L →* MathieuCode.m22PairStabilizer := (MulAut.conj c).toMonoidHom.comp j
  have hj : j.range = m22ToPairStabilizer.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective),←MonoidHom.range_eq_map]
  have hqr : q.range = m22ToPairStabilizer.range := by
    let : m22ToPairStabilizer.range.Normal := M22ChapterH.Quintet.inner_normal
    have hn' : c ∈ normalizer (m22ToPairStabilizer.range : Set MathieuCode.m22PairStabilizer) :=
      by rw [normalizer_eq_top]; trivial
    rw [MonoidHom.range_comp,hj]
    exact mem_normalizer_iff_map_conj_eq.mp hn'
  have hqF (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        m22OuterCodeRepresentation (q l) (F (Additive.ofMul w)) := by
    change F (automizerRepresentation W
      (W.normalizerMonoidHom.rangeRestrict (inclusion D.sourceOrbit_component_normalizes l))
      (Additive.ofMul w)) = _
    rw [hF]
    apply congrArg (fun g : MathieuCode.m22PairStabilizer =>
      m22OuterCodeRepresentation g (F (Additive.ofMul w)))
    change c * a (W.normalizerMonoidHom.rangeRestrict
      (inclusion D.sourceOrbit_component_normalizes l)) * c⁻¹ = _
    rw [haval l]
    rfl
  have hfull := Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer.marked_normalizer_residual_range
    W L U D.sourceOrbit_component_normalizes inf_le_left q hqr.ge F hqF
    (fun w => hU' (Additive.ofMul w)) f hval
  let q22 : L →* M22 := (m22PairStabilizerEquivAut c).toMonoidHom.comp
    (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom)
  have hq22 (l : L) : m22ToPairStabilizer (q22 l) = q l := by
    apply Subtype.ext
    exact m22PairStabilizerEquivAut_apply c (d.componentEquiv (D.orbitComponentHom l))
  have hq22sur : Function.Surjective q22 :=
    (m22PairStabilizerEquivAut c).surjective.comp
      (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective)
  have hq22ker : q22.ker = D.orbitComponentHom.ker :=
    (MonoidHom.ker_comp_of_injective _ _ (m22PairStabilizerEquivAut c).injective).trans
      (MonoidHom.ker_comp_of_injective _ _ d.componentEquiv.injective)
  refine ⟨f,hfk,marked_m22_section_residual W B U R inf_le_left hRV hRU F fR hfR hU' hB
    r hrsur hrc hrval,hfull,p,q22,F,(MulAut.conj c).injective.comp hinj,hq22sur,hq22ker,
    hF,hmark0,?_,?_⟩
  · intro l
    rw [hq22]
    change c * m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l)) * c⁻¹ =
      c * a (W.normalizerMonoidHom.rangeRestrict (inclusion D.sourceOrbit_component_normalizes l)) * c⁻¹
    exact congrArg (fun b => c * b * c⁻¹) (haval l).symm
  · intro n
    rw [hq22]
    exact hval n

set_option backward.isDefEq.respectTransparency true in
/-- Mark the literal B/U on any original degree-one quintet pair.
The full N_L(U) covering kernel is retained, separately from the residual two-core. -/
theorem sourceOrbit_m22_code_five_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hA : offenderNormalizer D.sourceOrbit i.val⁻¹ =
      D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)
    (hAT : offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T)
    (hfix : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hfour : rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) = 4)
    (hfive : rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)) = 5) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
    let B := D.sourceOrbit ⊓ I.pCoreIn 2
    let N := L ⊓ normalizer (U : Set G)
    let R := localResidual L U
    ∃ f : N →* M22Quintet.Q,
      f.ker = D.orbitComponentHom.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
      M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) := by
  obtain ⟨f,hk,hs,_⟩ := D.sourceOrbit_m22_code_five_section_full h d s hA hAT hfix hfour hfive
  exact ⟨f,hk,hs⟩

/-- The five-dimensional action belongs to the same original quasisimple
containing-component pair, with all its earlier normalization clauses. -/
theorem sourceOrbit_m22_code_five_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      (∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G)) ∧
      ∃ f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* M22Quintet.Q,
        f.ker = D.orbitComponentHom.ker.comap
          (inclusion (show (L ⊓ normalizer (U : Set G) : Subgroup G) ≤ L from inf_le_left)) ∧
        M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) := by
  have hex := @sourceOrbit_m22_code_component_pair G _ _ T L V D h hmany hV hnon d H hH
  rcases hex with ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hR,hcomm,hRI,hRP,hK⟩
  have hexs := @sourceOrbit_m22_code_five_section G _ _ T L V D h.toHypothesis1221 d H I i S s hA hAT hfix hfour hfive
  rcases hexs with ⟨f,hfk,hsection⟩
  exact ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,f,hfk,hsection⟩

/-- The unchanged pair has its full product quotient and diagonal A5 action
on the original ten-dimensional P/U, using the original inclusion and conjugator. -/
theorem sourceOrbit_m22_code_product_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      (∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G)) ∧
      ∃ f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* M22Quintet.Q,
        f.ker = D.orbitComponentHom.ker.comap
          (inclusion (show (L ⊓ normalizer (U : Set G) : Subgroup G) ≤ L from inf_le_left)) ∧
        M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) ∧
        M22CodePairProductAction R I D.sourceOrbit U ∧
        M22CodePairAction R I D.sourceOrbit U i (f.comp (inclusion (localResidual_le L U))) := by
  have hex := @sourceOrbit_m22_code_five_pair G _ _ T L V D h hmany hV hnon d H hH
  rcases hex with ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,f,hfk,hsection⟩
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  let R := localResidual L U
  have hsection' := hsection
  rcases hsection' with ⟨hRB,hRU,hBU,r,eB,hrsur,hrc,hrval,hact,hkernel,hdim⟩
  have hcommI : ⁅R,I⁆ ≤ R.pCoreIn 2 :=
    (commutator_mono le_rfl hcent).trans hcomm
  have hr := hfive
  rw [hA] at hr
  have hprod := selected_m22_code_full_product_action s hfix hcent hr hfour
    hRI hRU hcommI hRB hBU hkernel
  have hpair := selected_m22_code_pair_action s hprod hsection hcommI
  exact ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
