module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeQuintetPair
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpaceCover
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original M22-code four-space normalizer

For the unchanged pair of 8.2.5, the original fixed subgroup U has rank four.
The full automizer coordinates identify it with the geometric quintet
four-space. The relative normalizer N_L(U) has the actual five-point action,
with the whole original component-map kernel retained. Its solvable residual
L_U acts naturally as A5 on the same U. Odd-rank transfer applied to the
original central cover L/O₂(L) removes the odd kernel only on this perfect
residual, proving C_{L_U}(U) = O₂(L_U).

The final application constructs these maps on the original selected pair,
proves L_U is a C-component of N_{N_G(L)}(U), and puts N_G(U) in characteristic
two using the original Sylow subgroup. These are the M22-code assertions of
8.2.6. The containing-component argument of 8.2.7 and the subsequent M22-code
exclusion and unconditional M24-cocode selection remain separate obligations.

Source: Aschbacher--Smith 8.2.5--6 and H.16.3(2,4), printed pp.717,403,
refs/quasithin.pdf. The full central-cover argument uses I.1.2, printed p.407.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
open Chapter7.NormalizedSource.MathieuShadowRows
open MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- The same original fixed four-space has the literal quintet normalizer action. -/
theorem sourceOrbit_m22_code_normalizer_of_quintet
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hfour : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer)
    (hE : ∀ b v, (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (automizerRepresentation D.sourceOrbit b v) = m22OuterCodeRepresentation (a b)
        ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) v))
    (c : MathieuCode.m22PairStabilizer)
    (hc : ((inducedAutomizer D.sourceOrbit A).map a).map
      (MulAut.conj c).toMonoidHom = M22Quintet.K) :
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let N := L ⊓ normalizer (U : Set G)
    ∃ (f : N →* M22Quintet.Q)
      (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5))),
      Function.Surjective (NaturalQuotient.q.comp f) ∧
      f.ker = D.orbitComponentHom.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
      (∀ l, (f l).val = c * m22ToPairStabilizer
        (d.componentEquiv (D.orbitComponentHom ⟨l,l.property.1⟩)) * c⁻¹) ∧
      (NaturalQuotient.q.comp f).ker = (centralizer (U : Set G)).subgroupOf N ∧
      ∀ (n : N) (u : U),
        (e (U.normalizerMonoidHom ⟨n,n.property.2⟩ u)).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 5) (NaturalQuotient.q (f n)) (e u).toAdd := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (A : Set G)
  let B := inducedAutomizer W A
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
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
  have hfix : (fixedSpace (automizerRepresentation W) B).map F.toLinearMap =
      fixedSpace m22OuterCodeRepresentation M22Quintet.K := by
    rw [fixedSpace_map_equivariant _ _ p F hF]
    change fixedSpace m22OuterCodeRepresentation (B.map ((MulAut.conj c).toMonoidHom.comp a)) = _
    rw [←map_map,hc]
  have hd : Module.finrank (ZMod 2) (fixedSpace m22OuterCodeRepresentation M22Quintet.K) = 4 := by
    rw [←hfix,LinearEquiv.finrank_map_eq]
    have hs := fixedCodim_add_finrank (automizerRepresentation W) B
    have hcod := fixedCodim_inducedAutomizer W A hAN
    have hsum := offender_corank_add (W := W) (A := U) (B := ⊥) bot_le inf_le_left
    have hsum' : rank W = subgroupCorank W U + rank U := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
    have hv := Chapter7.log_card_eq_finrank W
    change rank W = Module.finrank (ZMod 2) (Additive W) at hv
    change rank U = 4 at hfour
    change fixedCodim (automizerRepresentation W) B = subgroupCorank W U at hcod
    rw [hcod,←hv] at hs
    exact (Nat.add_left_cancel (hs.trans hsum')).trans hfour
  rw [NormalizedShadowRows.M22CodeFourSpace.fixed_eq_of_finrank hd] at hfix
  have hspace (w : W) : (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ M22Quintet.V4 := by
    rw [←hfix]
    constructor
    · intro hw
      exact ⟨Additive.ofMul w,(mem_fixedSpace_inducedAutomizer W A hAN _).mpr hw.2,rfl⟩
    · rintro ⟨v,hv,he⟩
      have hvw : v = Additive.ofMul w := F.injective he
      rw [hvw] at hv
      exact ⟨w.property,(mem_fixedSpace_inducedAutomizer W A hAN _).mp hv⟩
  let j : L →* MathieuCode.m22PairStabilizer := m22ToPairStabilizer.comp
    (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom)
  let q : L →* MathieuCode.m22PairStabilizer := (MulAut.conj c).toMonoidHom.comp j
  have hj : j.range = m22ToPairStabilizer.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective),←MonoidHom.range_eq_map]
  have hqr : m22ToPairStabilizer.range ≤ q.range := by
    let : m22ToPairStabilizer.range.Normal := M22ChapterH.Quintet.inner_normal
    have hn' : c ∈ normalizer (m22ToPairStabilizer.range : Set MathieuCode.m22PairStabilizer) :=
      by rw [normalizer_eq_top]; trivial
    rw [MonoidHom.range_comp,hj]
    have he : m22ToPairStabilizer.range.map (MulAut.conj c).toMonoidHom =
        m22ToPairStabilizer.range := mem_normalizer_iff_map_conj_eq.mp hn'
    exact he.symm.le
  have hqF (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        m22OuterCodeRepresentation (q l) (F (Additive.ofMul w)) := by
    have he := D.sourceOrbit_m22_component_coordinates m22CodeRepresentation
      m22OuterCodeRepresentation rfl d l (Additive.ofMul w)
    change m22OuterCodeRepresentation c (E (automizerRepresentation W
      (W.normalizerMonoidHom.rangeRestrict (inclusion D.sourceOrbit_component_normalizes l))
      (Additive.ofMul w))) = _
    rw [he]
    change m22OuterCodeRepresentation c
      (m22OuterCodeRepresentation (m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l)))
        (E (Additive.ofMul w))) = m22OuterCodeRepresentation (q l) (m22OuterCodeRepresentation c (E (Additive.ofMul w)))
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    change c * j l = (c * j l * c⁻¹) * c
    group
  have hqk : q.ker = D.orbitComponentHom.ker := by
    have hi : Function.Injective m22ToPairStabilizer := by
      intro x y he
      exact m22Embedding_injective (congrArg Subtype.val he)
    ext l
    change (MulAut.conj c) (m22ToPairStabilizer (d.componentEquiv (D.orbitComponentHom l))) = 1 ↔
      D.orbitComponentHom l = 1
    exact (MulAut.conj c).map_eq_one_iff.trans
      ((map_eq_one_iff m22ToPairStabilizer hi).trans d.componentEquiv.map_eq_one_iff)
  have hex := @M22CodeNormalizer.marked_normalizer_action G _ W L U _
    D.sourceOrbit_component_normalizes inf_le_left q hqr F hqF hspace
  rcases hex with ⟨f,e,hp,hk,hval,hpoint,_,ha⟩
  rw [hqk] at hk
  exact ⟨f,e,hp,hk,hval,hpoint,ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original perfect residual has natural A5 action and exactly its two-core as kernel. -/
theorem sourceOrbit_m22_code_fourSpace_residual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hfour : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer)
    (hE : ∀ b v, (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (automizerRepresentation D.sourceOrbit b v) = m22OuterCodeRepresentation (a b)
        ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) v))
    (c : MathieuCode.m22PairStabilizer)
    (hc : ((inducedAutomizer D.sourceOrbit A).map a).map
      (MulAut.conj c).toMonoidHom = M22Quintet.K) :
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let N := L ⊓ normalizer (U : Set G)
    let R := localResidual L U
    ∃ (f : N →* M22Quintet.Q)
      (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
      (r : R →* alternatingGroup (Fin 5)),
      Function.Surjective (NaturalQuotient.q.comp f) ∧
      f.ker = D.orbitComponentHom.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
      (∀ l, (f l).val = c * m22ToPairStabilizer
        (d.componentEquiv (D.orbitComponentHom ⟨l,l.property.1⟩)) * c⁻¹) ∧
      Function.Surjective r ∧ r.ker = pCore 2 R ∧
      r.ker = (centralizer (U : Set G)).subgroupOf R ∧
      (∀ x, (r x).val = NaturalQuotient.q (f (inclusion (localResidual_le L U) x))) ∧
      (∀ (x : R) (u : U),
        (e (U.normalizerMonoidHom ⟨x,(localResidual_le L U x.property).2⟩ u)).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 5) (r x).val (e u).toAdd) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5)) := by
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let N := L ⊓ normalizer (U : Set G)
  let R := localResidual L U
  have hex := @sourceOrbit_m22_code_normalizer_of_quintet G _ _ T L V D
    d A hAN hfour a hE c hc
  rcases hex with ⟨f,e,hp,hfk,hval,hpoint,ha⟩
  have hexr := @M22CodeNormalizer.residual_action G _ _ L U
    (NaturalQuotient.q.comp f) hp hpoint e ha
  rcases hexr with ⟨r,hr,hrk,hrval,hract⟩
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let j : R →* N := inclusion (localResidual_le L U)
  let jL : R →* L := inclusion ((localResidual_le L U).trans inf_le_left)
  let q : R →* (L ⧸ pCore 2 L) := (QuotientGroup.mk' (pCore 2 L)).comp jL
  have hq : IsPGroup 2 q.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let k := d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
  let cv : Covering (L ⧸ pCore 2 L) M22 := {
    toMonoidHom := k
    surjective := d.componentEquiv.surjective.comp (D.orbitComponentQuotientHom_surjective h) }
  let g := (m22ToPairStabilizer.comp k).comp q
  have hg (x : R) : c*g x*c⁻¹ = (f (j x)).val := (hval (j x)).symm
  have hg2 : IsPGroup 2 g.ker :=
    NormalizedShadowRows.M22CodeFourSpace.quintet_perfect_kernel_isTwo
      (PerfectCentralCovering.ofCovering cv) (pCore_quotient_pCore_eq_bot 2) q hq c
      (fun x => hg x ▸ (f (j x)).property)
  let fR := f.comp j
  have hfk2 : IsPGroup 2 fR.ker := by
    have he : fR.ker = g.ker := by
      ext x
      change f (j x) = 1 ↔ g x = 1
      rw [Subtype.ext_iff,←hg]
      exact (MulAut.conj c).map_eq_one_iff
    exact he.symm ▸ hg2
  have hp2 : IsPGroup 2 (NaturalQuotient.q.comp fR).ker := by
    change IsPGroup 2 (NaturalQuotient.q.ker.comap fR)
    rw [NaturalQuotient.q_ker_eq_partAction_ker,M22ChapterH.Quintet.partAction_ker]
    exact pCore_isPGroup.comap_of_ker_isPGroup fR hfk2
  have hr2 : IsPGroup 2 r.ker := by
    have he : r.ker = (NaturalQuotient.q.comp fR).ker := by
      ext x
      change r x = 1 ↔ NaturalQuotient.q (f (j x)) = 1
      rw [Subtype.ext_iff,hrval]
      rfl
    exact he.symm ▸ hp2
  have hbot : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 5))
        (N := pCore 2 (alternatingGroup (Fin 5))) with he | he
    · exact he
    · have hh : Nat.card (pCore 2 (alternatingGroup (Fin 5))) = 60 := by
        rw [he,card_top,nat_card_alternatingGroup,Nat.card_fin]
        decide
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))).exists_card_eq
      have hd : 3 ∣ 2^n := hn ▸ hh.symm ▸ (by decide : 3∣60)
      exact False.elim ((by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hd))
  have hrc : r.ker = pCore 2 R := by
    have hh := r.comap_pCore_of_ker_isPGroup hr hr2
    simpa only [hbot,MonoidHom.comap_bot] using hh
  exact ⟨f,e,r,hp,hfk,hval,hr,hrc,hrk,hrval,hract,
    ⟨(QuotientGroup.quotientMulEquivOfEq hrc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Source 8.2.6 on the unchanged original M22-code pair, with the full
normalizer kernel and literal A5 action retained. -/
theorem sourceOrbit_m22_code_fourSpace_normalizer_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let N := L ⊓ normalizer (U : Set G)
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧ globalR D.sourceOrbit = 6 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsTwoLocal (normalizer (U : Set G)) ∧ HasCharacteristicTwo (normalizer (U : Set G)) ∧
      (R.subgroupOf (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5)) ∧
      ∃ (a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer) (c : MathieuCode.m22PairStabilizer)
        (f : N →* M22Quintet.Q)
        (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
        (r : R →* alternatingGroup (Fin 5)),
        Function.Injective a ∧
        (∀ b v, (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
          (automizerRepresentation D.sourceOrbit b v) = m22OuterCodeRepresentation (a b)
            ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) v)) ∧
        ((inducedAutomizer D.sourceOrbit A).map a).map
          (MulAut.conj c).toMonoidHom = M22Quintet.K ∧
        Function.Surjective (NaturalQuotient.q.comp f) ∧
        f.ker = D.orbitComponentHom.ker.comap (inclusion (show N ≤ L from inf_le_left)) ∧
        (∀ l, (f l).val = c*m22ToPairStabilizer
          (d.componentEquiv (D.orbitComponentHom ⟨l,l.property.1⟩))*c⁻¹) ∧
        Function.Surjective r ∧ r.ker = pCore 2 R ∧
        r.ker = (centralizer (U : Set G)).subgroupOf R ∧
        (∀ x, (r x).val = NaturalQuotient.q (f (inclusion (localResidual_le L U) x))) ∧
        ∀ (x : R) (u : U),
          (e (U.normalizerMonoidHom ⟨x,(localResidual_le L U x.property).2⟩ u)).toAdd =
            BinaryPermutation.naturalRepresentation (Fin 5) (r x).val (e u).toAdd := by
  have hex := @sourceOrbit_m22_code_quintet_pair G _ _ T L V D h hmany hV hnon d H hH
  rcases hex with ⟨I,i,S,s,hw,hr,hOff,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,_,a,hinj,hE,c,hc⟩
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  have hexr := @sourceOrbit_m22_code_fourSpace_residual G _ _ T L V D
    h.toHypothesis1221 d A inf_le_right hfour a hE c hc
  rcases hexr with ⟨f,e,r,hp,hfk,hval,hrsur,hrc,hrk,hrval,hract,⟨b⟩⟩
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hfour
    rw [hz,Representation.BinaryOffender.rank_bot] at hfour
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hlocalOver : normalizer (U : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hlocal,hTU⟩
  have hchar : HasCharacteristicTwo (normalizer (U : Set G)) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h.simpleQTKE.evenCharacteristic T) hlocalOver)
  let M := normalizer (L : Set G) ⊓ normalizer (U : Set G)
  have hRM : R ≤ M := (localResidual_le L U).trans (inf_le_inf_right _ L.le_normalizer)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_localResidual L U M inf_le_left inf_le_right)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv b.symm
  have hperfect : IsPPerfect 2 R := by
    intro B hB hq
    let : B.Normal := hB
    by_contra hne
    let : Nontrivial (R ⧸ B) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (R ⧸ B) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective B)
    let : Group.IsNilpotent (R ⧸ B) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (R ⧸ B) inferInstance
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) (pCore_isPGroup (p := 2)) hperfect
  have htop : (⊤ : Subgroup (R.subgroupOf M)).IsCComponent := by
    simpa using ht.map_equiv (subgroupOfEquivOfLe hRM).symm
  have hcomponent : (R.subgroupOf M).IsCComponent := by
    simpa only [←MonoidHom.range_eq_map,range_subtype] using
      htop.map_subtype (inferInstance : (R.subgroupOf M).Normal).isSubnormal
  exact ⟨I,i,S,s,hw,hr,hOff,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hlocal,hchar,
    hcomponent,⟨b⟩,a,c,f,e,r,hinj,hE,hc,hp,hfk,hval,hrsur,hrc,hrk,hrval,hract⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
