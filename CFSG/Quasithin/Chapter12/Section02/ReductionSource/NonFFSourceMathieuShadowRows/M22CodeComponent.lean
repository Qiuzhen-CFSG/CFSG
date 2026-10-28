module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFourSpace
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeRadicalGeometry
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeRadicalSection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraPlacement
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraCenter
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Equivalences
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
-- Reuse the original relative containing-component construction.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component

/-!
# The containing component of the original M22-code four-space

The original natural A5 residual lies in a normal C-component K of N_G(U).
For each nonquasisimple A.3.6 alternative its actual Xi radical centralizes
U and escapes the original N_G(L). An elementary radical gives an H-star
Sylow join. Reselecting there preserves U by rank-five uniqueness; the
component-invariant section has contradictory dimension bounds ten and 24.

Every remaining radical is extraspecial. Original two-core escape proves
its Sylow join is in H-star. B.6.8 places its actual Sylow center in N_G(L),
and the full quintet automizer shows that this odd center fixes the original
module. Original odd-normalizer control contradicts escape of that same
Sylow subgroup. Full A.3.6 exhaustiveness now gives K/O2(K) quasisimple.

The final theorem applies this to the same original selected pair. It also
proves [L_U,C_G(U)] <= O2(L_U) and normalization of the original I and O2(I),
with the original Sylow and containing-component two-core retained.
The preceding full normalizer covering kernel and maps are unchanged.
The remaining 8.2.8--13 argument and unconditional M24-cocode selection are
not asserted here.

Source: Aschbacher--Smith 8.2.7, 8.2.8(2) and the opening normalization step
of 8.2.8(4), printed pp.717--718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.Normalizer
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem m22_fourSpace_local {U K : Subgroup G} [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hUne : U ≠ ⊥)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent) :
    K ∈ Chapter1.L G (T : Subgroup G) := by
  refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
  · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
  · exact ne_bot_of_le_ne_bot hUne
      (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
        (hUV.trans (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
        (sup_le hKU hTU))

private theorem fitting_quotient_not_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hf : generalizedFitting Q = fittingSubgroup Q) : ¬ IsQuasisimple Q := by
  intro hq
  let := hq
  have ht : fittingSubgroup Q = ⊤ := hf.symm.trans generalizedFitting_eq_top_of_quasisimple
  let e := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center Q))
  exact Group.IsPerfect.not_isSolvable Q
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- Any nonquasisimple radical at the same four-space lies in the actual
Xi-family, escapes the original M, and centralizes the unchanged U. -/
theorem sourceOrbit_m22_code_radical_data
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {U K : Subgroup G} [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hu : rank U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : localResidual L U ≤ K)
    (hR : Nonempty ((localResidual L U ⧸ pCore 2 (localResidual L U)) ≃* alternatingGroup (Fin 5)))
    (hmodel : A36Natural (XiQuotient K) ∨ A36Nilpotent (XiQuotient K))
    (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    3 < p ∧ XiOddQuotient p (XiQuotient (XiP p K)) ∧
      XiMember (T : Subgroup G) (XiP p K) ∧
      ¬ XiP p K ≤ normalizer (L : Set G) ∧ XiP p K ≤ centralizer (U : Set G) := by
  have hUne : U ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hu; omega
  have hlocal := D.m22_fourSpace_local hUV hUne hTU hKU hK
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hn := fitting_quotient_not_quasisimple (hmodel.elim (fun hh => hh.1) (fun hh => hh.1))
  have hp := (Chapter1.RadicalStructure.radical_core hmodel hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hq := (XiP_oddQuotient_of_A36 hA36 hlocal hQ hn ho hd).2
  have hXi : XiMember (T : Subgroup G) (XiP p K) :=
    ⟨XiP_isPPerfect p K,XiP_invariant p hTK,XiP_join_mem_H p hlocal,
      ⟨p,Fact.out,ho,hq⟩,RadicalActions.XiP_irreducible_of_A36 hA36 hlocal hQ hn hTK ho hd⟩
  let R := localResidual L U
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  have hTR := normalizes_localResidual L U T D.sylow_normalizes_component hTU
  have hMR := normalizes_localResidual L U
    (normalizer (L : Set G) ⊓ normalizer (U : Set G)) inf_le_left inf_le_right
  have hout := radical_not_le_relative_normalizer hA36 hlocal hQ hTK hTR hRK hKU hMR
    hn ho hd hXi
  exact ⟨hp,hq,hXi,hout,xi_radical_centralizes_four_space hXi hTU ((XiP_le p K).trans hKU) hu hp hq⟩

/-- The elementary radical branch is impossible on the original M22-code
orbit. Pair reselection has the identical fixed four-space. -/
theorem sourceOrbit_m22_code_elementary_radical_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {A K : Subgroup G} [IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A)]
    (hAT : A ≤ T) (hfive : rank (inducedAutomizer D.sourceOrbit A) = 5)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hKU : K ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ≤ K)
    (hR : Nonempty ((localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ⧸
      pCore 2 (localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)))) ≃* alternatingGroup (Fin 5)))
    (hmodel : A36Natural (XiQuotient K) ∨ A36Nilpotent (XiQuotient K))
    (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    ¬ IsElementaryAbelian p (XiQuotient (XiP p K)) := by
  intro hel
  let := hel
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨hp,hq,hXi,hout,_⟩ := D.sourceOrbit_m22_code_radical_data h.toHypothesis1221
    (show U ≤ D.sourceOrbit from inf_le_left) hu hTU hKU hK hTK hRK hR hmodel p hd
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hqcard : Nat.card (XiQuotient (XiP p K)) = p^2 := by
    rcases hq with he | ⟨hex,hcard,_⟩
    · exact he.2
    · let := hex
      have hh := IsExtraspecial.center_order_p p (XiQuotient (XiP p K))
      rw [Subgroup.center_eq_top,card_top,hcard] at hh
      nlinarith [pow_pos (Fact.out : p.Prime).pos 2,(Fact.out : p.Prime).two_le]
  have hH := elementary_radical_join_HStar (p := p) T hXi D.sylow_normalizes_component hout
  obtain ⟨I,i,S,s,hw,hr,hOff,hA,hAT',hfix,hker,hcent,hfive',hfour,hUT,hTU',_,a,hinj,hE,c,hc⟩ :=
    D.sourceOrbit_m22_code_quintet_pair h hmany hV hnon d hH
  let A' := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U' := D.sourceOrbit ⊓ centralizer (A' : Set G)
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A') :=
    offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  have heq : U = U' := (Chapter8.MathieuShadowRows.m22_code_fixed_eq
    D.sourceOrbit T A A' T.isPGroup' hAT hAT'
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right a hinj hfive hfive').2
  have hUcard : Nat.card U' = 16 := by
    obtain ⟨n,hn⟩ := ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le
      (show U' ≤ D.sourceOrbit from inf_le_left)).exists_card_eq
    change rank U' = 4 at hfour
    rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hfour
    simpa [hfour] using hn
  have hVcard : Nat.card D.sourceOrbit = 1024 := by
    change Nat.card (Additive D.sourceOrbit) = 1024
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv).finrank_eq,finrank_m22Code]
    decide
  have hUne : U ≠ ⊥ := by intro hz; change rank U = 4 at hu; rw [hz,Representation.BinaryOffender.rank_bot] at hu; omega
  have hlocal := D.m22_fourSpace_local (show U ≤ D.sourceOrbit from inf_le_left) hUne hTU hKU hK
  have hKU' : K ≤ normalizer (U' : Set G) := heq ▸ hKU
  exact Chapter8.MathieuShadowRows.selected_one_elementary_radical_exclusion s
    (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1 hH
    D.sourceOrbit_weakClosure_setup (h.simpleQTKE.evenCharacteristic T)
    hlocal hTK hKU' hTU' hfix hcent hUcard hVcard p hp hXi rfl hqcard hmodel hd

/-- At this original fixed four-space only extraspecial radical quotients
can remain. Both elementary A.3.6 alternatives have been excluded. -/
theorem sourceOrbit_m22_code_component_radicals
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {A K : Subgroup G} [IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A)]
    (hAT : A ≤ T) (hfive : rank (inducedAutomizer D.sourceOrbit A) = 5)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hKU : K ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ≤ K)
    (hR : Nonempty ((localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ⧸
      pCore 2 (localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)))) ≃* alternatingGroup (Fin 5)))
 :
    ¬ A36Natural (XiQuotient K) ∧
      (A36Nilpotent (XiQuotient K) → ∀ (p : ℕ) (_ : Fact p.Prime),
        p ∣ Nat.card (fittingSubgroup (XiQuotient K)) →
        LocalModels.OddExtraspecialThree p (pCore p (XiQuotient K)) ∧
        IsExtraspecial p (XiQuotient (XiP p K)) ∧
        Nat.card (XiQuotient (XiP p K)) = p^3 ∧
        Monoid.exponent (XiQuotient (XiP p K)) = p) := by
  constructor
  · intro hnat
    obtain ⟨hf,p,hp,hp3,ha⟩ := hnat
    let : Fact p.Prime := ⟨hp⟩
    have hnat : A36Natural (XiQuotient K) := ⟨hf,p,hp,hp3,ha⟩
    obtain ⟨_,hc⟩ := Chapter1.RadicalStructure.natural_elementary ha
    have hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K)) := by
      rw [←hf,hc]
      exact dvd_pow_self p (by decide)
    obtain ⟨_,he,_⟩ := Chapter1.RadicalStructure.natural_core hnat hd
    let := he
    have ho : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
    have ht : omega (pCore p (XiQuotient K)) (p := p) 1 = ⊤ :=
      Chapter1.RadicalStructure.omega_top (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (pCore p (XiQuotient K))))
    let eq := (xiPQuotientEquivOmega ho K).trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
    exact D.sourceOrbit_m22_code_elementary_radical_exclusion h hmany hV hnon d
      hAT hfive hu hTU hKU hK hTK hRK hR (Or.inl hnat) p hd
      (IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective)
  · intro hnil p hp hd
    let := hp
    exact nilpotent_core_extraspecial_of_not_elementary K hnil p hd
      (D.sourceOrbit_m22_code_elementary_radical_exclusion h hmany hV hnon d
        hAT hfive hu hTU hKU hK hTK hRK hR (Or.inr hnil) p hd)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.Normalizer
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- An odd subgroup of the original M fixing the quintet four-space fixes
the whole original module. The full automizer action is used. -/
theorem sourceOrbit_m22_code_odd_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {A : Subgroup G} [IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A)]
    (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hfive : rank (inducedAutomizer D.sourceOrbit A) = 5)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (Z : Subgroup G) (hZ : Odd (Nat.card Z))
    (hZM : Z ≤ normalizer (L : Set G))
    (hZU : Z ≤ centralizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G)) :
    Z ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  let B := inducedAutomizer D.sourceOrbit A
  let : IsElementaryAbelian 2 (B.map a) := IsElementaryAbelian.map _
  obtain ⟨c,hc⟩ := NormalizedShadowRows.M22CodeQuintet.quintet_marking (B.map a)
    ((rank_map_injective a ha B).trans hfive)
  have hUne : D.sourceOrbit ⊓ centralizer (A : Set G) ≠ ⊥ := by
    intro he
    rw [he,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hZN : Z ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf hZM hZU).trans
      ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
        hUne (show D.sourceOrbit ⊓ centralizer (A : Set G) ≤ D.sourceOrbit from inf_le_left))
  exact Chapter8.MathieuShadowRows.m22_code_odd_centralizer D.sourceOrbit A Z hAN
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) a ha hE c hc hZ hZN hZU

/-- The extraspecial radical is impossible: its actual Sylow center lies
in M and fixes V, while its normalizer escapes M. -/
theorem sourceOrbit_m22_code_extraspecial_radical_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {A K : Subgroup G} [IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A)]
    (hAT : A ≤ T) (hfive : rank (inducedAutomizer D.sourceOrbit A) = 5)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hKU : K ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ≤ K)
    (hR : Nonempty ((localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ⧸
      pCore 2 (localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)))) ≃* alternatingGroup (Fin 5)))
    (p : ℕ) [Fact p.Prime]
    (hnil : A36Nilpotent (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K)))
    (hx : IsExtraspecial p (XiQuotient (XiP p K)))
    (hc : Nat.card (XiQuotient (XiP p K)) = p^3) : False := by
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let X := XiP p K
  let H := X ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  obtain ⟨hp,hq,hXi,hout,hXU⟩ := D.sourceOrbit_m22_code_radical_data h.toHypothesis1221
    (show U ≤ D.sourceOrbit from inf_le_left) hu hTU hKU hK hTK hRK hR (Or.inr hnil) p hd
  have hUne : U ≠ ⊥ := by intro hz; change rank U = 4 at hu; rw [hz,Representation.BinaryOffender.rank_bot] at hu; omega
  have hlocal := D.m22_fourSpace_local (show U ≤ D.sourceOrbit from inf_le_left) hUne hTU hKU hK
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hTR := normalizes_localResidual L U T D.sylow_normalizes_component hTU
  have hns : ¬ Group.IsSolvable R := by
    intro hh
    let := hh
    exact Group.IsPerfect.not_isSolvable (R ⧸ pCore 2 R) inferInstance
  have hcomm := RadicalActions.XiP_commutator_eq_of_nonsolvable_subgroup_of_A36
    hA36 hlocal hQ (nilpotent_not_quasisimple hnil) hTK hTR hRK hns ho hd
  let := hx
  have hH := extraspecial_radical_join_HStar T hXi
    (hRK.trans (XiP_invariant p K.le_normalizer))
    (((localResidual_le L U).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
    hcomm hout D.sourceOrbit_weakClosure_setup.le_sylow D.sourceOrbit_weakClosure_setup.normalizes
    (fun J hJ => D.sourceOrbit_m22_code_not_le_parabolic_core h hmany hV hnon d hJ) ho hc
  let : Group.IsSolvable X := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable H := Group.isSolvable_sup_of_normalizes _ _ hXi.invariant
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  let Y := (P : Subgroup X).map X.subtype
  let Z := (center Y).map Y.subtype
  let e := hXi.ambientSylowQuotientEquiv ho hq P
  let : IsExtraspecial p Y := IsExtraspecial.of_mulEquiv e.symm hx
  have hYM : ¬ Y ≤ normalizer (L : Set G) := by
    intro hh
    apply hout
    rw [←hXi.sylow_sup hq P]
    have hcore := hXi.pCoreIn_le_of_isSylowIn
      (show IsSylowIn 2 (T : Subgroup G) H from
        ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩)
    exact sup_le (hcore.trans D.sylow_normalizes_component) hh
  have hYU : Y ≤ centralizer (U : Set G) := (map_subtype_le _).trans hXU
  obtain ⟨hZcard,_,hne,hZU,_,hescape⟩ := extraspecial_supplement_center_escape (p := p) hYU hYM
  have hZM : Z ≤ normalizer (L : Set G) := extraspecial_center_le_of_solvable_parabolic
    (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1
    hsol ((map_subtype_le (P : Subgroup X)).trans le_sup_left) ho
  have hZo : Odd (Nat.card Z) := hZcard.symm ▸ ho
  have hZV := D.sourceOrbit_m22_code_odd_centralizer h hmany hV hnon d
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) hfive hu Z hZo hZM hZU
  have hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent := by
    have hz : center D.orbitComponent = ⊥ := by
      have hh := FixedElementary.map_center d.componentEquiv
      rw [m22_center_eq_bot] at hh
      exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
    exact Or.inr (Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).trans d.componentEquiv⟩)
  exact hescape (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon Z hne (le_inf hZM hZV) hZo)

/-- Source 8.2.7 at the unchanged M22-code four-space. Full A.3.6
exhaustiveness and all radical exclusions are discharged here. -/
theorem sourceOrbit_m22_code_quasisimple_at_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {A K : Subgroup G} [IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A)]
    (hAT : A ≤ T) (hfive : rank (inducedAutomizer D.sourceOrbit A) = 5)
    (hu : rank (D.sourceOrbit ⊓ centralizer (A : Set G)) = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hKU : K ≤ normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G))).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hRK : localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ≤ K)
    (hR : Nonempty ((localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)) ⧸
      pCore 2 (localResidual L (D.sourceOrbit ⊓ centralizer (A : Set G)))) ≃* alternatingGroup (Fin 5)))
 :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by intro hz; change rank U = 4 at hu; rw [hz,Representation.BinaryOffender.rank_bot] at hu; omega
  have hlocal := D.m22_fourSpace_local (show U ≤ D.sourceOrbit from inf_le_left) hUne hTU hKU hK
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let X := Chapter1.radicalLocalImage (T : Subgroup G) K
  let ex : XiQuotient K ≃* X := Chapter1.radicalLocalQuotientEquiv hlocal
  let := pCore_isNilpotent (p := 2) (G := (K ⊔ (T : Subgroup G) : Subgroup G))
  have hX : X.IsCComponent := hlocal.1.map_quotient _
  have ha := proposition_1_2_1_four_earlier_conclusion hA36 hQ hlocal.1
  obtain ⟨hnat,hcores⟩ := D.sourceOrbit_m22_code_component_radicals h hmany hV hnon d
    hAT hfive hu hTU hKU hK hTK hRK hR
  by_contra hnot
  have hnotX : ¬ IsQuasisimple X := fun hx => hnot (hx.of_mulEquiv ex.symm)
  rcases Chapter1.RadicalStructure.nonsimple_radical ha hnotX with hna | hni
  · exact hnat (hna.of_mulEquiv ex.symm)
  have hnil := hni.of_mulEquiv ex.symm
  let : Nontrivial X := (nontrivial_iff_ne_bot _).mpr hX.ne_bot
  let : Nontrivial (XiQuotient K) := ex.symm.injective.nontrivial
  have hfit : Nat.card (fittingSubgroup (XiQuotient K)) ≠ 1 := by
    intro hc
    have hg : generalizedFitting (XiQuotient K) = ⊥ := hnil.1.trans (card_eq_one.mp hc)
    have hh := Theory.GroupTheory.centralizer_generalizedFitting_le (XiQuotient K)
    have hbot : centralizer ((⊥ : Subgroup (XiQuotient K)) : Set (XiQuotient K)) = ⊤ := by
      ext g
      simp [mem_centralizer_iff]
    rw [hg,hbot] at hh
    exact top_ne_bot (le_antisymm hh bot_le)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hfit
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,hx,hc,_⟩ := hcores hnil p inferInstance hd
  exact D.sourceOrbit_m22_code_extraspecial_radical_exclusion h hmany hV hnon d
    hAT hfive hu hTU hKU hK hTK hRK hR p hnil hd hx hc

/-- The same original pair has a normal containing component with
quasisimple two-core quotient. Its residual centralizes C_G(U) modulo its
two-core and normalizes the original pair and pair core (8.2.7--8). -/
theorem sourceOrbit_m22_code_component_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5)) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I,i,S,s,hw,hr,hOff,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,
    hlocal,hchar,hcomponent,⟨e⟩,a,c,f,E,r,ha,hE,hc,hp,hfk,hval,hrsur,hrc,hrk,hrval,hract⟩ :=
    D.sourceOrbit_m22_code_fourSpace_normalizer_pair h hmany hV hnon d hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A) :=
    offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hfour
    rw [hz,Representation.BinaryOffender.rank_bot] at hfour
    omega
  obtain ⟨K,hKU,hK,hRK,hNK⟩ := D.fixed_overcomponent h.toHypothesis1221 U
    inf_le_left hUne hTU hcomponent
  have hquasi := D.sourceOrbit_m22_code_quasisimple_at_actor h hmany hV hnon d
    hAT hfive hfour hTU hKU hK (hTU.trans hNK) hRK ⟨e⟩
  let := hquasi
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKU).toMonoidHom) (subgroupOfEquivOfLe hKU).surjective
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hmove : ¬ R ≤ centralizer (U : Set G) := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨g,hg⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨x,rfl⟩ := hrsur g
    intro hh
    apply hg
    exact show x ∈ r.ker from hrk.symm ▸ hh x.property
  have hcomm := localResidual_centralizer_commutator L K U (T : Subgroup G)
    hRK hKU hNK hmove hQT D.sylow_normalizes_component hTU
  obtain ⟨hpair,hcore⟩ := local_factor_normalizes_pair_and_core L K U I D.sourceOrbit
    (T : Subgroup G) i.val i.property s.generate hcent hNK hQT
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes hcomm
  exact ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,⟨e⟩,hcomm,
    le_sup_left.trans hpair,le_sup_left.trans hcore,K,hKU,hK,hRK,hNK,hquasi,hQT,hpair,hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
