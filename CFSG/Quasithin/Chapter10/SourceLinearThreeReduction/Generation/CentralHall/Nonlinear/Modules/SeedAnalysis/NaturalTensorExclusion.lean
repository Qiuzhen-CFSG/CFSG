module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorOrdinaryField
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.SymplecticFour.DerivedSplitTorus
-- Internal proof access identifies the named minimal-parabolic core with core(M).
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Excluding the original natural-tensor Hall branch

The literal tensor alternative gives |B| = 2^n - 1 and n(H) >= n-1,
with n >= 3. A marked model's cyclic torus and the proved upper bound
n(H) <= f force f = n by Hall divisibility. The full unitary or rank-two
torus is then too large, with the projective scalar kernel retained.
For an exchanged component, two disjoint commuting tori inside the same
original maximal image give the squared torus order, also too large.
The remaining normal PSL₂ and Suzuki rows are excluded by comparing
ordinary field action with inverse field action on the same original B.

The final dispatcher uses the actual original source component catalogue;
no numerical equality across a solvable quotient or extra model premise
is assumed. Its consumer is the unchanged central Hall source contract.
Source: Aschbacher--Smith, 9.2.7, pp.731--732, and the centralizing-Z
branch of 10.2.3, p.745; the component catalogue is E.2.2, pp.215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem odd_dvd_hall_card {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (hB : IsHallSubgroup OddHall.oddPrimes B)
    {d : ℕ} (ho : Odd d) (hd : d ∣ Nat.card A) : d ∣ Nat.card B := by
  have hc : Nat.Coprime d B.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpi
    apply hB.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi
    intro he
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (he ▸ hpd))
  apply hc.dvd_of_dvd_mul_right
  rwa [B.card_mul_index]

private theorem square_card_dvd_of_disjoint_commuting
    {Q : Type*} [Group Q] [Finite Q] (A A' M : Subgroup Q)
    (hdisj : Disjoint A A') (hcomm : A ≤ centralizer (A' : Set Q))
    (hAM : A ≤ M) (hA'M : A' ≤ M) (hcard : Nat.card A' = Nat.card A) :
    (Nat.card A)^2 ∣ Nat.card M := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A A' hdisj hcomm
  have he : Nat.card (A ⊔ A' : Subgroup Q) = (Nat.card A)^2 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hcard,pow_two]
  rw [←he]
  exact card_dvd_of_le (sup_le hAM hA'M)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)

include c

/-- Every odd divisor of a marked Borel order divides the original Hall order,
through the literal source quotient and original overlap. -/
theorem original_marked_odd_card_dvd (K : Subgroup H)
    {Y : Type*} [Group Y] (U : Subgroup Y)
    (hm : ModelBorelPair (D.maximalLocal.subgroupOf H) K U)
    {d : ℕ} (ho : Odd d) (hd : d ∣ Nat.card U) : d ∣ Nat.card B := by
  let M := D.maximalLocal.subgroupOf H
  obtain ⟨e,he⟩ := hm
  let q := QuotientGroup.mk' (sourceKernel M)
  let r := (componentBorelEquiv U e he).toMonoidHom.comp (q.subgroupMap (M ⊓ K))
  have hr : Function.Surjective r :=
    (componentBorelEquiv U e he).surjective.comp (q.subgroupMap_surjective (M ⊓ K))
  have hdM := hd.trans ((card_dvd_of_surjective r hr).trans (card_dvd_of_le (show M ⊓ K ≤ M from inf_le_left)))
  have hh := odd_dvd_hall_card (B.subgroupOf M) c.hall ho hdM
  rwa [Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv] at hh

/-- The full unitary torus, retaining its scalar kernel, is too large for
the prescribed Hall order in tensor degree at least three. -/
theorem unitary_model_false_of_hall_order (K : Subgroup H) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card B = 2^n-1)
    (hm : UnitaryModel (D.maximalLocal.subgroupOf H) K n) : False := by
  obtain ⟨F,hF,hfin,hchar,J,hJ,_,hFcard,hconj,_hfixed,hmodel⟩ := hm
  let := hF
  let := hfin
  let := hchar
  let P := BenderSuzuki.External.hermitianTorusPSU J hJ
  have h8 : 8 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have ho : Odd (Nat.card P.range) := by
    apply Odd.of_dvd_nat _ (card_range_dvd P)
    rw [Nat.card_units,hFcard]
    exact Nat.Even.sub_odd (by nlinarith)
      ((even_two.pow_of_ne_zero (by omega : n ≠ 0)).pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one
  have hd := original_marked_odd_card_dvd D c K (unitaryBorel J hJ) hmodel ho
    (card_dvd_of_le (show P.range ≤ unitaryBorel J hJ from le_sup_right))
  have hle : Nat.card P.range ≤ 2^n-1 := Nat.le_of_dvd (by omega) (hcard ▸ hd)
  have he := P.ker.card_mul_index
  rw [index_ker,Nat.card_units,hFcard,
    BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projective_ker_card J hJ hFcard hconj] at he
  have hg : Nat.gcd (2^n+1) 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
  have hu := Nat.mul_le_mul hg hle
  have hsub : 2^n-1+1 = 2^n := by omega
  have hsq : 64 ≤ (2^n)^2 := by simpa only [pow_two] using Nat.mul_le_mul h8 h8
  have hsub2 : (2^n)^2-1+1 = (2^n)^2 := by omega
  have h7 : 7 ≤ 2^n-1 := by omega
  nlinarith

/-- The projective rank-two torus retains its cubic scalar kernel. Its
order still exceeds the original Hall order in tensor degree at least three. -/
theorem linear_three_model_false_of_hall_order (K : Subgroup H) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card B = 2^n-1)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair (D.maximalLocal.subgroupOf H) K (Matrix.PSL3.LinearThree.borel F)) :
    False := by
  let U := Matrix.PSL3.CartanActions.torus F
  have ho : Odd (Nat.card U) := by
    apply Odd.of_dvd_nat _ (card_range_dvd (Matrix.PSL3.CartanActions.torusMap F))
    rw [Nat.card_prod]
    exact (Matrix.PSL3.CartanActions.BorelQuotient.units_odd F hF).mul
      (Matrix.PSL3.CartanActions.BorelQuotient.units_odd F hF)
  have hd := original_marked_odd_card_dvd D c K (Matrix.PSL3.LinearThree.borel F) hm ho
    (card_dvd_of_le (Matrix.PSL3.CartanActions.torus_le_borel F))
  have h8 : 8 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hle : Nat.card U ≤ 2^n-1 := Nat.le_of_dvd (by omega) (hcard ▸ hd)
  have he := Matrix.PSL3.CartanActions.BorelQuotient.card_torus_mul_scalar F
  rw [hF] at he
  have hg : Nat.gcd 3 (2^n-1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hu := Nat.mul_le_mul hle hg
  change Nat.card U * _ = _ at he
  have h7 : 7 ≤ 2^n-1 := by omega
  nlinarith

/-- The full split torus is too large even in the literal derived Sp₄ Borel. -/
theorem symplectic_model_false_of_hall_order (K : Subgroup H) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card B = 2^n-1)
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair (D.maximalLocal.subgroupOf H) K (MarkedModels.sp4DerivedBorel F)) :
    False := by
  have ho : Odd (Nat.card (Fˣ × Fˣ)) := by
    rw [Nat.card_prod]
    exact (Matrix.PSL3.CartanActions.BorelQuotient.units_odd F hF).mul
      (Matrix.PSL3.CartanActions.BorelQuotient.units_odd F hF)
  have hd := original_marked_odd_card_dvd D c K (MarkedModels.sp4DerivedBorel F) hm ho
    (card_dvd_of_injective Theory.SpecificGroups.SymplecticFour.DerivedSplitTorus.embedding
      Theory.SpecificGroups.SymplecticFour.DerivedSplitTorus.embedding_injective)
  rw [Nat.card_prod,Nat.card_units,hF,hcard] at hd
  have h8 : 8 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hle := Nat.le_of_dvd (by omega : 0 < 2^n-1) hd
  have h7 : 7 ≤ 2^n-1 := by omega
  nlinarith

/-- The original unitary H-model is excluded by the full torus order,
using only its proved generation upper bound. -/
theorem original_hall_conclusion_of_unitary_model (K : Subgroup H) {f : ℕ}
    (hbound : generationParameter H ≤ f)
    (hm : UnitaryModel (D.maximalLocal.subgroupOf H) K f) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  rcases original_hall_conclusion_or_natural_tensor_inverse_field D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,_heq,_hseed,_hBR,_hcyc,hcard,_hexp,hlo,_rest⟩
  · exact hh
  · obtain ⟨A,hAM,_hAc,hAc⟩ := hm.cyclic
    have hfn := original_hall_source_degree D c hn hcard hlo hbound ⟨A,hAM,hAc⟩
    subst f
    exact (unitary_model_false_of_hall_order D c K hn hcard hm).elim

/-- Both actual rank-two H-models are excluded, retaining their projective
or derived-group conventions and the original Hall carrier. -/
theorem original_hall_conclusion_of_diagram_model (K : Subgroup H) {f : ℕ}
    (hbound : generationParameter H ≤ f)
    (hm : DiagramModel (D.maximalLocal.subgroupOf H) K
      (T.subtype c.hstar.1.1.2 : Subgroup H) f) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  rcases original_hall_conclusion_or_natural_tensor_inverse_field D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,_heq,_hseed,_hBR,_hcyc,hcard,_hexp,hlo,_rest⟩
  · exact hh
  · obtain ⟨A,hAM,_hAc,hAc⟩ := hm.cyclic
    have hfn := original_hall_source_degree D c hn hcard hlo hbound ⟨A,hAM,hAc⟩
    subst f
    rcases hm with ⟨F,hF,hfin,hchar,_hf,hFc,eH,hB,_⟩ | ⟨F,hF,hfin,hchar,_hf,hFc,eH,hB,_⟩
    · let := hF
      let := hfin
      exact (linear_three_model_false_of_hall_order D c K hn hcard F hFc ⟨eH,hB⟩).elim
    · let := hF
      let := hfin
      let := hchar
      exact (symplectic_model_false_of_hall_order D c K hn hcard F hFc ⟨eH,hB⟩).elim

/-- Every actual normal H-component now gives the original Hall conclusion,
with all model, numerical, quotient and action premises discharged. -/
theorem original_hall_conclusion_of_normal_source
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T.subtype c.hstar.1.1.2 : Subgroup H) = ⊤) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  let S := T.subtype c.hstar.1.1.2
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
  have hH := Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1
  have hM := source_hstar_parabolicMax_eq_overlap D c.hstar hP
  rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH S hP hs K hK hgen with
    h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one ChapterA.Section02.theoremA_knownSimple
      hH S hP hs K hK hgen h2 c.large).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one ChapterA.Section02.theoremA_knownSimple
        hH S hP hs K hK hgen hp ho (Or.inr huni.2) c.large).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact (normal_odd_three_false_of_parameter_gt_one ChapterA.Section02.theoremA_knownSimple
        hH S hP hs K hK hgen hp ho (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) c.large).elim
  · cases hb with
    | linear f hf hm => exact original_hall_conclusion_of_normal_linear_source D c hP K hK hgen hf hm
    | suzuki m hm he => exact original_hall_conclusion_of_normal_suzuki_source D c hP K hK hgen hm he
    | unitary f hf hm =>
      exact original_hall_conclusion_of_unitary_model D c K
        (normal_unitary_three_parameter_le ChapterA.Section02.theoremA_knownSimple hH S hP hs K hK hgen hf hm)
        (hM ▸ source_unitary_borel_model S hP hs K hK hgen hf hm)
  · obtain ⟨f,hf,hm⟩ := hl
    exact original_hall_conclusion_of_diagram_model D c K
      (normal_linear_three_parameter_le ChapterA.Section02.theoremA_knownSimple hH S hP hs K hK hgen (by omega) hm)
      (hM ▸ source_binary_linear_three_model S hP hs K hK hgen hf hm)
  · obtain ⟨f,hf,hm⟩ := hsp
    exact original_hall_conclusion_of_diagram_model D c K
      (normal_symplectic_parameter_le ChapterA.Section02.theoremA_knownSimple hH S hP hs K hK hgen hf hm)
      (hM ▸ source_binary_symplectic_model S hP hs K hK hgen hf hm)
  · exact ((Nat.not_le_of_gt c.large) (normal_binary_six_parameter_le S hP hs K hK hgen hbi)).elim

/-- In the paired source row, two actual commuting conjugates of a marked
odd torus contribute its squared order to the original Hall subgroup. -/
theorem original_paired_torus_square_dvd
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype c.hstar.1.1.2 : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {Y : Type*} [Group Y] (U : Subgroup Y)
    (hm : ModelBorelPair (ChapterB.minimalParabolicMax (T.subtype c.hstar.1.1.2) hP) K U)
    {A₀ : Type*} [Group A₀] [Finite A₀] (i : A₀ →* U) (hi : Function.Injective i)
    (ho : Odd (Nat.card A₀)) : (Nat.card A₀)^2 ∣ Nat.card B := by
  let S := T.subtype c.hstar.1.1.2
  let M := ChapterB.minimalParabolicMax S hP
  let J := ChapterB.minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let R := K.map q
  let M' := M.map q
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable S hP
  have hH := Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1
  have hstar := Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hH S hP hs
  have hR := Structure.source_component_simple_image S hP hs K hK hgen
  have hrad : solvableRadical (H ⧸ J) = ⊥ := by
    let e : (H ⧸ J) ≃* (H ⧸ solvableRadical H) := QuotientGroup.quotientMulEquivOfEq
      (ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hP hs)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_solvableRadical_equiv,solvableRadical_quotient_solvableRadical,Subgroup.map_bot]
  rcases Structure.component_normal_or_pair hstar.stronglyQuasithin S' hR.2.1 hR.2.2.2 with
    hh | ⟨t,hne,hR',hcomm,_⟩
  · exact (hn (cComponent_normal_of_quotient_normal hK J hh.1)).elim
  · let R' := R.map (MulAut.conj (t : H ⧸ J)).toMonoidHom
    have hdisj : Disjoint R R' :=
      (hK.map_quotient J).disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hrad hcomm
    obtain ⟨e,he⟩ := hm
    let O : Subgroup (H ⧸ J) := sourceImage M (M ⊓ K)
    let b : O ≃* U := componentBorelEquiv U e he
    let j : A₀ →* O := b.symm.toMonoidHom.comp i
    let k : A₀ →* (H ⧸ J) := O.subtype.comp j
    have hk : Function.Injective k := O.subtype_injective.comp (b.symm.injective.comp hi)
    let A := k.range
    let A' := A.map (MulAut.conj (t : H ⧸ J)).toMonoidHom
    have hAR : A ≤ R := by
      rintro _ ⟨a,rfl⟩
      exact map_mono (f := q) (show M ⊓ K ≤ K from inf_le_right) (j a).property
    have hAM : A ≤ M' := by
      rintro _ ⟨a,rfl⟩
      exact map_mono (f := q) (show M ⊓ K ≤ M from inf_le_left) (j a).property
    have hA'R' : A' ≤ R' := map_mono hAR
    have htM : (t : H ⧸ J) ∈ M' :=
      map_mono (f := q) (ChapterB.minimalParabolicMax_spec S hP).2 t.property
    have hA'M : A' ≤ M' := by
      rintro _ ⟨a,ha,rfl⟩
      exact M'.mul_mem (M'.mul_mem htM (hAM ha)) (M'.inv_mem htM)
    have hc : A ≤ centralizer (A' : Set (H ⧸ J)) := by
      intro a ha b hb
      exact (commutator_eq_bot_iff_le_centralizer.mp hcomm) (hAR ha) b (hA'R' hb)
    have hd' := square_card_dvd_of_disjoint_commuting A A' M'
      (hdisj.mono hAR hA'R') hc hAM hA'M
      (card_map_of_injective (MulAut.conj (t : H ⧸ J)).injective)
    have hAc : Nat.card A = Nat.card A₀ := (Nat.card_congr (MonoidHom.ofInjective hk).toEquiv).symm
    have hd : (Nat.card A₀)^2 ∣ Nat.card M := by
      rw [hAc] at hd'
      exact hd'.trans (card_map_dvd M q)
    have hM : M = D.maximalLocal.subgroupOf H := source_hstar_parabolicMax_eq_overlap D c.hstar hP
    have hh := odd_dvd_hall_card (B.subgroupOf M) (hM.symm ▸ c.hall) ho.pow hd
    rwa [Nat.card_congr (subgroupOfEquivOfLe (hM.symm ▸ c.hall_le)).toEquiv] at hh

/-- All actual paired H-models are incompatible with the natural tensor.
Their two tori retain both source components and the full quotient kernel. -/
theorem original_hall_conclusion_of_paired_source
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype c.hstar.1.1.2 : Subgroup H) = ⊤) (hnorm : ¬ K.Normal) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  let S := T.subtype c.hstar.1.1.2
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
  have hH := Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1
  have hM := source_hstar_parabolicMax_eq_overlap D c.hstar hP
  rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH S hP hs K hK hgen hnorm with
    ⟨f,hf,hm⟩ | ⟨p,hp,ho,hp7,hmodel⟩
  · have hmodel : (2 ≤ f ∧ ClassicalGroup.IsPSL
        (sourceImage (ChapterB.minimalParabolicMax S hP) K) 2 (2^f)) ∨
        ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
          (sourceImage (ChapterB.minimalParabolicMax S hP) K ≃*
            BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
      rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,e,_⟩ | ⟨m,hm,hf,e,_⟩
      · exact Or.inl ⟨hf,F,hF,hfin,hcard,⟨e⟩⟩
      · exact Or.inr ⟨m,by omega,hf,⟨e⟩⟩
    have hbound := paired_bender_parameter_le ChapterA.Section02.theoremA_knownSimple
      hH S hP hs K hK hgen hnorm hmodel
    rcases original_hall_conclusion_or_natural_tensor_inverse_field D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,_heq,_hseed,_hBR,_hcyc,hcard,_hexp,hlo,_rest⟩
    · exact hh
    · exfalso
      obtain ⟨A,hAM,_hAc,hAc⟩ := hm.cyclic
      have hfn := original_hall_source_degree D c hn hcard hlo hbound ⟨A,hM ▸ hAM,hAc⟩
      subst f
      have hd : (2^n-1)^2 ∣ Nat.card B := by
        rcases hm with ⟨F,hF,hfin,hchar,_,hFc,hmodel⟩ | ⟨m,hm,hf,hmodel⟩
        · let := hF
          let := hfin
          let := hchar
          have hh := original_paired_torus_square_dvd D c hP K hK hgen hnorm
            (BenderSuzuki.Converse.PBorel F) hmodel (Tori.psl2Torus (F := F))
            Tori.psl2Torus_injective (Matrix.PSL3.CartanActions.BorelQuotient.units_odd F hFc)
          simpa only [Nat.card_units,hFc] using hh
        · have hFc : Nat.card (GaloisField 2 (2*m+1)) = 2^n := by
            rw [GaloisField.card 2 (2*m+1) (by omega),hf]
          have hh := original_paired_torus_square_dvd D c hP K hK hgen hnorm
            (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m) hmodel (Tori.suzukiTorus m hm)
            (Tori.suzukiTorus_injective m hm)
            (Matrix.PSL3.CartanActions.BorelQuotient.units_odd (GaloisField 2 (2*m+1)) hFc)
          simpa only [Nat.card_units,hFc] using hh
      rw [hcard] at hd
      have h8 : 8 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      have hle := Nat.le_of_dvd (by omega : 0 < 2^n-1) hd
      have h7 : 7 ≤ 2^n-1 := by omega
      nlinarith
  · let : Fact p.Prime := ⟨hp⟩
    exact ((Nat.not_le_of_gt c.large) (paired_prime_parameter_le_one
      ChapterA.Section02.theoremA_knownSimple hH S hP hs K hK hgen hnorm (by omega) hmodel)).elim

/-- The original central Hall conclusion, with every source model excluded
in the remaining tensor branch and no new premise. -/
theorem original_hall_conclusion :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  obtain ⟨hP,_⟩ := source_hstar_cartan_data_of_generation_gt_one D c.hstar c.large
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,_hqs,hgen,_⟩ := Structure.source_original_component
    (Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1) (T.subtype c.hstar.1.1.2) hP hs
  by_cases hnorm : K.Normal
  · let := hnorm
    exact original_hall_conclusion_of_normal_source D c hP K hK hgen
  · exact original_hall_conclusion_of_paired_source D c hP K hK hgen hnorm

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
