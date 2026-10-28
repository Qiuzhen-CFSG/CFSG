module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Sieve
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.StarKernel
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductProjection
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricFourSolvable
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Simple component carriers in F.6.18 rows (2)–(9)

Row (2) is solvable, including every extension of the concrete Heisenberg
three-group by E₄. In row (3), perfectness puts the component in the literal
two-residual K × C₃. Projection away from C₃ identifies it with a component
of K, hence with K itself. The remaining linear and permutation rows have
a quasisimple whole group or an embedded quasisimple subgroup of index two,
which determines the component's actual carrier.

The triple alternating rows retain their center of order three. For a triple
symmetric row, simplicity makes the component inject into the permutation
quotient: its intersection with the solvable kernel is trivial. Its image
is the alternating subgroup. No classification of the row (2) extension
action or splitting of any index-two extension is asserted.

The final applications use F.6.11 and `star_isComponent_and_simple` on the
literal quotient I/O_{3′}(I), including the actual mixed setup of 15.4.18.
Selection of these source rows remains explicit. Lifting the original
component is performed by the parent ModelLifting module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18,
printed pp.309–310, and 15.4.18, pp.1162–1163. The imported linear-group
simplicity, perfectness and PGL₂ comparison retain their ATLAS attribution
and license.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.SmallRows
open FFBranch.ClassificationComparison
open GoldschmidtAlternatives

private theorem pslTwo_quasisimple (F : Type*) [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : IsQuasisimple PSL(2,F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  refine { toIsPerfect := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq (GorensteinWalter.psl2_center_eq_bot F)).trans
    QuotientGroup.quotientBot).isSimpleGroup

private theorem alternating_quasisimple {n : ℕ} (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  refine { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans
      QuotientGroup.quotientBot).isSimpleGroup

private theorem component_equiv_whole {D : Type*} [Group D] [IsQuasisimple D]
    {Q : Subgroup D} (hQ : IsComponent D Q) : Nonempty (Q ≃* D) := by
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have he := hQ.eq_of_le (show IsComponent D ⊤ from ⟨.top, inferInstance⟩) le_top
  exact ⟨(MulEquiv.subgroupCongr he).trans topEquiv⟩

private theorem component_equiv_indexTwo {D M : Type*} [Group D] [Group M]
    [IsQuasisimple M] {Q : Subgroup D} (hQ : IsComponent D Q)
    (i : M →* D) (hi : Function.Injective i) (hindex : i.range.index = 2) :
    Nonempty (Q ≃* M) := by
  let : i.range.Normal := normal_of_index_eq_two hindex
  let : IsQuasisimple i.range := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi)
  exact ⟨(MulEquiv.subgroupCongr (hQ.eq_of_index_two_quasisimple hindex)).trans
    (MonoidHom.ofInjective hi).symm⟩

private theorem symmetric_component {n : ℕ} (hn : 5 ≤ n)
    {Q : Subgroup (Equiv.Perm (Fin n))} (hQ : IsComponent _ Q) :
    Nonempty (Q ≃* alternatingGroup (Fin n)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := alternating_quasisimple hn
  exact ⟨MulEquiv.subgroupCongr
    (hQ.eq_of_index_two_quasisimple alternatingGroup.index_eq_two)⟩

private theorem simple_component_solvable_kernel {D H : Type*} [Group D] [Group H]
    {Q : Subgroup D} (hQ : IsComponent D Q) [IsSimpleGroup Q]
    (f : D →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    IsComponent H (Q.map f) ∧ Nonempty (Q ≃* Q.map f) := by
  let := hQ.2
  have hnot : ¬ Q ≤ f.ker := by
    intro hle
    let : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  have himage : Q.map f ≠ ⊥ := fun he => hnot ((map_eq_bot_iff Q).mp he)
  let g := f.comp Q.subtype
  have hi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker inferInstance).resolve_right
    intro ht
    apply hnot
    intro x hx
    have hxg : (⟨x, hx⟩ : Q) ∈ g.ker := by rw [ht]; trivial
    exact hxg
  refine ⟨(hQ.map_surjective f hf).resolve_left himage, ⟨?_⟩⟩
  exact MulEquiv.ofBijective (f.subgroupMap Q)
    ⟨fun x y he => hi (congrArg Subtype.val he), f.subgroupMap_surjective Q⟩

private theorem triple_symmetric_component {D : Type*} [Group D]
    {Q : Subgroup D} (hQ : IsComponent D Q) [IsSimpleGroup Q]
    {n : ℕ} (hn : 5 ≤ n) (h : TripleSymmetric D n) :
    Nonempty (Q ≃* alternatingGroup (Fin n)) := by
  obtain ⟨f, hf, ⟨ek⟩, _, _⟩ := h
  let : Group.IsSolvable f.ker :=
    Group.isSolvable_of_isSolvable_injective (f := ek.toMonoidHom) ek.injective
  obtain ⟨himage, ⟨e⟩⟩ := simple_component_solvable_kernel hQ f hf
  obtain ⟨e'⟩ := symmetric_component hn himage
  exact ⟨e.trans e'⟩

variable {D : Type*} [Group D] {A B Q : Subgroup D}

/-- Every group allowed by row (2) is solvable, with no restriction on the extension action. -/
theorem case2_solvable (h : Case2 D) : Group.IsSolvable D := by
  rcases h with he | he
  · obtain ⟨e⟩ := he
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable S3 := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨f, _, ⟨e⟩⟩ := he
    let : Group.IsNilpotent (HeisenbergPrime 3) :=
      (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).isNilpotent
    let : Group.IsSolvable f.ker :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

/-- A group in row (2) has no components, since a nontrivial perfect subgroup is not solvable. -/
theorem not_case2 (hQ : IsComponent D Q) (h : Case2 D) : False := by
  let := hQ.2
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  let := case2_solvable h
  exact Group.IsPerfect.not_isSolvable Q inferInstance

/-- The component in row (3) has the actual PSL₂(p) carrier of the factor K of O²(D). -/
theorem case3_model [Finite D] (hQ : IsComponent D Q) (h : Case3 A B) :
    IntrinsicComponentModel Q := by
  obtain ⟨p, K, C₀, hp, hm, hK, ⟨eC⟩, hsup, hd, hc, _⟩ := h
  obtain ⟨F, _, _, hF, ⟨eK⟩⟩ := hK
  let := pslTwo_quasisimple F (by omega)
  let := IsQuasisimple.of_mulEquiv eK.symm
  let := hQ.2
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hQR : Q ≤ K ⊔ C₀ := by
    rw [hsup]
    exact le_of_isPerfect_of_solvable_quotient Q (pResidual 2 D)
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K C₀ hd
    (fun k hk d hd => (hc ⟨k, hk⟩ ⟨d, hd⟩).eq.symm)
  let eR : ↥(K ⊔ C₀) ≃* C₀ × K := e.symm.trans MulEquiv.prodComm
  let : Group.IsSolvable C₀ :=
    Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
  obtain ⟨P, hP, ⟨eP⟩⟩ := IsComponent.equiv_component_of_solvable_prod _
    ((hQ.subgroupOf hQR).map_equiv eR)
  obtain ⟨ePK⟩ := component_equiv_whole hP
  let eQ : Q ≃* K := (subgroupOfEquivOfLe hQR).symm |>.trans
    (eR.subgroupMap (Q.subgroupOf (K ⊔ C₀))) |>.trans eP |>.trans ePK
  exact .linearTwo (hF ▸ Or.inl ⟨hp, hm⟩) (eQ.trans eK)

/-- Row (4) identifies the component with the whole PSL₂(p) group, retaining the prime congruence. -/
theorem case4_model (hQ : IsComponent D Q) (h : Case4 A B) :
    IntrinsicComponentModel Q := by
  obtain ⟨p, hp, hm, ⟨F, _, _, hF, ⟨e⟩⟩, _⟩ := h
  let := pslTwo_quasisimple F (by omega)
  let := IsQuasisimple.of_mulEquiv e.symm
  obtain ⟨eQ⟩ := component_equiv_whole hQ
  exact .linearTwo (hF ▸ Or.inl ⟨hp, hm⟩) (eQ.trans e)

/-- In row (5), the component is the actual index-two PSL₂ image inside PGL₂. -/
theorem case5_model (hQ : IsComponent D Q) (h : Case5 A B) :
    IntrinsicComponentModel Q := by
  obtain ⟨p, hp, hm, ⟨F, _, _, hF, ⟨e⟩⟩, _⟩ := h
  let := pslTwo_quasisimple F (by omega)
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), by decide, by simpa using hF⟩
  let i : PSL(2,F) →* D := e.symm.toMonoidHom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hi : Function.Injective i :=
    e.symm.injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hindex : i.range.index = 2 := by
    rw [MonoidHom.range_comp]
    exact (Subgroup.index_map_equiv _ e.symm).trans
      (GorensteinWalter.pgl2_psl2Range_index_eq_two F hpp)
  obtain ⟨eQ⟩ := component_equiv_indexTwo hQ i hi hindex
  exact .linearTwo (hF ▸ Or.inl ⟨hp, hm⟩) eQ

private theorem triple_alternating_model (hQ : IsComponent D Q)
    {n : ℕ} (hn : 5 ≤ n) (h : TripleAlternating D n) : IntrinsicComponentModel Q := by
  obtain ⟨hperf, ⟨ez⟩, ⟨e⟩⟩ := h
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsQuasisimple D := { toIsPerfect := hperf, simple := e.isSimpleGroup }
  obtain ⟨eQ⟩ := component_equiv_whole hQ
  apply IntrinsicComponentModel.tripleCover
  calc
    Nat.card (center Q) = Nat.card (center D) := Nat.card_congr (centerCongr eQ).toEquiv
    _ = Nat.card (C 3) := Nat.card_congr ez.toEquiv
    _ = 3 := by simp [C, Nat.card_eq_fintype_card]

/-- Both row (6) possibilities, including the triple cover and the restricted field degrees. -/
theorem case6_model (hQ : IsComponent D Q) (h : Case6 A B) :
    IntrinsicComponentModel Q := by
  rcases h.1 with ht | ⟨p, n, hp, hn, hn2, hm, F, _, _, hF, ⟨e⟩⟩
  · exact triple_alternating_model hQ (by decide) ht
  · let := pslTwo_quasisimple F (by omega)
    let := IsQuasisimple.of_mulEquiv e.symm
    obtain ⟨eQ⟩ := component_equiv_whole hQ
    exact .linearTwo (Or.inr (Or.inl ⟨p, n, hp, hn, hn2, hF, hF ▸ hm⟩)) (eQ.trans e)

/-- Both row (7) possibilities, retaining the alternating-seven triple cover. -/
theorem case7_model (hQ : IsComponent D Q) (h : Case7 A B) :
    IntrinsicComponentModel Q := by
  rcases h.1 with he | ht
  · obtain ⟨e⟩ := he
    let := alternating_quasisimple (by decide : 5 ≤ 7)
    let := IsQuasisimple.of_mulEquiv e.symm
    obtain ⟨eQ⟩ := component_equiv_whole hQ
    exact .alternatingSeven (eQ.trans e)
  · exact triple_alternating_model hQ (by decide) ht

/-- Row (8), with the full triple-symmetric or prescribed quadratic-field extension predicate. -/
theorem case8_model (hQ : IsComponent D Q) [IsSimpleGroup Q] (h : Case8 A B) :
    IntrinsicComponentModel Q := by
  rcases h.1 with ht | ⟨p, hp, hm, F, _, _, hF, _, _, i, _, hi, hindex, _⟩
  · obtain ⟨e⟩ := triple_symmetric_component hQ (by decide) ht
    exact .alternatingSix e
  · have hp3 : 3 ≤ p := by omega
    let := pslTwo_quasisimple F (by nlinarith)
    obtain ⟨eQ⟩ := component_equiv_indexTwo hQ i hi hindex
    exact .linearTwo (Or.inr (Or.inr ⟨p, hp, hm, hF⟩)) eQ

/-- A simple component in either symmetric-seven row has the actual alternating-seven carrier. -/
theorem case9_model (hQ : IsComponent D Q) [IsSimpleGroup Q] (h : Case9 A B) :
    IntrinsicComponentModel Q := by
  rcases h.1 with he | ht
  · obtain ⟨e⟩ := he
    obtain ⟨eQ⟩ := symmetric_component (by decide : 5 ≤ 7) (hQ.map_equiv e)
    exact .alternatingSeven ((e.subgroupMap Q).trans eQ)
  · obtain ⟨eQ⟩ := triple_symmetric_component hQ (by decide) ht
    exact .alternatingSeven eQ

/-- The complete source predicates for rows (2)–(9), in a fixed source labeling. -/
@[expose] def Selected (A B : Subgroup D) : Prop :=
  Case2 D ∨ Case3 A B ∨ Case4 A B ∨ Case5 A B ∨
    Case6 A B ∨ Case7 A B ∨ Case8 A B ∨ Case9 A B

/-- Extract an actual carrier for a simple component in any of rows (2)–(9).
The two-core assumption matches the star-quotient consumer; this extraction
in fact does not need it. No row is replaced by a generalized-Fitting label. -/
theorem model [Finite D] (hQ : IsComponent D Q) (hsimple : IsSimpleGroup Q)
    (_hcore : pCore 2 D = ⊥) (h : Selected A B) : IntrinsicComponentModel Q := by
  let := hsimple
  unfold Selected at h
  rcases h with h | h | h | h | h | h | h | h
  · exact (not_case2 hQ h).elim
  · exact case3_model hQ h
  · exact case4_model hQ h
  · exact case5_model hQ h
  · exact case6_model hQ h
  · exact case7_model hQ h
  · exact case8_model hQ h
  · exact case9_model hQ h

/-- F.6.11 and the literal star map produce the simple component to which
the selected F.6.18 rows apply. Both source labelings are allowed. -/
theorem star_model [Finite D] (h : ChapterF.IsGoldschmidtTriple A B)
    (L : Subgroup D) (hL : IsComponent D L) (hodd : pPrimeCore 2 D = ⊥)
    (hrows : Selected (threePrimeImage A) (threePrimeImage B) ∨
      Selected (threePrimeImage B) (threePrimeImage A)) :
    IntrinsicComponentModel (threePrimeImage L) := by
  have hs := star_isComponent_and_simple L hL hodd
    (f611Conclusion_of_goldschmidt h).core_solvable
  rcases hrows with hrows | hrows
  · exact model hs.1 hs.2 h.primeToThreeCore_quotient_twoCore_eq_bot hrows
  · exact model hs.1 hs.2 h.primeToThreeCore_quotient_twoCore_eq_bot hrows

open MixedLocal

/-- Application to the original mixed group in 15.4.18. The explicit row
selection is supplied by the F.6.18 case split; F.6.11 solvability and the
simple-component property of the actual quotient image are discharged here. -/
theorem mixed_star_model {G : Type*} [Group G] [Finite G]
    {K : GroupClass} (T : Sylow 2 G) {Y X M₂ : Subgroup G} {F : Bool → Subgroup G}
    (c : Configuration K T Y X M₂ F)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L)
    (hrows :
      let A := (firstGroup T Y F).subgroupOf (generated T Y F)
      let B := (secondGroup T F).subgroupOf (generated T Y F)
      Selected (threePrimeImage A) (threePrimeImage B) ∨
        Selected (threePrimeImage B) (threePrimeImage A)) :
    IntrinsicComponentModel (threePrimeImage L) :=
  star_model c.goldschmidt L hL hodd hrows

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.SmallRows
