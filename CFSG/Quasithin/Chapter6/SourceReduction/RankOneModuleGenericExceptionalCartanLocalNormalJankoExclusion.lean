module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJankoOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryModule

/-!
# Excluding the original normal J₁ containing-component row

The original residual lies in the same normal containing component and
escapes the original left normalizer. Baumann control therefore forces the
component outside the Baumann normalizer. If it moves omega, its reduced
omega commutator has precisely the component's two-core as action kernel.
The actual Thompson action then satisfies B.5.1 on its literal offender
subgroup; none of that theorem's native actors has the order of J₁.
Thus the component centralizes omega, contradicting the original seven-part
movement proved in the companion module.

The concluding sieve retains every earlier exclusion and removes J₁ using
its actual two-core quotient isomorphism and relative component status.
Other containing-component rows and the inverted-cubic sieve remain open.
Source: Aschbacher--Smith 5.1.13, printed p.637, with B.2.7 and B.5.1
(`refs/quasithin.pdf`). The Thompson argument supplies the terminal faithful
module exclusion without assuming an FSU witness or quotient injection.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

private theorem two_power_bound {E : Type*} (hE : Nat.card E = 175560)
    {k : ℕ} (h : 2 ^ k ∣ Nat.card E) : k ≤ 3 := by
  by_contra hk
  have hd : 16 ∣ Nat.card E := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans h
  rw [hE] at hd
  norm_num at hd

private theorem no_linearTwo {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = Nat.card E := (Nat.card_congr e.toEquiv).symm
  rw [Atlas.card_sl_two,F.card_eq] at hc
  have hd := two_power_bound hE (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  rw [hE] at hc
  interval_cases hn : F.degree <;> norm_num [hn] at hc

private theorem no_linearThree {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = Nat.card E := (Nat.card_congr e.toEquiv).symm
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  have hp := F.degree_pos
  have hn : F.degree ≤ 1 := by omega
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq] at hc
  rw [hE] at hc
  interval_cases hd : F.degree
  norm_num [hd] at hc

private theorem no_symplectic {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  omega

private theorem no_g2 {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (F : BinaryField) (hF : 1 < F.degree) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hE hd
  omega

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem no_binaryLinear {E : Type*} [Group E] (hE : Nat.card E = 175560)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;>
    norm_num [Fin.prod_univ_succ] at hc <;> omega

private theorem no_other_alternating {E : Type*} [Group E] (hE : Nat.card E = 175560)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm
  rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] at hc <;>
    norm_num [Nat.factorial] at hc <;> omega

private theorem no_symplecticTwo {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (e : E ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) : False := by
  have hb := Nat.card_le_card_of_injective
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
  rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two,
    ← Nat.card_congr e.toEquiv] at hb
  omega

private theorem no_g2Two {E : Type*} [Group E] (hE : Nat.card E = 175560)
    (e : E ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hh := (Nat.card_congr e.toEquiv).symm
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
  omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

/-- No actor in the exact B.4.2 table has the order of J₁. -/
private theorem no_janko_irreducible_case
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (hc : Nat.card C = 175560) (hz : center C = ⊥) :
    False := by
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F hd _ a _ => exact (no_symplectic hc F hd a.groupEquiv).elim
  | symplecticTwo a _ => exact (no_symplecticTwo hc a.subgroupEquiv).elim
  | g2 F hd _ a _ _ => exact (no_g2 hc F hd a.groupEquiv).elim
  | g2Two a _ _ => exact (no_g2Two hc a.subgroupEquiv).elim
  | symmetric n hn a _ _ =>
    rcases hn with rfl | rfl
    · exact (no_other_alternating hc (Or.inl rfl) a.subgroupEquiv).elim
    · exact no_other_alternating hc (Or.inr (Or.inr (Or.inl rfl))) a.subgroupEquiv
  | alternatingSix _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ e _ _ _ => exact no_other_alternating hc (Or.inr (Or.inr (Or.inl rfl))) e
  | tripleSix _ a _ =>
    have hh := Nat.card_congr a.centerEquiv.toEquiv
    rw [hz,Subgroup.card_bot] at hh
    norm_num at hh
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.groupEquiv).elim
  | symmetricEight _ a _ => exact (no_other_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

private theorem no_janko_source_conclusion
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : Nat.card C = 175560) (hz : center C = ⊥) : False := by
  cases c.clause_one with
  | irreducible _ _ _ hs _ => exact no_janko_irreducible_case _ hs hc hz
  | doubleThree F _ a _ _ => exact no_linearThree hc F a.groupEquiv
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact no_binaryLinear hc hd a.groupEquiv
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact no_binaryLinear hc hd a.groupEquiv

open Stellmacher ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G]

private theorem marked_center {E : Type*} [Group E]
    (e : E ≃* Janko1.Model) : center E = ⊥ := by
  let : IsSimpleGroup E := e.isSimpleGroup
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  exact (inferInstance : (center E).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp he))

private theorem marked_quasisimple {E : Type*} [Group E]
    (e : E ≃* Janko1.Model) : IsQuasisimple E := by
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  exact { toIsPerfect := inferInstance
          simple := ((QuotientGroup.quotientMulEquivOfEq (marked_center e)).trans
            (QuotientGroup.quotientBot.trans e)).isSimpleGroup }

private theorem thompson_moves
    {T : Sylow 2 G} {K : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Janko1.Model)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hout : ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localOmegaModule T K : Set G) := by
  intro hj
  let M := K ⊔ (T : Subgroup G)
  let U := localOmegaModule T K
  let := Chapter1.mem_L_isPerfect hK
  let := marked_quasisimple e
  let := hU.2.1
  have hr := LocalOmega.reduced_internal hU
  have hmove : ⁅U,K⁆ ≠ ⊥ := fun hz => hne (commutator_eq_bot_of_iterated_eq_bot _ K hz)
  have hUT : U ≤ (T : Subgroup G) :=
    (reduced_le_core hU).trans ((pCoreIn_le_sylow M (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have he : ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (M.pCoreIn 2) := by
    rw [ChapterB.lemma_B_2_3_5 (T : Subgroup G) U hUT hj,
      Chapter5.RankOneBaumannSource.reduced_sylow_centralizer hn hU.1 hr
        (marked_center e) hmove]
  apply hout
  rw [he]
  exact (show K ≤ M from le_sup_left).trans
    ((M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))).trans
      (normalizer_le_normalizer_baumann _))

/-- A normalized J₁ local component escaping the original
Baumann normalizer centralizes the actual Sylow omega-center. -/
theorem normal_janko_centralizes_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Janko1.Model)
    (hout : ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    K ≤ omegaCentralizer T := by
  by_contra hnon
  have hU := LocalOmega.module_reduced T K (hG.evenCharacteristic T) hK hn
  have hne := LocalOmega.module_ne_bot T K hnon
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let B := K.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal hU
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let eqv := (QuotientGroup.congr (pCore 2 B) (pCore 2 K)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)))).trans e
  let := marked_quasisimple eqv
  have hgen : B ⊔ (S : Subgroup M) = ⊤ := by
    change K.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤
    rw [←subgroupOf_sup (show K ≤ M from le_sup_left) le_sup_right,subgroupOf_self]
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hSm]
  have hj : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hc
    apply thompson_moves hK hn e hU hne hout
    rw [←hjmap]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg M.subtype (hc hx ⟨y,hU.1 hy⟩ hy)
  have hsq : IsSQTK KnownSimple.IsKnownSimple M := by
    let R := M.pCoreIn 2
    let N := normalizer (R : Set G)
    have hMN : M ≤ N := M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
    have hN : IsTwoLocal N := ⟨R,hK.2.2,isPGroup_pCoreIn 2 M,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hMN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (M.subgroupOf N))
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro he
    have he' := congrArg (map M.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hU.1,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),Subgroup.map_bot] at he'
    rw [LocalOmega.full_movement (hG.evenCharacteristic T) hK hn] at he'
    exact hne he'
  let a := reducedQuasisimpleImageEquiv U B hr (marked_center eqv) hm
  let : IsQuasisimple (B.map (actionMk U)) := IsQuasisimple.of_mulEquiv a
  have hBN := component_le_offenderSubgroup S B U hgen hr.quotient_pCore_eq_bot hj
  let b := a.trans (subgroupOfEquivOfLe hBN).symm
  obtain ⟨c⟩ := quasisimple_source_conclusion_of_thompson_movement hsq S B U hK.1 hgen
    hr.quotient_pCore_eq_bot hj
  apply no_janko_source_conclusion _ c
  · rw [←Nat.card_congr b.toEquiv,Nat.card_congr eqv.toEquiv,
      Janko1.card_model]
  · exact marked_center (b.symm.trans eqv)


/-- The original normal J₁ containing component is impossible. Its seven-part
moves omega, while the faithful Thompson action forces it to centralize omega. -/
theorem normal_janko_excluded
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hC : C.IsCComponent)
    (hRC : (residual H).subgroupOf Y ≤ C) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  let X := C.map Y.subtype
  have hXY : X ≤ Y := map_subtype_le C
  have hc : (X.subgroupOf Y).IsCComponent := by
    change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hnormal : (X.subgroupOf Y).Normal := by
    change (C.map Y.subtype |>.comap Y.subtype).Normal
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using (inferInstance : C.Normal)
  have hn : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (hH.1.1.2.trans hY.2).trans ((normal_subgroupOf_iff_le_normalizer hXY).mp hnormal)
  have hJY : X ⊔ (T : Subgroup G) ≤ Y := sup_le hXY (hH.1.1.2.trans hY.2)
  have hX : X ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hc.subgroupOf_of_le le_sup_left hJY,⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro hz
      exact hY.1 (bot_unique
        ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right hJY).trans_eq hz))
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRX : residual H ≤ X := by
    rw [←map_subgroupOf_eq_of_le hRY]
    exact map_mono hRC
  have hout : ¬ X ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
    intro hx
    exact residual_not_le T H _ hH.1.1.2 h.sylow_normalizes hH.1.2
      (hRX.trans (hx.trans h.baumann_normalizer_le))
  let a := C.equivMapOfInjective Y.subtype Y.subtype_injective
  let eqv := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans e
  exact normal_janko_moves_omega h hH hgen c hY hescape C hRC e
    (normal_janko_centralizes_omega h.qtke hX hn eqv hout)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original normal-container sieve retains its complete input and
excludes the normal J₁ row, retaining every earlier source alternative. -/
theorem localCartan_escape_seed_noJanko_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn⟩ :=
    localCartan_escape_seed_normalContainer_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,?_⟩
  let := hCn
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hRX : residual H ≤ C.map Y.subtype := by
    rw [←hR]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC
      (hH.1.1.2.trans (hY.2.trans hYn))
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  exact LocalSieve.normal_janko_excluded h hH hgen c hY hescape C hC hRC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
