module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreDuality
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl

/-!
# Six point-residual chief factors in the extraspecial branch

Relative normality of L₁ places U inside O₂(L₁). The three-subgroup
lemma and the original plane movement show that O₂(L₁) moves U.
Irreducibility of U/V₁ then makes the radical of the central commutator
pairing exactly V₁, identifying O₂(L₁)/C_{O₂(L₁)}(U) with the dual
six-space. These are literal conjugation sections with their exact kernels.

An actual order-three subgroup of L₁ maps onto L₁* and acts without
fixed points on both sections. Each contributes three to its cubic length;
the sections are ordered because U is abelian. The original L₁/O₂(L₁)
has order three, so this yields at least six noncentral two-chief factors
in a complete chief series of L₁. The original Heisenberg application
uses earlier 14.7.10 to deduce N_G(Baum(R₁)) ≤ N_G(L).

The genuine earlier Structural1222, Theorem12213 and 14.7.10 implications
remain explicit. Their existing source producers retain these obligations,
with 14.7.10 owned by qt-d-14710-baumann and final discharge at
qt-d-14775-source. No
recognition datum, chief count, duality or point-normality premise is
assumed by that application. The point-central chief intervals and the
remaining extraspecial exclusion are still open.

Source: Aschbacher–Smith, 14.5.21(1), 14.7.16(1),(7), and the use of
14.7.16(7) in 14.7.21, printed pp.1019,1048–1050.
-/

public noncomputable section

open Subgroup Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem pointCore_full_core_normalized : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
  F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))

omit [Finite G] in
private theorem pointCore_point_centralizes : F.Vi 1 ≤ centralizer (F.H : Set G) := by
  apply le_centralizer_iff.mp
  exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))

omit [Finite G] in
private theorem pointCore_irreducible_centralizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F.H W) [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (N : Subgroup G) (hNH : N ≤ F.H) (hN : F.H ≤ normalizer (N : Set G))
    (hmove : ¬ N ≤ centralizer (F.U : Set G)) :
    F.U ⊓ centralizer (N : Set G) = F.Vi 1 := by
  have hZ : F.Vi 1 ≤ F.U ⊓ centralizer (N : Set G) :=
    le_inf s.kernel_le (pointCore_point_centralizes.trans (centralizer_le hNH))
  apply (s.eq_kernel_or_section _ hZ inf_le_left
    ((le_inf s.normalized (hN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  have hUC : F.U ≤ centralizer (N : Set G) := he ▸ inf_le_right
  exact hmove (le_centralizer_iff.mp hUC)

/-- The point-residual two-core moves U under relative point normality. -/
theorem point_core_moves_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ (F.Li L 1).pCoreIn 2 ≤ centralizer (F.U : Set G) := by
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hcent
  have hcomm : ⁅F.H.pCoreIn 2,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right))
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (hln))
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp
        ((show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right).trans pointCore_full_core_normalized)
  have h₁ : ⁅⁅F.U,F.H.pCoreIn 2⁆,F.Li L 1⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm F.U]
    exact (section_core_commutator_le_point h s).trans
      (pointCore_point_centralizes.trans (centralizer_le ((F.Li_le L 1).trans inf_le_right)))
  have h₂ : ⁅⁅F.H.pCoreIn 2,F.Li L 1⁆,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcent)
  have he := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [commutator_comm (F.Li L 1),commutator_U_point_of_normal h hn] at he
  exact plane_moved_of_point_normal h structural hn
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))

/-- The point-residual core has the same pairing radical as the full H-core. -/
theorem extraspecial_point_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer ((F.Li L 1).pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  exact pointCore_irreducible_centralizer ρ s _
    ((pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right))
    (hln.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1))))
    (point_core_moves_of_point_normal h hab structural
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp))

/-- The original span lies in the intrinsic two-core of the point residual. -/
theorem span_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) : F.U ≤ (F.Li L 1).pCoreIn 2 := by
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUK : F.U ≤ F.Li L 1 := by
    rw [←commutator_U_point_of_normal h hn]
    exact le_normalizer_iff_commutator_le_right.mp
      (s.section_le.trans (hln))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U) hUK
    ((show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right).trans s.normalized)

private theorem pointCore_pairing_of_radical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hNQ : N ≤ F.H.pCoreIn 2)
    (hUN : F.U ≤ N) (hN : F.H ≤ normalizer (N : Set G))
    (hc : F.U ⊓ centralizer (N : Set G) = F.Vi 1) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H N (N ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : N) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ₀,⟨s₀⟩⟩ := exists_section F
  obtain ⟨ρ,sU,sN,hpair,_⟩ := BinaryConjugationSection.exists_central_duality
    F.H N F.U (F.Vi 1) (hNQ.trans (pCoreIn_le 2 F.H)) s₀.section_le hN s₀.normalized
    (s₀.kernel_le.trans hUN) pointCore_point_centralizes
    ((commutator_mono hNQ le_rfl).trans (section_core_commutator_le_point h s₀))
    (by simpa using F.card 1 (by decide))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ :=
    { sU with kernel_le := s₀.kernel_le
              kernel_eq := sU.kernel_eq.trans (congrArg (fun C => C.subgroupOf F.U) hc) }
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  exact ⟨_,inferInstance,inferInstance,ρ,s,sN,hd,
    extraspecial_section_irreducible h hab structural previous hex hcard hexp s,hpair⟩

/-- The literal point-core quotient is the dual of U/V₁, with its commutator pairing. -/
theorem extraspecial_point_core_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H ((F.Li L 1).pCoreIn 2)
        ((F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : (F.Li L 1).pCoreIn 2) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hln : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  exact pointCore_pairing_of_radical h hab structural previous hex hcard hexp _
    (pCoreIn_mono_of_normalizes ((F.Li_le L 1).trans inf_le_right) hln)
    (span_le_point_core h hab hn)
    (hln.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1))))
    (extraspecial_point_core_centralizer h hab structural previous hex hcard hexp)

/-- Six noncentral two-chief factors occur in the original point residual. -/
theorem extraspecial_point_six_chief_factors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ∃ t : ChiefSeries (F.Li L 1), t.head = ⊥ ∧ t.last = ⊤ ∧
      6 ≤ t.noncentralTwoCount := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hquot := pointResidual_core_quotient_card (F := F) h structural
  have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
    simpa only [index_eq_card, hquot] using
      (pCore 2 (F.Li L 1)).index_dvd_card
  obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime (G := F.Li L 1) 3 (n := 1)
    (by simpa using hdiv)
  have hA3 : Nat.card A = 3 := by simpa using hA
  let C := A.map (F.Li L 1).subtype
  have hC3 : Nat.card C = 3 := by
    rw [card_map_of_injective (F.Li L 1).subtype_injective,hA3]
  have hCL : C ≤ F.Li L 1 := map_subtype_le _
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hCH : C ≤ F.H := hCL.trans hLH
  have hC : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC3)
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ :=
    extraspecial_point_core_duality h hab structural previous hex hcard hexp
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let f : C →* HStar F.H := (starMap F).comp (inclusion hCH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((starMap F).ker.comap (inclusion hCH))
    rw [show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hCH)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (hk.disjoint_of_coprime (hC.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)).le_bot)
  have hrange : f.range = star F (F.Li L 1) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨c,rfl⟩
      exact mem_map_of_mem (starMap F) (hCL c.property)
    · have hrCard : Nat.card f.range = Nat.card C :=
        (Nat.card_congr (Equiv.ofInjective f hf)).symm
      rw [hrCard, pointResidual_star_card_of_normal h structural hn,hC3]
  obtain ⟨σ,hσ⟩ := exists_star_representation h sU
  obtain ⟨z,_,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn sU σ hσ
  let τ : Representation (ZMod 2) C X := ρ.comp (inclusion hCH)
  have hz : z ∈ f.range := by
    rw [hrange,←hgen]
    exact mem_zpowers z
  obtain ⟨c,hc⟩ := hz
  have hfix : τ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply (Submodule.mem_bot _).mpr
    apply hfree v
    rw [←hc]
    change (σ.comp (starMap F)) (inclusion hCH c) v = v
    rw [hσ]
    exact hv c
  have hindex : BinaryFixedPoints.fixedIndex τ = 64 := by
    have hh := BinaryFixedPoints.fixedIndex_mul_card τ
    rw [hfix,Nat.card_unique,mul_one] at hh
    rw [hh,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    rfl
  let : IsCyclic C := isCyclic_of_prime_card hC3
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α := C)
  have hdual : BinaryFixedPoints.fixedIndex (ρ.dual.comp (inclusion hCH)) = 64 := by
    change BinaryFixedPoints.fixedIndex τ.dual = 64
    rw [BinaryFixedPoints.fixedIndex_dual τ c hc,hindex]
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hlow : sectionCubicLength C (F.Vi 1) F.U = 3 := by
    rw [sU.sectionCubicLength_eq_fixedIndex C hCH hC (IsElementaryAbelian.isPGroup 2 F.U),hindex]
    norm_num
  have hupp : sectionCubicLength C
      ((F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ((F.Li L 1).pCoreIn 2) = 3 := by
    rw [sN.sectionCubicLength_eq_fixedIndex C hCH hC (isPGroup_pCoreIn 2 _),hdual]
    norm_num
  have hUC : F.U ≤ (F.Li L 1).pCoreIn 2 ⊓ centralizer (F.U : Set G) :=
    le_inf (span_le_point_core h hab hn) F.U.le_centralizer
  have hm := conjugationCubicLength_mono C hUC
  have hlen : 6 ≤ conjugationCubicLength C ((F.Li L 1).pCoreIn 2) := by
    unfold sectionCubicLength at hlow hupp
    omega
  obtain ⟨t,ht0,ht1⟩ := exists_chiefSeries (⊥ : NormalNode (F.Li L 1)) ⊤ bot_le
  refine ⟨t,ht0,ht1,?_⟩
  rw [CubicComparison.count_of_core_quotient_card_three hquot A hA3 t ht0 ht1]
  rw [←CubicComparison.length_map_injective (F.Li L 1).subtype
    (F.Li L 1).subtype_injective A (pCore 2 (F.Li L 1))]
  exact hlen

/-- Source 14.7.16(7), applied to the literal Heisenberg residual. -/
theorem extraspecial_baumann_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨s,hs0,hs1,hcount⟩ :=
    extraspecial_point_six_chief_factors h hab structural previous hex hcard hexp
  rcases earlier G T L V F d h hab with hsmall | hnormal
  · have hb := hsmall s hs0 hs1
    omega
  · exact hnormal

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
