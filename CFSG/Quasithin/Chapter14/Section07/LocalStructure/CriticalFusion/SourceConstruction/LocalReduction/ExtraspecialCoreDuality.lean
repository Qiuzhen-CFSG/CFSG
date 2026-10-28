module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointNormality
public import Theory.Representation.BinaryConjugationSection.CentralDuality
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer

/-!
# The original two-core duality in the extraspecial branch

Irreducibility of the literal U/V₁ section makes the radical of its
commutator pairing with O₂(H) exactly V₁. The residual core O₂(K) also
moves U: otherwise the three-subgroup lemma and U = [U,K] would force
the whole H-core to centralize U, contrary to the original plane movement.
Its pairing therefore has the same radical.

Both core-centralizer quotients have order 64. Their indices give
O₂(H) = O₂(K) C_H(U), and restriction of the full-core coordinate map
identifies both quotients with the same contragredient of U/V₁. Restricting
the functionals to the original seed V gives |O₂(K) : O₂(K) ∩ Q| = 4.
The final application starts with the actual Heisenberg isomorphism and
constructs all section actions, retaining the literal core inclusion and
every functional kernel. It uses no recognition datum or duality premise.

This proves source 14.7.20(1) and the numerical part of (4). The chief-factor
alternative, equality of the point and residual cores, remaining commutator
identification in (4), and the extraspecial exclusion still require proof.
Source: Aschbacher–Smith, 14.7.16(1), 14.7.20, printed pp.1048–1049.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem irreducible_of_comp {D A W : Type*} [Group D] [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (f : A →* D) [IsIrreducible (ρ.comp f)] :
    IsIrreducible ρ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let S' : Subrepresentation (ρ.comp f) :=
    ⟨S.toSubmodule,fun a _ hv => S.apply_mem_toSubmodule (f a) hv⟩
  rcases eq_bot_or_eq_top S' with he | he
  · left
    apply le_antisymm _ bot_le
    intro v hv
    exact (show v ∈ (⊥ : Subrepresentation (ρ.comp f)) from he ▸ hv)
  · right
    apply top_unique
    intro v _
    exact (show v ∈ S' from he ▸ (show v ∈ (⊤ : Subrepresentation (ρ.comp f)) from trivial))

omit [Finite G] in
private theorem core_normalized : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
  F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))

omit [Finite G] in
private theorem point_centralizes : F.Vi 1 ≤ centralizer (F.H : Set G) := by
  apply le_centralizer_iff.mp
  exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))

omit [Finite G] in
private theorem irreducible_centralizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) F.H W) [IsIrreducible ρ]
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (N : Subgroup G) (hNH : N ≤ F.H) (hN : F.H ≤ normalizer (N : Set G))
    (hmove : ¬ N ≤ centralizer (F.U : Set G)) :
    F.U ⊓ centralizer (N : Set G) = F.Vi 1 := by
  have hZ : F.Vi 1 ≤ F.U ⊓ centralizer (N : Set G) :=
    le_inf s.kernel_le (point_centralizes.trans (centralizer_le hNH))
  apply (s.eq_kernel_or_section _ hZ inf_le_left
    ((le_inf s.normalized (hN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  have hUC : F.U ≤ centralizer (N : Set G) := he ▸ inf_le_right
  exact hmove (le_centralizer_iff.mp hUC)

/-- The original H-action is irreducible in the extraspecial branch. -/
theorem extraspecial_section_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) : IsIrreducible ρ := by
  obtain ⟨σ,hσ,_,_,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let := hi
  let : IsIrreducible σ := irreducible_of_comp σ (pResidual 2 (HStar F.H)).subtype
  exact hσ ▸ ((irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mpr inferInstance)

/-- In the extraspecial branch the core commutator pairing has radical exactly the original point. -/
theorem extraspecial_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact irreducible_centralizer ρ s _ (pCoreIn_le 2 F.H) core_normalized
    (fun he => plane_moved_of_point_normal h structural hn
      (he.trans (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))))

omit [Finite G] in
private theorem residual_core_normalized :
    F.H ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
  (le_normalizer_embedded_pResidual 2 F.H).trans
    (normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F)))

omit [Finite G] in
private theorem residual_core_le_core : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual 2 F.H)

/-- The residual two-core already moves U; the original core action cannot come only from H/K. -/
theorem residual_core_moves_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ (K F).pCoreIn 2 ≤ centralizer (F.U : Set G) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hcent
  have hcomm : ⁅F.H.pCoreIn 2,K F⁆ ≤ (K F).pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show K F ≤ F.H from map_subtype_le _))
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp
        ((pCoreIn_le 2 F.H).trans (le_normalizer_embedded_pResidual 2 F.H))
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp
        ((show K F ≤ F.H from map_subtype_le _).trans core_normalized)
  have h₁ : ⁅⁅F.U,F.H.pCoreIn 2⁆,K F⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm F.U]
    exact (section_core_commutator_le_point h s).trans
      (point_centralizes.trans (centralizer_le (map_subtype_le _)))
  have h₂ : ⁅⁅F.H.pCoreIn 2,K F⁆,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcent)
  have he := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [commutator_comm (K F),commutator_U h F] at he
  exact plane_moved_of_point_normal h structural hn
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))

/-- The residual core has the same original pairing radical as the full H-core. -/
theorem extraspecial_residual_core_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    F.U ⊓ centralizer ((K F).pCoreIn 2 : Set G) = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let := extraspecial_section_irreducible h hab structural previous hex hcard hexp s
  exact irreducible_centralizer ρ s _
    (residual_core_le_core.trans (pCoreIn_le 2 F.H)) residual_core_normalized
    (residual_core_moves_of_point_normal h hab structural
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp))


/-- The original span lies in the intrinsic two-core of the actual residual, before any recognition datum. -/
theorem span_le_residual_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) : F.U ≤ (K F).pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hUK : F.U ≤ K F := by
    rw [←commutator_U h F]
    exact le_normalizer_iff_commutator_le_right.mp
      (s.section_le.trans (le_normalizer_embedded_pResidual 2 F.H))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U) hUK
    ((show K F ≤ F.H from map_subtype_le _).trans s.normalized)

private theorem pairing_of_radical
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
    (s₀.kernel_le.trans hUN) point_centralizes
    ((commutator_mono hNQ le_rfl).trans (section_core_commutator_le_point h s₀))
    (by simpa using F.card 1 (by decide))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ :=
    { sU with kernel_le := s₀.kernel_le
              kernel_eq := sU.kernel_eq.trans (congrArg (fun C => C.subgroupOf F.U) hc) }
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  exact ⟨_,inferInstance,inferInstance,ρ,s,sN,hd,
    extraspecial_section_irreducible h hab structural previous hex hcard hexp s,hpair⟩

/-- Both original core quotients are the contragredient of the literal six-dimensional U/V₁ section.
The evaluation-zero clause identifies every functional kernel with its actual group centralizer. -/
theorem extraspecial_core_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hN : N = F.H.pCoreIn 2 ∨ N = (K F).pCoreIn 2) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sN : BinaryConjugationSection F.H N (N ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (n : N) (u : F.U),
        (sN.coordinates n).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(n : G),(u : G)⁆ = 1) := by
  rcases hN with rfl | rfl
  · exact pairing_of_radical h hab structural previous hex hcard hexp _ le_rfl
      ((span_le_residual_core h hab).trans residual_core_le_core) core_normalized
      (extraspecial_core_centralizer h hab structural previous hex hcard hexp)
  · exact pairing_of_radical h hab structural previous hex hcard hexp _ residual_core_le_core
      (span_le_residual_core h hab) residual_core_normalized
      (extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp)

/-- Each of the two core-centralizer quotients has order 64. -/
theorem extraspecial_core_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N : Subgroup G) (hN : N = F.H.pCoreIn 2 ∨ N = (K F).pCoreIn 2) :
    (N ⊓ centralizer (F.U : Set G)).relIndex N = 64 := by
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp N hN
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  change Nat.card (N ⧸ (N ⊓ centralizer (F.U : Set G)).subgroupOf N) = 64
  let := sN.kernel_normal
  rw [Nat.card_congr sN.quotientEquiv.toEquiv]
  change Nat.card (Module.Dual (ZMod 2) X) = 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
  rfl


/-- The full core is generated by the residual core and its actual U-centralizer, as in 14.7.20(1). -/
theorem extraspecial_core_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    (K F).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let P := (K F).pCoreIn 2
  let C := centralizer (F.U : Set G)
  let QH := F.H.pCoreIn 2
  have hCQ : C ≤ QH := centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s
  have hPQ : P ≤ QH := residual_core_le_core
  have hjoin : P ⊔ C ≤ QH := sup_le hPQ hCQ
  let : (C.subgroupOf QH).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 F.H).trans (s.normalized.trans (normalizer_le_normalizer_centralizer _)))
  have hrel : C.relIndex (P ⊔ C) = C.relIndex P := by
    have he := relIndex_sup_right (P.subgroupOf QH) (C.subgroupOf QH)
    rw [←subgroupOf_sup hPQ hCQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hPQ] at he
    exact he
  have hP := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp P (Or.inr rfl)
  have hQ := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp QH (Or.inl rfl)
  rw [inf_relIndex_left] at hP hQ
  have hm := relIndex_mul_relIndex C (P ⊔ C) QH le_sup_right hjoin
  rw [hrel,hP,hQ] at hm
  have hone : (P ⊔ C).relIndex QH = 1 := by
    omega
  exact le_antisymm hjoin (Subgroup.relIndex_eq_one.mp hone)


/-- The literal residual core meets the original LT-core in index four. -/
theorem extraspecial_residual_core_seed_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ((K F).pCoreIn 2 ⊓ Q T L).relIndex ((K F).pCoreIn 2) = 4 := by
  let P := (K F).pCoreIn 2
  obtain ⟨X,aX,mX,ρ,sU,sP,_,_,hpair⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  have hi := BinaryConjugationSection.centralizer_index_of_dual_pairing sU sP hpair V
    (le_conjugateSpanBy V F.H)
  rw [sU.imageSpace_card_eq_relIndex V (le_conjugateSpanBy V F.H)] at hi
  have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
  have hZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) V bot_le (F.le_seed 1)
  rw [relIndex_bot_left,relIndex_bot_left,hV,hZ] at hm
  have hv : (F.Vi 1).relIndex V = 4 := by omega
  rw [hv] at hi
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hPLT : P ≤ L ⊔ (T : Subgroup G) :=
    (residual_core_le_core.trans hQT).trans le_sup_right
  have he : P ⊓ Q T L = P ⊓ centralizer (V : Set G) := by
    change P ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [←h.centralizer_LT structural,←inf_assoc,inf_eq_left.mpr hPLT]
  rw [he,inf_relIndex_left]
  exact hi

/-- Original-group application of 14.7.20(1) and its index-four consequence.
Both quotient actions use one literal U/V₁ section; inclusion of the residual
core preserves every coordinate and every functional kernel. -/
theorem extraspecial_core_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 ∧
    F.U ⊓ centralizer ((K F).pCoreIn 2 : Set G) = F.Vi 1 ∧
    (K F).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 ∧
    (centralizer (F.U : Set G)).relIndex (F.H.pCoreIn 2) = 64 ∧
    ((K F).pCoreIn 2 ⊓ Q T L).relIndex ((K F).pCoreIn 2) = 4 ∧
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X)
      (ρ : Representation (ZMod 2) F.H X)
      (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
      (sQ : BinaryConjugationSection F.H (F.H.pCoreIn 2)
        (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual)
      (sP : BinaryConjugationSection F.H ((K F).pCoreIn 2)
        ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual),
      Module.finrank (ZMod 2) X = 6 ∧ IsIrreducible ρ ∧
      (∀ (q : F.H.pCoreIn 2) (u : F.U),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(q : G),(u : G)⁆ = 1) ∧
      (∀ (p : (K F).pCoreIn 2) (q : F.H.pCoreIn 2),
        (p : G) = q → sP.coordinates p = sQ.coordinates q) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hsup := extraspecial_core_supplement h hab structural previous hex hcard hexp
  have hi := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp
    (F.H.pCoreIn 2) (Or.inl rfl)
  rw [inf_relIndex_left] at hi
  refine ⟨extraspecial_core_centralizer h hab structural previous hex hcard hexp,
    extraspecial_residual_core_centralizer h hab structural previous hex hcard hexp,
    hsup,hi,extraspecial_residual_core_seed_index h hab structural previous hex hcard hexp,?_⟩
  obtain ⟨X,aX,mX,ρ,sU,sQ,hd,hirr,hpair⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp (F.H.pCoreIn 2) (Or.inl rfl)
  have hCQ := centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU
  have hs : (K F).pCoreIn 2 ⊔ (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) = F.H.pCoreIn 2 := by
    rwa [inf_eq_right.mpr hCQ]
  obtain ⟨sP,hcoord⟩ := sQ.restrict_of_sup_kernel ((K F).pCoreIn 2)
    residual_core_le_core residual_core_normalized hs
  have hk : (K F).pCoreIn 2 ⊓ (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) =
      (K F).pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
    rw [←inf_assoc,inf_eq_left.mpr residual_core_le_core]
  let sP' : BinaryConjugationSection F.H ((K F).pCoreIn 2)
      ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual :=
    { sP with kernel_le := inf_le_left
              kernel_eq := sP.kernel_eq.trans (congrArg (fun C => C.subgroupOf ((K F).pCoreIn 2)) hk) }
  refine ⟨X,aX,mX,ρ,sU,sQ,sP',hd,hirr,hpair,?_⟩
  intro p q hpq
  exact (hcoord p).trans (congrArg sQ.coordinates (Subtype.ext hpq))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
