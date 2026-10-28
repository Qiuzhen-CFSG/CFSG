module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourMax1
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.SeedFusion
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PairRanks
public import Theory.GroupAction.MinimalNormal
public import Theory.GroupTheory.AlternatingFiveSmallAction
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement

/-!
# From a normal elementary subgroup to a J₄ involution centralizer

Choose a minimal nonzero subgroup invariant under the actual local subgroup
and its full Sylow actor. It is irreducible for its full ambient normalizer,
so the checked Sylow catalogue places it inside the literal Mathieu kernel.
A subgroup containing a 2B involution has normalizer in max1, excluded by
the actual M₂₄ quotient. The pure rows have order at most eight; their A₅
extension action is trivial. The resulting even centralizer contains an
involution fixed by the original Sylow. This retains both original subgroups
without requiring irreducibility of the initial elementary group.

Source: Aschbacher--Smith A.3.12(17) and10.2.9, printed pp.47--48 and750--751.
The imported catalogues retain their literal J₄ matrix certificate provenance.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SylowNormalEights
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open KernelOrders OutsideKernelOrders
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private theorem exists_minimal_invariant (H E : Subgroup Model)
    (he : E ≠ ⊥) (hn : H ≤ normalizer (E : Set Model)) :
    ∃ A : Subgroup Model, A ≠ ⊥ ∧ A ≤ E ∧ H ≤ normalizer (A : Set Model) ∧
      ClosureNormalizerIrreducible A := by
  obtain ⟨A,⟨ha,hnA⟩,hAE,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun A : Subgroup Model => A ≠ ⊥ ∧ H ≤ normalizer (A : Set Model)) E ⟨he,hn⟩
  refine ⟨A,ha,hAE,hnA,?_⟩
  intro X hXA hNX
  by_cases hx : X = ⊥
  · exact Or.inl hx
  · exact Or.inr (hmin X ⟨hx,hnA.trans hNX⟩ hXA)

/-- Every full-normalizer irreducible pure kernel row has at most eight elements. -/
private theorem pure_irreducible_card_le_eight (A : Subgroup Model)
    (hAK : A ≤ orderSpectrumKernel) (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (hi : ClosureNormalizerIrreducible A) (hp : ∀ u ∈ A, ¬ IsConj u classSeed) :
    Nat.card A ≤ 8 := by
  obtain ⟨i,rfl⟩ := pureKernelCatalogue.1 A hAK hn hp
  have hnot : i ≠ 5 := by
    intro he
    subst i
    obtain ⟨X,hX,hne,hN⟩ := PureNormalizers.candidate_five_obstruction
    rcases hi X hX.le hN with hx | hx
    · exact hne hx
    · exact hX.ne hx
  rw [pureKernelCatalogue.2 i]
  fin_cases i <;> norm_num [candidateRows] at *
  exact hnot rfl

/-- A pair normalizing a nonzero elementary subgroup of the fixed full Sylow
is either in max1 or normalizes a nonzero elementary group of order at most eight. -/
theorem fixed_pair_minimal_alternative (H E : Subgroup Model)
    (hSE : E ≤ twoSubgroup) (he : E ≠ ⊥) (hel : IsElementaryAbelian 2 E)
    (hSH : twoSubgroup ≤ H) (hn : H ≤ normalizer (E : Set Model)) :
    H ≤ M ∨ ∃ A : Subgroup Model, A ≠ ⊥ ∧ A ≤ E ∧
      IsElementaryAbelian 2 A ∧ Nat.card A ≤ 8 ∧ H ≤ normalizer (A : Set Model) := by
  obtain ⟨A,hne,hAE,hHA,hi⟩ := exists_minimal_invariant H E he hn
  let := hel
  have heA : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAE
  have hSA := hSH.trans hHA
  have hAK : A ≤ orderSpectrumKernel :=
    elementary_sylow_le_kernel_of_outside_certificates
      MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
      (outsideCatalogue_of_card (presentation_card_of_equiv
        (matrixEquivOfWords MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure)))
      matrixKernel_eq_orderSpectrumKernel rankCertificates A (hAE.trans hSE) hSA heA hi
  by_cases hp : ∀ u ∈ A, ¬ IsConj u classSeed
  · exact Or.inr ⟨A,hne,hAE,heA,pure_irreducible_card_le_eight A hAK hSA hi hp,hHA⟩
  · push Not at hp
    obtain ⟨u,hu,hc⟩ := hp
    exact Or.inl (hHA.trans (normalizer_le_max1_of_seed_conjugate A hAK u hu hc))
private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_even_centralizer (B E : Subgroup Model)
    (hl : B ∈ localCComponents markedSylow)
    (hnB : twoSubgroup ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hES : E ≤ twoSubgroup) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : twoSubgroup ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  rcases fixed_pair_minimal_alternative (B ⊔ twoSubgroup) E hES hne he le_sup_right
    (sup_le hBE hSE) with hmax | ⟨A,hA,hAE,heA,hcard,hHA⟩
  · exact (not_pair_le_max1 markedSylow B hl hnB eB
      (le_sup_left.trans hmax) (le_sup_right.trans hmax)).elim
  · let := heA
    let := SolvableQuotients.local_perfect hl
    have hBA := le_sup_left.trans hHA
    let f := A.normalizerMonoidHom.comp (inclusion hBA)
    have hf : f = 1 := AlternatingFiveSmallAction.small_elementary_action_trivial eB hcard f
    have hBC : B ≤ centralizer (A : Set Model) := by
      intro b hb
      have hk : inclusion hBA ⟨b,hb⟩ ∈ A.normalizerMonoidHom.ker := by
        change f ⟨b,hb⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hk
    have hAC : A ≤ centralizer (B : Set Model) := le_centralizer_iff.mp hBC
    have h2 : 2 ∣ Nat.card A := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hn
        exact hA (A.eq_bot_of_card_eq hn)
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact h2.trans (card_dvd_of_injective (inclusion hAC) (inclusion_injective hAC))

/-- A nonzero normal elementary subgroup shared by the original local A5
and its full Sylow forces even centralizer in the actual J4 carrier. -/
theorem even_centralizer_of_normal_elementary (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hnB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S markedSylow
  let f := MulAut.conj g
  have hS : (S : Subgroup Model).map f.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hnB).trans (B.le_normalizer_map f.toMonoidHom)
  have hSE' := (map_mono (f := f.toMonoidHom) hSE).trans (E.le_normalizer_map f.toMonoidHom)
  have hES' := map_mono (f := f.toMonoidHom) hES
  rw [hS] at hl' hn' hSE' hES'
  let := he
  have h := fixed_even_centralizer (B.map f.toMonoidHom) (E.map f.toMonoidHom)
    hl' hn' (SolvableQuotients.section_map f.toMonoidHom B hl eB).some hES'
    (fun hz => hne ((map_eq_bot_iff_of_injective _ f.injective).mp hz))
    (IsElementaryAbelian.map f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hBE).trans (E.le_normalizer_map f.toMonoidHom)) hSE'
  have hc : (centralizer (B : Set Model)).map f.toMonoidHom =
      centralizer (B.map f.toMonoidHom : Set Model) := by
    rw [map_centralizer_equiv]
    rfl
  rw [←hc,card_map_of_injective f.injective] at h
  exact h

/-- The same original pair lies in an actual involution centralizer. -/
theorem involution_centralizer_placement (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hnB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model)) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ (S : Subgroup Model) ≤ centralizer ({z} : Set Model) :=
  exists_involution_centralizing_normalizing_two_group B (S : Subgroup Model) S.isPGroup'
    hnB (even_centralizer_of_normal_elementary S B E hl hnB eB hES hne he hBE hSE)

/-- The nontrivial original two-core supplies the normal elementary input,
so no additional seed or irreducibility hypothesis is needed for placement. -/
theorem involution_centralizer_placement_of_core (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ (S : Subgroup Model) ≤ centralizer ({z} : Set Model) := by
  obtain ⟨N,hN,hBN,hSN⟩ := SolvableQuotients.exists_maximal_two_local S B hn hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le S hN hSN
  let E := R.map (S : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by
    let := heR
    exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  exact involution_centralizer_placement S B E hl hn eB (map_subtype_le R) hne he
    (hNR ▸ hBN) (hNR ▸ hSN)

private theorem second_seed_conjugacy :
    IsConj (InvolutionCentralizers.Second.seed : Model) ((a*b*a*b*b)^5) := by
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha,hb] at hg
  have hw : Simplicity.word a b "ababb" = a*b*a*b*b := by
    simp [Simplicity.word,mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g,hg.symm⟩

private theorem centralizer_map_of_conj {x y : Model} (g : Model)
    (hg : g*x*g⁻¹=y) :
    (centralizer ({x} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set Model) := by
  rw [map_centralizer_equiv,Set.image_singleton]
  exact congrArg (fun z => centralizer ({z} : Set Model)) hg

/-- Every original full-Sylow local A5 section with nontrivial two-core is
carried into the literal first involution centralizer by ambient conjugation.
The second class is excluded through literal containment in max1. -/
theorem first_centralizer_placement (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ g : Model,
      B.map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer ∧
      (S : Subgroup Model).map (MulAut.conj g).toMonoidHom ≤
        InvolutionCentralizers.First.centralizer := by
  obtain ⟨z,hz,hpair⟩ := involution_centralizer_placement_of_core S B hl hn eB hc
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hz with h | h
  · obtain ⟨g,hg⟩ := isConj_iff.mp h.symm
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    exact ⟨g,le_sup_left.trans hmap,le_sup_right.trans hmap⟩
  · obtain ⟨g,hg⟩ := isConj_iff.mp (second_seed_conjugacy.trans h).symm
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    have hBM := (le_sup_left.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1
    have hSM := (le_sup_right.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1
    exact (not_pair_map_le_max1 (MulAut.conj g) S B hl hn eB hBM hSM).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
