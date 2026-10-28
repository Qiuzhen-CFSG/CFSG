module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.GroupTheory.CharacteristicTwoLocalCover

public import Theory.GroupTheory.Hall.CyclicHallSmallIndex
public import Theory.SpecificGroups.Janko4.Model.SylowAbelianIndex
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourHall

/-!
# A nontrivial two-core for the entire native J₄ Hall actor

For the same surjection and original images S, D and E, the solvable group
K = (D join S) join E has nontrivial two-core. The two cyclic Hall products
give an index at most three subgroup; a trivial core would force an abelian
subgroup of index at most two in S, contradicted by J₄'s extraspecial seed.

The normalizer of the embedded two-core supplies a nonzero elementary
subgroup invariant under the whole K. After literal Sylow conjugacy, the
checked kernel catalogue puts K in max1 or gives a small K-minimal elementary
row, retaining its actual kernel inclusion and normalizer irreducibility.
The original residual R, S₅ and marked S₃ quotients, both Hall products and
escape conditions are preserved under the same original map. Placement and
normalization of that same R remain separate obligations.

Source: Aschbacher--Smith 5.1.9--13, printed pp.634--637, refs/quasithin.pdf.
The model and finite catalogue imports retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SylowNormalEights
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open KernelOrders OutsideKernelOrders
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M₁" => max1Subgroup matrixA_mul_self matrixB_pow_four

/-- A small elementary row with the actual Mathieu-kernel inclusion and
purity and minimality for the entire actor. -/
@[expose] def JankoFourMinimalKernelRow (K E : Subgroup Model) : Prop :=
  ∃ A : Subgroup Model, A ≠ ⊥ ∧ A ≤ E ∧ IsElementaryAbelian 2 A ∧
    Nat.card A ≤ 8 ∧ K ≤ normalizer (A : Set Model) ∧
    A ≤ orderSpectrumKernel ∧ ClosureNormalizerIrreducible A ∧
    (∀ u ∈ A, ¬ IsConj u classSeed) ∧
    ∀ X : Subgroup Model, X ≤ A → K ≤ normalizer (X : Set Model) → X = ⊥ ∨ X = A

private theorem fixed_whole_actor_minimal_alternative (K E : Subgroup Model)
    (hSE : E ≤ twoSubgroup) (he : E ≠ ⊥) (hel : IsElementaryAbelian 2 E)
    (hSK : twoSubgroup ≤ K) (hn : K ≤ normalizer (E : Set Model)) :
    K ≤ M₁ ∨ JankoFourMinimalKernelRow K E := by
  obtain ⟨A,⟨ha,hnA⟩,hAE,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun A : Subgroup Model => A ≠ ⊥ ∧ K ≤ normalizer (A : Set Model)) E ⟨he,hn⟩
  have hm : ∀ X : Subgroup Model, X ≤ A → K ≤ normalizer (X : Set Model) →
      X = ⊥ ∨ X = A := by
    intro X hXA hKX
    by_cases hx : X = ⊥
    · exact Or.inl hx
    · exact Or.inr (hmin X ⟨hx,hKX⟩ hXA)
  have hi : ClosureNormalizerIrreducible A := by
    intro X hXA hNX
    exact hm X hXA (hnA.trans hNX)
  let := hel
  have heA : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAE
  have hSA := hSK.trans hnA
  have hAK : A ≤ orderSpectrumKernel :=
    elementary_sylow_le_kernel_of_outside_certificates
      MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
      (outsideCatalogue_of_card (presentation_card_of_equiv
        (matrixEquivOfWords MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure)))
      matrixKernel_eq_orderSpectrumKernel rankCertificates A (hAE.trans hSE) hSA heA hi
  by_cases hp : ∀ u ∈ A, ¬ IsConj u classSeed
  · have hcard : Nat.card A ≤ 8 := by
      obtain ⟨i,heq⟩ := pureKernelCatalogue.1 A hAK hSA hp
      have hnot : i ≠ 5 := by
        intro hfive
        subst i
        subst A
        obtain ⟨X,hX,hne,hN⟩ := PureNormalizers.candidate_five_obstruction
        rcases hi X hX.le hN with hx | hx
        · exact hne hx
        · exact hX.ne hx
      rw [heq,pureKernelCatalogue.2 i]
      fin_cases i <;> norm_num [candidateRows] at *
      exact hnot rfl
    exact Or.inr ⟨A,ha,hAE,heA,hcard,hnA,hAK,hi,hp,hm⟩
  · push Not at hp
    obtain ⟨u,hu,hc⟩ := hp
    exact Or.inl (hnA.trans (normalizer_le_max1_of_seed_conjugate A hAK u hu hc))

/-- Literal Sylow transport, a whole-actor invariant elementary subgroup, and
the marked small-row alternative. This makes no assertion that R lies in K. -/
@[expose] def JankoFourWholeActorPlacement (S : Sylow 2 Model) (K : Subgroup Model) : Prop :=
  ∃ (g : Model) (E : Subgroup Model),
    (S : Subgroup Model).map (MulAut.conj g).toMonoidHom = twoSubgroup ∧
    E ≠ ⊥ ∧ E ≤ twoSubgroup ∧ (E.subgroupOf twoSubgroup).Normal ∧
    IsElementaryAbelian 2 E ∧
    K.map (MulAut.conj g).toMonoidHom ≤ normalizer (E : Set Model) ∧
    (K.map (MulAut.conj g).toMonoidHom ≤ M₁ ∨
      JankoFourMinimalKernelRow (K.map (MulAut.conj g).toMonoidHom) E)

private noncomputable def fixedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

/-- A nontrivial intrinsic two-core gives a whole-actor placement without
assuming a nontrivial two-core in an arbitrary maximal overgroup. -/
theorem jankoFour_whole_actor_placement (S : Sylow 2 Model) (K : Subgroup Model)
    (hSK : (S : Subgroup Model) ≤ K) (hc : pCore 2 K ≠ ⊥) :
    JankoFourWholeActorPlacement S K := by
  let U := (pCore 2 K).map K.subtype
  have hU : U ≠ ⊥ := fun hz => hc ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hz)
  have hKU : K ≤ normalizer (U : Set Model) := by
    have hh := (map_mono (f := K.subtype)
      (show (⊤ : Subgroup K) ≤ normalizer (pCore 2 K : Set K) from le_normalizer_of_normal)).trans
      ((pCore 2 K).le_normalizer_map K.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  obtain ⟨E,hE,hES,_,hel,hNE⟩ := exists_normal_elementary_sylow_overgroup S
    (normalizer (U : Set Model)) ⟨U,hU,pCore_isPGroup.map K.subtype,rfl⟩ (hSK.trans hKU)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S fixedSylow
  let f := (MulAut.conj g).toMonoidHom
  have hS : (S : Subgroup Model).map f = twoSubgroup := congrArg Sylow.toSubgroup hg
  let E' := E.map f
  let K' := K.map f
  have hE' : E' ≠ ⊥ := fun hz => hE ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hz)
  have hES' : E' ≤ twoSubgroup := hS ▸ map_mono hES
  have hSK' : twoSubgroup ≤ K' := hS ▸ map_mono hSK
  have hK'E : K' ≤ normalizer (E' : Set Model) :=
    (map_mono (hKU.trans hNE)).trans (E.le_normalizer_map f)
  let := hel
  have hel' : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  exact ⟨g,E',hS,hE',hES',
    (normal_subgroupOf_iff_le_normalizer hES').mpr (hSK'.trans hK'E),hel',hK'E,
    fixed_whole_actor_minimal_alternative K' E' hES' hE' hel' hSK' hK'E⟩

open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The same original native action now supplies a nontrivial whole-actor two-core
and the marked placement alternative, retaining every original Hall and residual clause. -/
theorem normal_jankoFour_native_whole_actor
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (S : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ x : C, f x = e (QuotientGroup.mk' (pCore 2 C) x)) ∧
      (S : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      let R := ((residual H).subgroupOf Y).map f
      let D := (A.subgroupOf Y).map f
      let E := (B.subgroupOf Y).map f
      R ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      Nat.card B = 3 ∧ Nat.card E = 3 ∧ E ≤ R ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set Janko4.Model) ∧
      (D : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (D : Set Janko4.Model) ∧
      Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ∧
      (E : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (E : Set Janko4.Model) ∧
      Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 ∧
      Nat.card (pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) = 2^20 ∧
      Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
        pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
        Equiv.Perm (Fin 5)) ∧
      (∃ e₃ : ((E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
          pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
          Equiv.Perm (Fin 3),
        let N := E ⊔ (S : Subgroup Janko4.Model)
        let q := e₃.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf N).map q) = 2 ∧
        Nat.card ((E.subgroupOf N).map q) = 3) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E ∧
      pCore 2 ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ≠ ⊥ ∧
      JankoFourWholeActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot⟩ :=
    normal_jankoFour_native_hall_geometry h hH hgen c hY hescape hR C hC hRC e
  let D := (A.subgroupOf Y).map f
  let E := (B.subgroupOf Y).map f
  let := hcyc
  have htwo : pCore 2 ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ≠ ⊥ :=
    CyclicHallSmallIndex.twoCore_ne_bot_of_products D (S : Subgroup Janko4.Model) E
      hodd S.isPGroup' hED hE hDS hES hsol (Janko4.sylow_no_abelian_index_le_two S)
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,
    jankoFour_whole_actor_placement S _ (le_sup_right.trans le_sup_left) htwo⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
