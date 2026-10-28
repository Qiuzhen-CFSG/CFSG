module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.FivePair
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.BorelPlacement
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.EvenBorel

/-!
# Ordinary-component elimination in the Sylow contradiction

Full 1.1.5(3), applied to the actual local hypotheses, constructs faithful
conjugation actions. The binary linear and large odd-prime cases then use
their computed Sylow-center bounds. For the pairs over fields of order four
or five, multiplication constructs the component projections, and the
factor stabilizer acts trivially on X/O₂(X), contradicting the D₈ action.
The even-field Borel adapter uses a literal product model and root placement.

`no_component_branch_of_source` completes this branch from the two source
C-component embedding alternatives. The ordinary reduction proves the
odd-core, component, model and inner-action conclusions of full 1.1.5.
The actual marked S₃ × S₃ action supplies D₈. In the even-field pair,
Sylow-aligned matrix coordinates and the E₉ quotient construct the literal
Borel and root placement. Its two-residual property then gives the forbidden
action on the actual four-module [V(M₁),Xᵢ]. V(M₁) is anchored to the
M₁-conjugate closure of Z, rather than an arbitrary auxiliary module.

The genuine universal 1.1.5 and the preceding source geometry and embedding
alternatives remain inputs, as required by this conditional branch contract.
Final Sylow assembly belongs to the overgroup-Sylow task. No 15.4.21–23
identification is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; 1.1.5, printed pp.501–503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The binary component obstruction with faithfulness constructed from full
1.1.5. The model comparison must still supply the inner-action witnesses. -/
theorem no_binary_of_earlier115 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Earlier115Three κ G) {H K U Z : Subgroup G}
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (Q : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H Q M z)
    (hKH : K ≤ H) (hcomp : IsComponent H (K.subgroupOf H))
    (hn : H ≤ normalizer (K : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hinner : CentralInnerAction K Z)
    {n : ℕ} (hn' : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) : False := by
  have ha := component_actions_of_earlier115 hG earlier hlocal hKH hcomp
  exact no_binary_linear_component_central_four hKH hn P hP hZU hZC hcard
    ha.2.2.1 hinner hn' hm

/-- The large odd-prime obstruction uses relative subnormality of the actual
component and obtains its commutator faithfulness from 1.1.5. -/
theorem no_large_odd_pair_of_earlier115 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Earlier115Three κ G) {H K U Z : Subgroup G}
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (Q : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H Q M z)
    (d : OrdinaryComponentPair H K U)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hinner : CentralInnerAction (d.factor false) Z)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL (d.factor false) 2 p) : False := by
  have ha := component_actions_of_earlier115 hG earlier hlocal (d.le_overgroup false) (d.component false)
  let : IsQuasisimple ((d.factor false).subgroupOf H) := (d.component false).2
  let : Group.IsPerfect (d.factor false) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (d.le_overgroup false)).toMonoidHom)
    (subgroupOfEquivOfLe (d.le_overgroup false)).surjective
  have hne : d.factor false ≠ ⊥ := by
    let : IsSimpleGroup (((d.factor false).subgroupOf H) ⧸ center ((d.factor false).subgroupOf H)) := IsQuasisimple.simple
    have hn : Nontrivial ((d.factor false).subgroupOf H) :=
      (QuotientGroup.mk'_surjective (center ((d.factor false).subgroupOf H))).nontrivial
    intro he
    exact (nontrivial_iff_ne_bot ((d.factor false).subgroupOf H)).mp hn (by rw [he,bot_subgroupOf])
  exact no_odd_linear_subnormal_component hne (d.le_overgroup false) (d.component false).1
    P hP hZU hZC hcard ha.2.1 hinner hp hp7 hm

/-- Both small rank-one endpoints contradict D₈. The action hypotheses of
the pair calculation are constructed from full 1.1.5, and field four is
transported through the actual exceptional isomorphism. -/
theorem no_small_pair_of_earlier115 {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Earlier115Three κ G) {H K X U Z : Subgroup G}
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (Q : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H Q M z)
    (d : OrdinaryComponentPair H K U)
    (hm : ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 4 ∨ ClassicalGroup.IsPSL (d.factor i) 2 5)
    (hX : X ≤ K) (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X))
    (hD : Nonempty (((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range ≃* DihedralGroup 4)) : False := by
  have ha (i : Bool) := component_actions_of_earlier115 hG earlier hlocal (d.le_overgroup i) (d.component i)
  have hm' (i : Bool) : ClassicalGroup.IsPSL (d.factor i) 2 5 :=
    (hm i).elim five_model_of_four id
  exact no_five_pair_dihedral_action d.factor d.action d.le_overgroup d.component hm'
    (hX.trans_eq d.product.symm) hUX P hP hZC hcard (fun i => (ha i).1) (fun i => (ha i).2.1) hq hD

/-- Conditional assembly of every ordinary-model obstruction. The two
construction obligations are explicit here: the ordinary-model reduction
and the actual Borel/root placement. `no_component_branch_of_source` below
discharges both from the contrary configuration. -/
theorem no_ordinary_alternatives_with_placed_borels
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) (earlier : Earlier115Three κ G)
    {H K X U Z M V : Subgroup G} {L : Bool → Subgroup G}
    (hlocal : ∀ z ∈ Z, z ≠ 1 → ∃ (Q : Sylow 2 H) (Mz : Subgroup G),
      Chapter1.Lemma115Hypotheses H Q Mz z)
    (a : TwoFactors.MixedLocal.FactorPairAction M L)
    (hMV : M ≤ normalizer (V : Set G)) (i : Bool)
    (hVcard : Nat.card (⁅V,L i⁆ : Subgroup G) = 4)
    (hXK : X ≤ K) (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X))
    (hD : Nonempty (((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range ≃* DihedralGroup 4))
    (hmodels : OrdinaryAlternatives H K U Z)
    (hBorel : ∀ (d : OrdinaryComponentPair H K U) (n : ℕ), 4 ≤ n → Even n →
      (∀ j, ClassicalGroup.IsPSL (d.factor j) 2 (2 ^ n)) →
      EvenBorelPlacement K ⁅V,L i⁆ M (2 ^ n)) : False := by
  rcases hmodels with ⟨hcomp,⟨n,hn,hm⟩,hi⟩ | ⟨d,hm,hi⟩
  · exact no_binary_of_earlier115 hG earlier hlocal hKH hcomp hHK P hP hZU hZC hcard hi hn hm
  · rcases hm with ⟨p,hp,hp5,hm⟩ | ⟨n,heven,hn2,hm⟩
    · by_cases he : p = 5
      · subst p
        exact no_small_pair_of_earlier115 hG earlier hlocal d (fun j => Or.inr (hm j))
          hXK hUX P hP hZC hcard hq hD
      · have hp7 : 7 ≤ p := by
          by_contra h
          have hp6 : p = 6 := by omega
          have hprime := hp.1
          rw [hp6] at hprime
          norm_num at hprime
        exact no_large_odd_pair_of_earlier115 hG earlier hlocal d P hP hZU hZC hcard
          (hi false) hp hp7 (hm false)
    · by_cases hn4 : 4 ≤ n
      · have hpow : 16 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn4
        have hbound := even_borel_placement_field_bound a hMV i hVcard
          (by omega : 4 ≤ 2 ^ n) (hBorel d n hn4 heven hm)
        omega
      · have he : n = 2 := by
          obtain ⟨k,hk⟩ := heven
          omega
        subst n
        have hm4 (j : Bool) : ClassicalGroup.IsPSL (d.factor j) 2 4 := by simpa using hm j
        exact no_small_pair_of_earlier115 hG earlier hlocal d (fun j => Or.inl (hm4 j))
          hXK hUX P hP hZC hcard hq hD

/-- The F*(K) ≠ O₂(K) branch of the contrary Sylow setup is impossible.
The input retains the genuine relative normal closure, prime-to-three
residual, larger Sylow subgroup, both source factor families, and full
marked product action. Ordinary components, inner and faithful actions,
the D₈ quotient action, the five-pair projections, and the actual even-field
Borel/root placement are all constructed by this proof and its dependencies.
Only the full universal earlier 1.1.5 and the preceding source geometry
and C-component embedding alternatives remain as inputs. -/
theorem no_component_branch_of_source
    {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    (earlierThree : Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : OrdinaryReduction.SourceContext d i j H K U)
    (b : OrdinaryReduction.EmbeddingAlternatives H K U)
    (a : TwoFactors.MixedLocal.FactorPairAction d.M₁ d.X)
    (hVM : IsElementaryAbelian 2 d.VM₁)
    (hVM_eq : d.VM₁ = EmbeddingReduction.normalClosureIn d.Z d.M₁)
    (hVcard : Nat.card (d.V₁ i) = 4)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hF : generalizedFitting K ≠ pCore 2 K) : False := by
  have hXK : d.wholeX ≤ K :=
    s.closure ▸ EmbeddingReduction.le_normalClosureIn s.placed.whole_le
  have hKH : K ≤ H :=
    s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  have hHK : H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hKH).mp
    rw [s.closure]
    exact EmbeddingReduction.normalClosureIn_normal _ _
  have hUX : U ≤ normalizer (d.wholeX : Set G) :=
    s.placed.upper.le.trans s.placed.T_normalizes
  have hVM₁ : d.VM₁ ≤ d.M₁ :=
    hVM_eq ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  have hMVM : d.M₁ ≤ normalizer (d.VM₁ : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hVM₁).mp
    rw [hVM_eq]
    exact EmbeddingReduction.normalClosureIn_normal _ _
  have hZU : d.Z ≤ U := by
    apply le_trans (show d.Z ≤ ChapterB.baumann (d.T : Subgroup G) from ?_)
      s.placed.baumann_le
    intro z hz
    rw [s.omega] at hz
    have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    refine ⟨hzT.1, mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hJT : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) ≤
        (d.T : Subgroup G) := sSup_le fun _ hA => hA.1
    exact hzT.2.2 w (hJT ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hw).1)
  have hZC : d.Z ≤ centralizer (U : Set G) := by
    intro z hz
    rw [s.omega] at hz
    apply mem_centralizer_iff.mpr
    intro u hu
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 u
      (s.placed.upper.le hu)
  have hU : IsPGroup 2 U :=
    s.placed.sylow_image ▸ s.placed.sylow.isPGroup'.map H.subtype
  have hperm : ∀ u ∈ U, ∀ V ∈ ({d.X false, d.X true} : Set (Subgroup G)),
      V.map (MulAut.conj u).toMonoidHom ∈ ({d.X false, d.X true} : Set (Subgroup G)) := by
    intro u hu V hV
    obtain ⟨σ, hσ⟩ := s.placed.permutes u hu
    have hm (k : Bool) : (d.X k).map (MulAut.conj u).toMonoidHom ∈
        ({d.X false, d.X true} : Set (Subgroup G)) := by
      rw [hσ k]
      cases σ k <;> simp
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · exact hm false
    · exact Set.mem_singleton_iff.mp hV ▸ hm true
  have hD := contrary_dihedral_from_full_product d.wholeX
    (ChapterB.baumann (d.T : Subgroup G)) U hU s.placed.baumann_le hUX
    s.placed.quotient d.X rfl s.placed.product s.placed.product_surjective
    s.placed.product_kernel s.placed.first_image s.placed.second_image hperm i s.placed.moves
  have hmodels := ordinary_alternatives_of_source hG earlierOneTwo earlierThree s b hF
  apply no_ordinary_alternatives_with_placed_borels hG earlierThree s.local115 a hMVM i
    hVcard hXK hKH hHK hUX s.placed.sylow s.placed.sylow_image hZU hZC s.four
    (order_nine_quotient_structure s.placed.quotient).1.isPGroup hD hmodels
  intro pair n hn heven hm
  exact (even_pair_borel_placement_of_source d s.placed pair s.generation.symm hXK
    hunique hVM hVM₁ hMVM hVcard heven hn hm).1

/-- The surviving Fitting branch for the final Sylow assembly. This equality
is deduced by eliminating the component branch; it is not a setup premise. -/
theorem generalizedFitting_eq_twoCore_of_source
    {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    (earlierThree : Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : OrdinaryReduction.SourceContext d i j H K U)
    (b : OrdinaryReduction.EmbeddingAlternatives H K U)
    (a : TwoFactors.MixedLocal.FactorPairAction d.M₁ d.X)
    (hVM : IsElementaryAbelian 2 d.VM₁)
    (hVM_eq : d.VM₁ = EmbeddingReduction.normalClosureIn d.Z d.M₁)
    (hVcard : Nat.card (d.V₁ i) = 4)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁) :
    generalizedFitting K = pCore 2 K := by
  by_contra hF
  exact no_component_branch_of_source hG earlierOneTwo earlierThree s b a hVM hVM_eq
    hVcard hunique hF

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
