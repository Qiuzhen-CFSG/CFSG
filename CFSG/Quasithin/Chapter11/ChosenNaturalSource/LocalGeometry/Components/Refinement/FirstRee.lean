module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstExceptionalLie
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstReeModels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.SpecificGroups.ReeF4.TwoRankLower

/-!
# Excluding the Ree row at the first flag normalizer

The first containing C-component centralizes V₁ and meets the faithful
Cartan factor trivially. A primitive prime for its odd binary degree is
larger than that degree. The actual Ree split torus has rank two at this
prime, and the proved outer order divides the degree. Hence the prime
residual of the local normalizer, after its ambient two-core quotient,
is the component. Membership lifts through the two-group supplement and
contradicts the faithful Cartan element.

Simplicity is derived here, not assumed for the model. The native Tits
eight gives two-rank at least three. The SQTK noncentral-Fitting theorem
therefore makes the two-core image quasisimple. Its inherited perfectness
and the actual core-free maximal Ree parabolic kill its center, giving
simplicity and permitting the known outer-automorphism theorem.

The literal Cartan consumer removes the final non-field-four Lie row.
With the complete embedding list supplied, every non-field-four first
component equals L₁. At field four the linear models, PSL₂(25), signed
ternary field-five models and J₁ remain in addition to the established
refinement alternatives. No embedding classification or triangle is asserted.

The preceding flag uniqueness, quotient model, pointwise action, Cartan
order and faithfulness are inputs of qt-d-1222-natural-flag-cartan, with
ultimate discharge by qt-d-1222-natural-local-geometry. This owner retains
the exhaustive embeddings, remaining field-four sieve and triangle,
second-component equality, and source-family assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, using A.3.18 on printed pp.51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open ExceptionalActors

private theorem ree_primitive_mem {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (B : Subgroup H) [B.Normal]
    (hB : B.IsCComponent) {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime)
    (ho : Odd p) (hnp : 2 * m + 1 < p) (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (B ⧸ pCore 2 B) m)
    {a : H} (ha : a ^ p = 1) : a ∈ B := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d,⟨e⟩⟩ := hmodel
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let eC : C ≃* d.fixedGroup := (cComponentTwoCoreQuotientEquiv hB).symm.trans e
  let := pCore_isNilpotent (p := 2) (G := H)
  have hCQ : C.IsCComponent := hB.map_quotient _
  let : Group.IsPerfect C := hCQ.perfect
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := eC.toMonoidHom) eC.surjective
  have hHQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hH.stronglyQuasithin r hr hor)
  have htwo : 2 ≤ primeRank 2 C := by
    rw [primeRank_congr 2 (eC.trans d.modelEquiv)]
    exact (by decide : 2 ≤ 3).trans (ReeF4.three_le_twoRank m)
  let : IsQuasisimple C :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
      hHQ (pCore_quotient_pCore_eq_bot 2) hCQ htwo
  have hz : center C = ⊥ := by
    apply bot_unique
    intro z hz
    exact eC.map_eq_one_iff.mp ((ree_center_eq_bot_of_perfect hm d).le
      ((centerCongr eC) ⟨z,hz⟩).property)
  let eZ : (C ⧸ center C) ≃* d.fixedGroup :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eC
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : IsSimpleGroup d.fixedGroup := eZ.symm.isSimpleGroup
  have hC : IsComponent (H ⧸ pCore 2 H) C := ⟨hCQ.subnormal,inferInstance⟩
  have hr : 2 ≤ primeRank p C := by
    rw [primeRank_congr p eC]
    exact ree_split_rank d hd
  have hb := hHQ.stronglyQuasithin p hp ho
  have hres : B.map q = primeToResidual p (H ⧸ pCore 2 H) :=
    (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual hC
      (by rw [hz,card_bot]; exact Nat.coprime_one_right p) hr hb eZ (by
        intro b _ k hk
        exact ree_primitive_primePower_inner hm d hp hnp b k hk)).2
  have hbar : q a ∈ B.map q := by
    rw [hres]
    apply mem_primeToResidual_of_pow (n := 1)
    simp only [pow_one, ← map_pow, ha, map_one]
  have haJ : a ∈ B ⊔ pCore 2 H := by
    have hh : a ∈ (B.map q).comap q := hbar
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hi : Nat.Coprime p (B.subgroupOf (B ⊔ pCore 2 H)).index := by
    change Nat.Coprime p (B.relIndex (B ⊔ pCore 2 H))
    rw [relIndex_sup_left]
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_dvd_pow
    exact (((Nat.coprime_two_right.mpr ho).pow_right m).coprime_dvd_right hm).coprime_dvd_right
      (relIndex_dvd_card _ _)
  exact primeToResidual_le _ hi (mem_primeToResidual_of_pow (n := 1)
    (show (⟨a,haJ⟩ : ↥(B ⊔ pCore 2 H)) ^ (p ^ 1) = 1 from Subtype.ext (by simpa using ha)))

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual large Ree first-component row is impossible. The primitive
split prime avoids its field actors, and rank two forces it into the
component, contradicting the faithful Cartan factor. -/
theorem first_component_not_ree
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    {m : ℕ} (hmpos : 1 ≤ m) (hn : S.field.degree = 2 * m + 1) :
    ¬ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ pCore 2 K) m := by
  intro hk
  obtain ⟨p,hp,hnp,ho,hd⟩ := primitive_split_prime S.nonbinary (by omega)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (hXcard.symm ▸ hd)
  have haG : orderOf (a : G) = p := (orderOf_coe a).trans ha
  have hap : (a : G) ^ p = 1 := by simpa only [haG] using pow_orderOf_eq_one (a : G)
  have haK : (a : G) ∉ K := by
    intro haK
    have he : (a : G) = 1 := mem_bot.mp ((first_component_disjoint_of_faithful_cartan
      D S f hm hfix hK.1 hLK hfaith).le_bot ⟨haK,a.property⟩)
    rw [he,orderOf_one] at haG
    exact hp.ne_one haG.symm
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  have hmB : Chapter1.Section02.LocalModels.IsReeF4At (B ⧸ pCore 2 B) m := by
    obtain ⟨d,⟨j⟩⟩ := hk
    exact ⟨d,⟨e.trans j⟩⟩
  exact haK (ree_primitive_mem (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0))
    B hK.1.2 hmpos hp ho (hn ▸ hnp) (hn ▸ hd) hmB
    (a := ⟨a,hXN a.property⟩) (Subtype.ext hap))

/-- Every first-normalizer Lie row forces field four and is linear.
The Ree exclusion completes the all-degree Lie sieve. -/
theorem first_lie_overgroup_four_linear
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G))
    (hXcard : Nat.card X₁ = 2 ^ S.field.degree - 1)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) := by
  rcases first_lie_overgroup_four_linear_or_ree D S f hm hfix hK hLK hXN
    hXcard hfaith hk with h | ⟨m,hmpos,hn,h⟩
  · exact h
  · exact (first_component_not_ree D S f hm hfix hK hLK hXN
      hXcard hfaith hmpos hn h).elim

/-- Apply the complete Lie sieve to the original Cartan factor, retaining
its literal quotient-centralizer definition and the same invariant flag. -/
theorem first_lie_overgroup_four_linear_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : LieOvergroup (K ⧸ pCore 2 K) S.field.degree) :
    S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :=
  first_lie_overgroup_four_linear D S f hm hfix hK hLK
    (inf_le_left.trans (f.cartan_normalizes hu hX 0)) hXcard hfaith hk

/-- Away from field four, the complete embedding alternatives force the
first containing component to equal L₁. The embedding list remains an input. -/
theorem first_nonfour_component_equal_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hn : S.field.degree ≠ 2) (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    f.Li 0 = K := by
  cases hk with
  | equal h => exact h
  | four h _ => exact (hn h).elim
  | lie h =>
    exact (hn (first_lie_overgroup_four_linear_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith h).1).elim

/-- The complete first-normalizer sieve now has unresolved models only at
field four. All other degrees give the equality refinement. Each surviving
model is an actual isomorphism type of K/O₂(K), not a group-family tag. -/
theorem first_refinement_or_fieldFour_models_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
        (∃ u, Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
          Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model))) := by
  by_cases hn : S.field.degree = 2
  · rcases first_fieldFour_refinement_or_remaining_models_of_cartan D S f hu hm hfix hX hK hLK
      hXcard hfaith hn hk with h | h
    · exact .inl h
    · exact .inr ⟨hn,h⟩
  · have he := first_nonfour_component_equal_of_cartan
      D S f hu hm hfix hX hK hLK hXcard hfaith hn hk
    exact .inl (.equal (by simpa using he))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
