module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryFixedCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NoncentralPairedComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCatalogueSquare
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionEstimate

/-!
# Fixed subgroups with two large unitary markings

The paired core indices are bounded above by the moving field order. The
reverse unitary comparison gives the matching lower bound and saturates the
moving core-intersection index. Thus the small-index premise of the trapped
fixed-subgroup theorem follows from the original graph hypotheses.

The terminal unitary residual estimate also traps the full fixed subgroup
inside the beta core. Consequently that subgroup fixes the entire beta span,
and the fixed subgroup in the chosen moving center is exactly the intersection
of all terminal neighboring centers. These are reductions of the remaining
unitary branch, not a proof of centrality of the original displacement.

Source: DGS, *Groups and Graphs* (1985), 8.2, 8.3 and 8.7,
printed pp.134--140.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

private theorem marked_unitary_rank {D : Type*} [Group D] [Finite D] {n : ℕ}
    (hn : 2 ≤ n) (hu : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n)) :
    primeRank 2 D ≤ n := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le

/-- With large unitary terminal and moving markings, the two original
opposite core indices and the moving intersection index all equal the
moving field order. No centrality or proper-product premise is used. -/
theorem reduced_double_unitary_core_indices
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
        pCore 2 (graphLocalGroup Γ a')) 3 (2^k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2^k))
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hw : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
        pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n)) :
    (Q Γ a').relIndex (V Γ beta 1) = 2^n ∧
      (Q Γ beta).relIndex (V Γ a' 1) = 2^n ∧
      (Q Γ w.val).relIndex (V Γ beta 1 ⊓ Q Γ a') = 2^n := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (graphLocalGroup Γ w.val) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr := marked_unitary_rank hn hw
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  obtain ⟨hx,hy⟩ := reduced_noncentral_unitary_paired_index_le
    h models hc hab hd hb hcomm hne hk hn hu w hm hr
  have he := reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne
  have hs := (source_paired_core_indices ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm n hr).2.2.1
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hlo : (2^n)^2 ≤ (Q Γ a').relIndex (V Γ beta 1) *
      (Q Γ w.val).relIndex (V Γ beta 1 ⊓ Q Γ a') := by
    rcases source_unitary_reverse_index_alternatives ht (Reduction.reduced_borel_core_sylow h)
      d hc hab hd hb hcomm models w hm hn hw with hl | hl
    · have hsq := hl.trans hy
      nlinarith only [hq,hsq]
    · exact hl
  have hxe : (Q Γ a').relIndex (V Γ beta 1) = 2^n := by
    apply le_antisymm hx
    have hmul : 2^n * 2^n ≤ (Q Γ a').relIndex (V Γ beta 1) * 2^n := by
      simpa only [pow_two] using hlo.trans (Nat.mul_le_mul_left _ hs)
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hse : (Q Γ w.val).relIndex (V Γ beta 1 ⊓ Q Γ a') = 2^n := by
    apply le_antisymm hs
    rw [hxe,pow_two] at hlo
    exact Nat.le_of_mul_le_mul_left hlo (by omega)
  exact ⟨hxe,he.symm.trans hxe,hse⟩

/-- The full terminal-span fixed subgroup is trapped in the beta core
and fixes the whole beta span. Both the trapping and small-index premises
are discharged from the two unitary markings. -/
theorem reduced_double_unitary_fixed_centralizer
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
        pCore 2 (graphLocalGroup Γ a')) 3 (2^k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2^k))
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hw : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
        pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n)) :
    V Γ a' 1 ⊓ centralizer ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ L S₀)) :
      Set (Reduction.G₀ L S₀)) ≤ Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let A := V Γ beta 1 ⊓ Q Γ a'
  let E := V Γ a' 1 ⊓ centralizer (A : Set (Reduction.G₀ L S₀))
  change E ≤ Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))
  obtain ⟨hx,hy,_⟩ := reduced_double_unitary_core_indices h models hc hab hd hb hcomm hk hn hu w hm hw
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hsmall : (Q Γ a').relIndex (V Γ beta 1) < (2^n)^2 := by rw [hx]; nlinarith only [hq]
  have hb3 := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ a' 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow
      (Nat.lt_of_lt_of_le (by decide) hb3) a'
  let : IsElementaryAbelian 2 (V Γ beta 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow
      (Nat.lt_of_lt_of_le (by decide) hb3) beta
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : Finite (graphLocalGroup Γ a') := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (d.localGroup a') := Finite.of_injective
    (inclusion (d.local_le a')) (inclusion_injective _)
  have hVL : V Γ beta 1 ≤ d.localGroup a' := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let R : Sylow 2 (graphLocalGroup Γ a') := default
  let Rq := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a')))
  have hRq : Nat.card (omegaCenterIn Rq.toSubgroup) ≤ 2^k :=
    (primeRank_le_iff_elementary_card_le _).mp (marked_unitary_rank hk hu) _ inferInstance
  have hupper : (Q Γ a').relIndex (V Γ beta 1) ≤ 2^k :=
    (source_elementary_core_index_le_omega ht d a' (models a') (V Γ beta 1) hVL R).trans hRq
  obtain ⟨_,_,f,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hub : ClassicalGroup.IsPSU (graphLocalGroup Γ beta ⧸
      pCore 2 (graphLocalGroup Γ beta)) 3 (2^k) ∨
      IsSU (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) 3 (2^k) := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      exact Or.inl ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨f.symm.trans e⟩⟩
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      exact Or.inr ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨f.symm.trans e⟩⟩
  have hlarge : 4 ≤ (Q Γ beta).relIndex (V Γ a' 1) := by
    rw [hy]
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  have hEQ : E ≤ Q Γ beta := by
    by_contra hescape
    have hlo := reduced_critical_unitary_residual_square h hc hab hd hb hcomm hk hub
      hlarge E inf_le_left hescape
    have hAC : A ≤ centralizer (E : Set (Reduction.G₀ L S₀)) := le_centralizer_iff.mp inf_le_right
    have hi := relIndex_le_of_le_left hAC (A.subgroupOf (V Γ beta 1)).index_ne_zero_of_finite
    have hi' : (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) ≤
        (Q Γ a').relIndex (V Γ beta 1) := by simpa only [A,inf_relIndex_left] using hi
    have hsq := hlo.trans (hi'.trans hupper)
    have hp : 1 < 2^k := Nat.one_lt_pow (by omega) (by decide)
    nlinarith only [hp,hsq]
  exact le_inf hEQ (source_unitary_core_actor_fixed_of_small_index ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm hn hw hsmall E hEQ inf_le_right)

/-- At the chosen moving center the fixed subgroup is the whole
neighboring-center intersection, with the literal terminal normalizer and
all preceding-core intersection identities. No trapping assumption remains. -/
theorem reduced_double_unitary_fixed_intersection
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    {k n : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
        pCore 2 (graphLocalGroup Γ a')) 3 (2^k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2^k))
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hw : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
        pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n)) :
    let A := V Γ beta 1 ⊓ Q Γ a'
    let C := Z Γ w.val ⊓ centralizer (A : Set (Reduction.G₀ L S₀))
    graphLocalGroup Γ a' ≤ normalizer (C : Set (Reduction.G₀ L S₀)) ∧
      C = neighborCenterIntersection Γ a' ∧
      ∀ z : (graph Γ).neighborSet a', A ≤ Q Γ z.val → C = Z Γ w.val ⊓ Z Γ z.val := by
  have hx := (reduced_double_unitary_core_indices h models hc hab hd hb hcomm hk hn hu w hm hw).1
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have hsmall : (Q Γ a').relIndex (V Γ beta 1) < (2^n)^2 := by rw [hx]; nlinarith only [hq]
  have htrap := (inf_le_inf_right
    (centralizer ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Z_neighbor_le_V Γ w.property)).trans
      ((reduced_double_unitary_fixed_centralizer h models hc hab hd hb hcomm hk hn hu w hm hw).trans inf_le_left)
  exact source_unitary_trapped_fixed_intersection (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedFullEarlierLocalTheorems h)
      hc hab hd hb hcomm models w hm hn hw hsmall htrap

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
