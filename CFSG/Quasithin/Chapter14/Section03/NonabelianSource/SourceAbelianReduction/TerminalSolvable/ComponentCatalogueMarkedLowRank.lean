module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRecognitionReduction
public import CFSG.Quasithin.ChapterG.Section11.NaturalCentralizer
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Recognition of the nonfaithful marked branch with larger fixed space

In the small-actor setting, original 14.3.12 identifies the terminal kernel
with the two-core. Odd-prime ranks therefore descend from the actual point
normalizer. A doubled natural A₆, A₇ or A₈ orbit exhausts the available
three-rank, while its centralizer embeds in S₃. That centralizer must be a
two-group, hence trivial, contradicting the nontrivial constituent kernel.

If the fixed space is larger than the marked line, the same-vector
alternative supplies a rank-one constituent action. G.6.4, self-duality of
the fixed orbit action, and the preceding centralizer exclusion leave the
natural S₅ quotient. Its orbit is A₅; simplicity identifies the original
component with that orbit. The literal image transport then supplies the
local lift and its intrinsic two-core quotient.

The final conditional assembly retains faithful recognition and the two
nonfaithful fixed-line branches. No counterexample to the full G.11.2
catalogue is assumed.

Source: Aschbacher--Smith G.6.4, G.11.8, and 14.3.12--15, printed
pp.345--346,368--369,993--994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
private theorem not_even_core_model {D A U : Type*} [Group D] [Group A]
    [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) (r : A →* D) [IsIrreducible (σ.comp r)]
    (hd : 2 ≤ Module.finrank (ZMod 2) U) (n : ℕ) (hn : 0 < n) (he : Even n)
    (hm : ChapterG.Section06.HasModelOn σ ⊤ ⊤
      (BinaryPermutation.coreRepresentation (Fin n))) : False := by
  obtain ⟨e,c,stable,hc⟩ := hm
  have hOne : BinaryPermutation.allOne (Fin n) ∈ BinaryPermutation.core (Fin n) := by
    change BinaryPermutation.augmentation (Fin n) (BinaryPermutation.allOne (Fin n)) = 0
    rw [BinaryPermutation.augmentation_allOne,Fintype.card_fin]
    obtain ⟨k,hk⟩ := he
    rw [hk,Nat.cast_add,← two_mul,show (2 : ZMod 2) = 0 by decide,zero_mul]
  let u : BinaryPermutation.core (Fin n) := ⟨BinaryPermutation.allOne (Fin n),hOne⟩
  have hu : u ≠ 0 := by
    intro hz
    have hh := congrArg (fun w : BinaryPermutation.core (Fin n) => w.val ⟨0,hn⟩) hz
    exact (by decide : (1 : ZMod 2) ≠ 0) hh
  let w : U := (c.symm u).val
  have hw (k : A) : σ (r k) w = w := by
    have hh := hc ⟨r k,mem_top _⟩ (c.symm u)
    rw [c.apply_symm_apply] at hh
    have huFix (t : Equiv.Perm (Fin n)) : BinaryPermutation.coreRepresentation (Fin n) t u = u := by
      apply Subtype.ext
      exact BinaryPermutation.permute_allOne (Fin n) t
    rw [huFix] at hh
    exact congrArg Subtype.val (c.injective (hh.trans (c.apply_symm_apply u).symm))
  have hw0 : w = 0 := by
    have hmem : w ∈ Representation.OneCohomology.fixed (σ.comp r) := hw
    rw [Representation.OneCohomology.fixed_eq_bot_of_irreducible_finrank (σ.comp r) hd] at hmem
    exact hmem
  apply hu
  have hw' : c.symm u = 0 := Subtype.ext hw0
  simpa only [c.apply_symm_apply,map_zero] using congrArg c hw'

variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- Original 14.3.12 makes the terminal quotient retain each odd-prime rank bound. -/
theorem terminal_odd_prime_rank {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p F.TerminalHdot ≤ 2 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d s.nonabelian
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor).2.2.2.2
  have hk2 : IsPGroup 2 F.terminalHatAction.ker := hk ▸ pCore_isPGroup
  exact (primeRank_quotient_le_of_isTwoGroup p hp F.terminalHatAction.ker hk2).trans
    ((Recognition.pointNormalizer_sqtk s.simple F (by decide)).stronglyQuasithin p
      Fact.out hp)

/-- A nontrivial marked actor kernel excludes the doubled natural A₆--A₈ rows. -/
theorem not_doubled_natural_six_seven_eight
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (n : ℕ) (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hmodel : ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)))) : False := by
  let H := componentOrbit L ⊤
  let C := centralizer (H : Set F.TerminalHdot)
  have hm := hmodel
  obtain ⟨e,_,_⟩ := hmodel
  have hd : Disjoint H C := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    have haz : (⟨a,ha.1⟩ : H) ∈ center H := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (ha.2 k k.property)
    have hez := (Subgroup.centerCongr e ⟨⟨a,ha.1⟩,haz⟩).property
    change e ⟨a,ha.1⟩ ∈ center (alternatingGroup (Fin n)) at hez
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega),mem_bot] at hez
    exact congrArg Subtype.val (e.injective (hez.trans e.map_one.symm))
  have hc : H ≤ centralizer (C : Set F.TerminalHdot) := by
    intro k hk c hc
    exact (hc k hk).symm
  have hr := (primeRank_subgroup_le 3 (H ⊔ C)).trans (s.terminal_odd_prime_rank (by decide))
  rw [H.primeRank_sup_eq_add_of_disjoint_commuting C hd hc 3] at hr
  have hH : 2 ≤ primeRank 3 H := by
    rw [primeRank_equiv 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by omega)
  have hC3 : ¬ 3 ∣ Nat.card C :=
    PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 3 C = 0)
  obtain ⟨j,hj⟩ := ChapterG.Section11.natural_centralizer_embedding
    F.terminalRepresentation s.hypothesis.faithful H n hm hn
  have hdiv : Nat.card C ∣ 6 := by
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using
      (Subgroup.card_dvd_of_injective j hj)
  have hdiv2 : Nat.card C ∣ 2 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    interval_cases hc : Nat.card C <;> norm_num at *
  have hcp : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdiv2)
  have htop : (⊤ : Subgroup C) ≤ pCore 2 C := by
    apply le_sSup
    exact ⟨inferInstance,hcp.to_subgroup ⊤⟩
  rw [s.centralizer_twoCore_eq_bot] at htop
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (s.actor_centralizer_ne_bot hk)
  have hz : (⟨a.val,a.property.2⟩ : C) = 1 := htop (mem_top _)
  exact ha (Subtype.ext (congrArg (fun z : C => (z : F.TerminalHdot)) hz))


private theorem smallComponentImage_of_orbit_five
    (e : componentOrbit L ⊤ ≃* alternatingGroup (Fin 5)) : SmallComponentImage L := by
  let H := componentOrbit L ⊤
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup H := e.isSimpleGroup
  have hLH := le_componentOrbit L (⊤ : Subgroup F.TerminalHdot)
  have heq : L = H := by
    rcases s.component.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup H) with hb | ht
    · have he := congrArg (Subgroup.map H.subtype) hb
      rw [map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] at he
      exact (s.moved (by rw [he,commutator_bot_left])).elim
    · exact le_antisymm hLH (subgroupOf_eq_top.mp ht)
  exact Or.inl ⟨(MulEquiv.subgroupCongr heq).trans e⟩

/-- The low-displacement nonfaithful branch recognizes the original component.
G.6.4 is applied on the literal constituent quotient, and its only surviving
row identifies the component with A₅. -/
theorem smallComponentImage_of_not_actorFaithful_of_fixedSpace_ne_point
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) ≠
      Submodule.span (ZMod 2) {v}) : SmallComponentImage L := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := s.component.orbit_isPerfect ⊤
  let σ := MarkedAction.action F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes
  obtain ⟨a,_,_,_,_,hc⟩ := s.constituent_rankOne_classification_of_fixedSpace_ne_point hk hfix
  have hdual := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2.1
  have hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v X := by
    obtain ⟨b,_,hr,hv⟩ := s.fixedPointAlternative.resolve_left hfix
    exact ⟨b,b.property,hr,hv⟩
  change ChapterG.Section06.Conclusion (kerRepresentation σ)
    (QuotientGroup.mk' σ.ker ⟨a,(show X ≤ H ⊔ X from le_sup_right) a.property⟩) at hc
  rcases hc.1 with ⟨_,hm,ht⟩ | htwo
  · rw [ht] at hm
    rcases hm with ⟨n,_,_,hmodel⟩ | ⟨n,hn5,hn8,hmodel⟩ | ⟨n,hn,hmodel⟩
    · exact (ChapterG.Section11.not_linear_model_of_selfDual_constituent
        F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes
        (by have := s.dimension_gt_two; omega) hdual n hmodel).elim
    · have hd := ChapterG.Section11.proper_marked_natural_quotient_double s.hypothesis
        ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩ hw s.actor_normalSylow
        s.nonsolvable s.component s.moved s.selected.isIrrPlus s.point_mem
        (s.constituent_ne_top_of_not_actorFaithful hk) n hn5 hmodel
      by_cases he : n = 5
      · subst n
        obtain ⟨e,_,_⟩ := hd
        exact s.smallComponentImage_of_orbit_five e
      · exact (s.not_doubled_natural_six_seven_eight hk n (by omega) hd).elim
    · let r := (QuotientGroup.mk' σ.ker).comp
        (Subgroup.inclusion (show H ≤ H ⊔ X from le_sup_left))
      let : IsIrreducible ((kerRepresentation σ).comp r) := s.irreducible
      exact (not_even_core_model (kerRepresentation σ) r (by have := s.dimension_gt_two; omega)
        n (by rcases hn with rfl | rfl <;> decide)
        (by rcases hn with rfl | rfl <;> decide) hmodel).elim
  · obtain ⟨d⟩ := htwo
    let r := (QuotientGroup.mk' σ.ker).comp
      (Subgroup.inclusion (show H ≤ H ⊔ X from le_sup_left))
    have hi : IsIrreducible ((kerRepresentation σ).comp r) := s.irreducible
    exact (ChapterG.Section11.not_twoFactors_of_perfect_irreducible (kerRepresentation σ)
      (kerRepresentation_faithful σ) r hi _ d).elim

/-- The recognized small image supplies the actual local lift and component row. -/
theorem local_lift_of_not_actorFaithful_of_fixedSpace_ne_point
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) ≠
      Submodule.span (ZMod 2) {v}) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_smallComponentImage
    (s.smallComponentImage_of_not_actorFaithful_of_fixedSpace_ne_point hk hfix))

/-- The original local lift now requires nonfaithful recognition only when
the fixed space is exactly the marked line. The three remaining recognition
premises are not asserted here. -/
theorem local_lift_of_fixedLine_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases)
    (htwo : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I →
      Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2 →
      Module.finrank (ZMod 2) I =
        Module.finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
          (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
            (F.terminalDot (F.X g)))) + 2 →
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} →
      SmallComponentImage L)
    (hhigher : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat) →
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} → SmallComponentImage L) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  apply s.local_lift_of_image_cases
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · exact hfaithful hf s.fixedPointAlternative
  · by_cases hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v}
    · apply s.imageCases_of_smallComponentImage
      rcases s.constituent_dimension_cases_of_not_actorFaithful hf with hd | hd
      · exact htwo hf hd (s.actor_kernel_card_two_of_double_dimension hf hd)
          (s.actor_quotient_dimension_of_double_dimension hf hd) hfix
      · exact hhigher hf hd hfix
    · exact s.imageCases_of_smallComponentImage
        (s.smallComponentImage_of_not_actorFaithful_of_fixedSpace_ne_point hf hfix)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
