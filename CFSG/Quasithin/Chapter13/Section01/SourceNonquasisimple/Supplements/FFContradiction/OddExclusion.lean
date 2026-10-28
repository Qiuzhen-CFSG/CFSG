module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.RepeatedProduct
public import Theory.Representation.NormalElementaryQuotient.CommonChief
public import Theory.Representation.BinaryOffender.GeneratedActor
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddChief

/-!
# Exclusion of the larger odd-prime escaping branch

The literal order-d subgroup constructed in the hat image lifts to a
normalized two-perfect subgroup of K. Its common chief section has a faithful
canonical factor and a moving prime-order factor. Restrict the section to
K̂_B Â and pull back its action along the commuting product with L̂_R.
Clifford theory supplies repeated coordinates, and noncommutativity of the
faithful canonical action forces multiplicity greater than one. The proved
rank bound and B.2.4 then give the FF inequality, contradicting B.5.6.

The original outside maximal-two-local application now retains only the
actual A₅, L₃(2), and cyclic-three quotient models. It constructs K = Y,
K = [K,J], the moving Thompson actor and the common chief section. Selection
of the controlled Thompson index, the surviving tensor action and its final
generation contradiction remain with qt-d-1319-ff-contradiction; the earlier
canonical-star and source inputs remain with qt-d-1317-supplements and
qt-d-1317-source. No FF bound, repeated-coordinate marking, or odd-branch
exclusion is an extra premise.

Source: Aschbacher--Smith, proof of 13.1.9, printed pp.870--871, through (*).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddSection
universe u
variable {Q V : Type u} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]

private def restrictSubrep {F E : Subgroup Q} (hEF : E ≤ F)
    {ρ : Representation (ZMod 2) Q V} (W : Subrepresentation (ρ.comp F.subtype)) :
    Subrepresentation (ρ.comp E.subtype) where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule e _v hv := W.apply_mem_toSubmodule (inclusion hEF e) hv

private theorem commuting_product_surjective (S E : Subgroup Q)
    (hc : ⁅S,E⁆ = ⊥) :
    ∃ f : (E × S) →* ↥(S ⊔ E), Function.Surjective f ∧
      (∀ e, f (e,1) = inclusion le_sup_right e) ∧
      (∀ s, f (1,s) = inclusion le_sup_left s) := by
  let iE := inclusion (show E ≤ S ⊔ E from le_sup_right)
  let iS := inclusion (show S ≤ S ⊔ E from le_sup_left)
  have hcomm : ∀ e s, Commute (iE e) (iS s) := by
    intro e s
    apply Subtype.ext
    exact commutator_eq_bot_iff_le_centralizer.mp hc s.property e e.property
  let f := iE.noncommCoprod iS hcomm
  refine ⟨f,?_,?_,?_⟩
  · apply MonoidHom.range_eq_top.mp
    have hfr : f.range = iE.range ⊔ iS.range :=
      MonoidHom.noncommCoprod_range iE iS hcomm
    rw [hfr]
    apply Subgroup.map_injective (S ⊔ E).subtype_injective
    rw [Subgroup.map_sup,←MonoidHom.range_comp,←MonoidHom.range_comp]
    change E.subtype.range ⊔ S.subtype.range = _
    rw [range_subtype,range_subtype,←MonoidHom.range_eq_map,range_subtype,sup_comm]
  · intro e
    apply Subtype.ext
    exact mul_one _
  · intro s
    apply Subtype.ext
    exact one_mul _

/-- The literal common chief section supplies the product action needed by
Clifford's theorem and the repeated-coordinate FF exclusion. -/
theorem productData_of_commonChief
    {ρ : Representation (ZMod 2) Q V} {S P A : Subgroup Q}
    {support : Submodule (ZMod 2) V} (c : CommonChief.Data ρ S P A support)
    (hc : ⁅S,P ⊔ A⁆ = ⊥) (hPA : A ≤ normalizer (P : Set Q))
    (hgen : ⁅P,A⁆ = P) (hA : IsPGroup 2 A) (hr : rank A ≤ 2)
    (hnon : ¬ IsMulCommutative S)
    (hfaith : Function.Injective ((sectionRepresentation
      (ρ.comp (CommonChief.actorGroup S P A).subtype) c.lower c.upper).comp
        (inclusion (show S ≤ CommonChief.actorGroup S P A from le_sup_left))))
    {d : ℕ} (hd : d.Prime) (hd3 : 3 < d) (hp : IsPGroup d P) :
    Nonempty (ProductData ρ A) := by
  let E := P ⊔ A
  let F := CommonChief.actorGroup S P A
  have hEF : E ≤ F := le_sup_right
  let N := restrictSubrep hEF c.lower
  let W := restrictSubrep hEF c.upper
  let σ := sectionRepresentation (ρ.comp F.subtype) c.lower c.upper
  let τ := sectionRepresentation (ρ.comp E.subtype) N W
  have hτ : ∀ e v, τ e v = σ (inclusion hEF e) v := by
    intro e v
    refine Submodule.Quotient.induction_on _ v ?_
    intro w
    rfl
  obtain ⟨f,hf,hleft,hright⟩ := commuting_product_surjective S E hc
  let δ := σ.comp f
  have hi : IsIrreducible δ := (irreducible_comp_surjective_iff f hf σ).mpr c.irreducible
  have hfirst : ∀ e v, δ (e,1) v = τ e v := by
    intro e v
    change σ (f (e,1)) v = _
    rw [hleft]
    exact (hτ e v).symm
  have hnoncomm : ∃ a b : S, δ (1,a*b) ≠ δ (1,b*a) := by
    by_contra! hall
    apply hnon
    exact ⟨⟨fun a b => by
      apply hfaith
      have hh := hall a b
      change σ (f (1,a*b)) = σ (f (1,b*a)) at hh
      rw [hright,hright] at hh
      exact hh⟩⟩
  have hmove : RepeatedSectionBudget.actor ρ E A N W ≠ ⊥ := by
    intro hz
    apply c.movedSection.actor_ne_bot_of_generated hgen
    apply bot_unique
    rintro _ ⟨a,ha,rfl⟩
    have he : actionHom τ ⟨a.val,(show A ≤ E from le_sup_right) ha⟩ = 1 :=
      mem_bot.mp (hz ▸ mem_map_of_mem (actionHom τ) (show (⟨a.val,(show A ≤ E from le_sup_right) ha⟩ : E) ∈ A.subgroupOf E from ha))
    apply mem_bot.mpr
    apply (actionHom_eq_one_iff σ a).mpr
    intro v
    have hh := (actionHom_eq_one_iff τ _).mp he v
    exact (hτ ⟨a.val,(show A ≤ E from le_sup_right) ha⟩ v).symm.trans hh
  let P₀ := P.subgroupOf E
  let : P₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hPA)
  have hp₀ : IsPGroup d P₀ := hp.of_equiv (subgroupOfEquivOfLe (show P ≤ E from le_sup_left)).symm
  have hquot : IsPGroup 2 (E ⧸ P₀) :=
    isPGroup_quotient_of_sup_eq_top P₀ (A.subgroupOf E) hA.comap_subtype (by
      rw [←subgroupOf_sup (show P ≤ E from le_sup_left) (show A ≤ E from le_sup_right)]
      exact subgroupOf_self E)
  exact ⟨{
    overgroup := E
    actor_le := le_sup_right
    actor_rank := hr
    lower := N
    upper := W
    lower_le_upper := c.lower_le_upper
    Factor := S
    action := δ
    irreducible := hi
    first_action := hfirst
    noncommuting := hnoncomm
    moves := hmove
    oddSubgroup := P₀
    prime := d
    prime_prime := hd
    prime_gt_three := hd3
    odd_group := hp₀
    two_quotient := hquot }⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddSection

open Subgroup Stellmacher Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02.Adequate Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem canonical_hat_not_commutative (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j) :
    ¬ IsMulCommutative (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L)) := by
  let S := canonicalSupplement (T : Subgroup G) L
  let F := commonGroup (T : Subgroup G) L Y j
  let : Group.IsPerfect S := mem_L_isPerfect (canonical_frattini_geometry h hmany hL hn).1.1
  let : Group.IsPerfect (S.subgroupOf F) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe (show S ≤ F from le_sup_left)).symm.toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ F from le_sup_left)).symm.surjective
  let : Group.IsPerfect (hatImage (T : Subgroup G) L Y j S) :=
    Group.IsPerfect.map (H := S.subgroupOf F) (hatMap (T : Subgroup G) L Y j)
  let : Nontrivial (hatImage (T : Subgroup G) L Y j S) :=
    (nontrivial_iff_ne_bot _).mpr ha.canonical_nontrivial
  exact Group.IsPerfect.not_isMulCommutative _

/-- The constructed odd prime line is impossible in the literal candidate:
its common chief section has repeated coordinates and the source FF bound,
contradicting the proved B.5.6 odd-prime exclusion. -/
theorem odd_hat_prime_line_false (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j d : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j) (hj : j ≤ 1)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (b : OddHatPrimeLine (T : Subgroup G) L Y A j d) (hd : d.Prime) (hd3 : 3 < d)
    (hp : IsPGroup d (XiQuotient Y)) (he : Monoid.exponent (XiQuotient Y) = d)
    (hclass : Group.nilpotencyClass (XiQuotient Y) ≤ 2) : False := by
  let : Fact d.Prime := ⟨hd⟩
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  obtain ⟨c⟩ := odd_hat_chief h hmany hL hn w hTH hAH hTL ha b hd (by omega)
  let Shat := hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L)
  let Khat := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  let Ahat := hatImage (T : Subgroup G) L Y j A
  let Rhat := hatImage (T : Subgroup G) L Y j
    (thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer (T : Subgroup G) L)
  let F := commonGroup (T : Subgroup G) L Y j
  let := hat_commutator_normal w hTH hAH hTL j
  have hPR : b.subgroup ≤ Rhat := b.contained.trans
    ((commutator_le_left Khat Ahat).trans (map_mono (subgroupOf_mono F le_sup_left)))
  have hAR : Ahat ≤ Rhat := map_mono (subgroupOf_mono F (hA.1.trans le_sup_right))
  have hc : ⁅Shat,b.subgroup ⊔ Ahat⁆ = ⊥ := bot_unique
    ((commutator_mono le_rfl (sup_le hPR hAR)).trans ha.commute.le)
  have hr := odd_hat_actor_rank h w hH hTH hAH hTL hcore ha hA hd (by omega) hp he hclass
  have hAp : IsPGroup 2 Ahat := (ha.actor_bound A hA hAn).1.2.isPGroup
  have hBp : IsPGroup d b.subgroup := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using b.card)
  obtain ⟨p⟩ := OddSection.productData_of_commonChief c.chief hc b.normalized b.generated
    hAp hr (canonical_hat_not_commutative h hmany hL hn ha) (c.canonical_faithful ha) hd hd3 hBp
  obtain ⟨s⟩ := p.exists_repeated
  exact common_action_excludes_odd_section h w hH hTH hAH hTL ha hj hA hAn s

/-- The actual candidate's large odd-prime alternative is excluded; the
remaining branch has K=Y and the constructed common chief section. -/
theorem candidate_common_chief_nonodd (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          thompsonCommutator (T : Subgroup G) L Y j =
            ⁅thompsonCommutator (T : Subgroup G) L Y j,
              thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j⁆ ∧
          (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
            ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∨
            Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3))) ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j ∧
            Nonempty (CommonHatChief (T : Subgroup G) L Y A j) := by
  obtain ⟨Y,w,n,e,ha,_,A,hA,hmove,hAn,hAb,hcase⟩ :=
    candidate_common_moving_actor h hmany hs hrig hclass hL hn hH hTH hne hC hAC hN
  let := n
  let := e
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  have hsmall : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∨
      Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3)) := by
    rcases w.refined with ⟨_,_,_,ha5 | hl3⟩ | ⟨_,hc3⟩ | ⟨_,d,hd,hd3,hp,he,hc⟩
    · exact Or.inl ha5
    · exact Or.inr (Or.inl hl3)
    · exact Or.inr (Or.inr hc3)
    · obtain ⟨b⟩ := odd_hat_prime_line h w hH hTH (hAC.trans hC.1) hTL hcore
        ha hA hmove hd hd3 hp he
      exact (odd_hat_prime_line_false h hmany hL hn w hH hTH (hAC.trans hC.1) hTL
        ha hj hA hAn b hd hd3 hp he hc).elim
  rcases hcase with ⟨hKY,c⟩ | ⟨_,d,hd,hd3,hp,he,hc,_,⟨b⟩⟩
  · refine ⟨Y,w,n,e,ha,hKY,?_,hsmall,A,hA,hAn,hAb,c⟩
    conv_rhs => rw [hKY]
    rfl
  · exact (odd_hat_prime_line_false h hmany hL hn w hH hTH (hAC.trans hC.1) hTL
      ha hj hA hAn b hd hd3 hp he hc).elim
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
