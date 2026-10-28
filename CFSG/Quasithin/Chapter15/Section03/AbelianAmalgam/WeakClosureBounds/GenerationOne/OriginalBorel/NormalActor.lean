module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.PSL3.UniversalProjection
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearModels

/-!
# The actual normal component in H/O₂(H)

The source comparison restricts H/O₂(H) → H/J to the original component.
Its kernel is the component center by the single-source kernel clause. The
proved perfect-cover calculations for PSL₂, Suzuki, PSU₃, PSL₃ and Sp₄ kill
that center: the two-core excludes two, the original maximal overlap excludes
three, and the concrete cover results exclude every remaining prime. Thus
J=O₂(H), and the component equivalence preserves the marked overlap by the
literal quotient map. No equality n(H)=f or module-classification input enters.

The final applications discharge every group input from the genuine OddModel
normal branch and the original three-prime intersection in 15.3.49(4).

Source: Aschbacher--Smith E.2.2(2), printed pp.215--216, I.1.1--4, pp.407--408,
and the normal-component argument of 15.3.65, printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel.NormalActor
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] {M K T : Subgroup X} {f : ℕ}

/-- Exactly the group inputs used by the component cover calculation. -/
structure Input (M K T : Subgroup X) (f : ℕ) : Prop where
  component : K.IsCComponent
  quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  core_le : pCore 2 X ≤ sourceKernel M
  single : SingleClauses M K T
  exponent_gt_one : 1 < f
  odd : Odd f
  noThree : ¬3 ∣ Nat.card M

variable (h : Input M K T f)
include h

abbrev actorToSource : (X ⧸ pCore 2 X) →* (X ⧸ sourceKernel M) :=
  QuotientGroup.map _ _ (MonoidHom.id X) h.core_le

private theorem actorToSource_image (L : Subgroup X) :
    (MarkedModels.actorImage L).map (actorToSource h) = sourceImage M L := by
  change (L.map _).map _ = L.map _
  rw [map_map]
  rfl

/-- Restrict the original quotient H/O₂(H) → H/J to K's image. -/
def componentToSource : MarkedModels.actorImage K →* sourceImage M K :=
  ((actorToSource h).comp (MarkedModels.actorImage K).subtype).codRestrict _ (by
    intro k
    rw [← actorToSource_image h]
    exact mem_map_of_mem _ k.property)

theorem componentToSource_surjective : Function.Surjective (componentToSource h) := by
  rintro ⟨x,hx⟩
  rw [← actorToSource_image h] at hx
  obtain ⟨k,hk,rfl⟩ := hx
  exact ⟨⟨k,hk⟩,rfl⟩

theorem componentToSource_ker : (componentToSource h).ker = center (MarkedModels.actorImage K) := by
  have hk : (actorToSource h).ker =
      (center (MarkedModels.actorImage K)).map (MarkedModels.actorImage K).subtype := by
    have hm := QuotientGroup.ker_map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) h.core_le
    exact hm.trans (by simpa using h.single.kernel_center)
  ext k
  change componentToSource h k = 1 ↔ _
  rw [Subtype.ext_iff]
  change (k : X ⧸ pCore 2 X) ∈ (actorToSource h).ker ↔ _
  rw [hk]
  constructor
  · rintro ⟨z,hz,he⟩
    exact (Subtype.ext he : z=k) ▸ hz
  · intro hk
    exact ⟨k,hk,rfl⟩

variable [Finite X]

theorem actor_quasisimple : IsQuasisimple (MarkedModels.actorImage K) := by
  let := h.quasisimple
  exact IsQuasisimple.of_mulEquiv (h.component.subnormal.quotientCoreImageEquiv 2)

private theorem actor_twoCore : pCore 2 (MarkedModels.actorImage K) = ⊥ := by
  have hs : (MarkedModels.actorImage K).IsSubnormal :=
    h.component.subnormal.map (QuotientGroup.mk'_surjective _)
  rw [← hs.pCore_subgroupOf 2, pCore_quotient_pCore_eq_bot, bot_subgroupOf]

omit [Finite X] in
private theorem center_order_dvd : Nat.card (center (MarkedModels.actorImage K)) ∣ Nat.card M := by
  have hle : (center (MarkedModels.actorImage K)).map (MarkedModels.actorImage K).subtype ≤ MarkedModels.actorImage M := by
    rw [← h.single.kernel_center]
    exact map_mono M.normalCore_le
  have hd := (card_dvd_of_le hle).trans (card_map_dvd _ _)
  rwa [card_map_of_injective (MarkedModels.actorImage K).subtype_injective] at hd

omit [Finite X] in
private theorem center_no_three : ¬3 ∣ Nat.card (center (MarkedModels.actorImage K)) :=
  fun hd => h.noThree (hd.trans (center_order_dvd h))

private theorem center_no_two : ¬2 ∣ Nat.card (center (MarkedModels.actorImage K)) := by
  intro hd
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (MarkedModels.actorImage K)) 2 hd
  have hc : zpowers (z : MarkedModels.actorImage K) ≤ center (MarkedModels.actorImage K) := zpowers_le.mpr z.property
  let : (zpowers (z : MarkedModels.actorImage K)).Normal := ⟨by
    intro x hx g
    have he := mem_center_iff.mp (hc hx) g
    simpa only [he,mul_inv_cancel_right] using hx⟩
  have hp : IsPGroup 2 (zpowers (z : MarkedModels.actorImage K)) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers,Subgroup.orderOf_coe,pow_one] using hz
  have hle : zpowers (z : MarkedModels.actorImage K) ≤ pCore 2 (MarkedModels.actorImage K) := le_sSup ⟨inferInstance,hp⟩
  rw [actor_twoCore h] at hle
  have he : (z : MarkedModels.actorImage K) = 1 := hle (mem_zpowers _)
  have hez : z = 1 := Subtype.ext he
  simp only [hez,orderOf_one] at hz
  omega

private theorem center_eq_bot_of_prime_support
    (hcover : ∀p : ℕ, p.Prime → p ∣ Nat.card (center (MarkedModels.actorImage K)) → p=2 ∨ p=3) :
    center (MarkedModels.actorImage K) = ⊥ := by
  apply card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  rcases hcover p hp hd with rfl | rfl
  · exact center_no_two h hd
  · exact center_no_three h hd

private def modelCover {Y : Type*} [Group Y] (e : sourceImage M K ≃* Y) :
    PerfectCentralCovering.Cover (MarkedModels.actorImage K) Y where
  toMonoidHom := e.toMonoidHom.comp (componentToSource h)
  surjective := e.surjective.comp (componentToSource_surjective h)
  isPerfect := (actor_quasisimple h).toIsPerfect
  ker_le_center := by
    intro x hx
    have hk : x ∈ (componentToSource h).ker := e.injective (hx.trans e.map_one.symm)
    rwa [componentToSource_ker] at hk

private theorem modelCover_ker {Y : Type*} [Group Y] (e : sourceImage M K ≃* Y) :
    (modelCover h e).toMonoidHom.ker = center (MarkedModels.actorImage K) := by
  rw [← componentToSource_ker h]
  ext x
  exact e.injective.eq_iff' e.map_one

private theorem center_eq_bot_of_cyclic_odd_sylows {Y : Type*} [Group Y] [Finite Y]
    (e : sourceImage M K ≃* Y)
    (hcyclic : ∀(p : ℕ) [Fact p.Prime], p≠2 → ∀S : Sylow p Y, IsCyclic S) :
    center (MarkedModels.actorImage K) = ⊥ := by
  apply card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  by_cases hp2 : p=2
  · exact center_no_two h (hp2 ▸ hd)
  let : Fact p.Prime := ⟨hp⟩
  have hn := (modelCover h e).not_dvd_card_multiplier_of_isCyclic_sylow (hcyclic p hp2)
  change ¬p ∣ Nat.card (modelCover h e).toMonoidHom.ker at hn
  rw [modelCover_ker] at hn
  exact hn hd

private theorem psl2_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2^f)
    (e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    center (MarkedModels.actorImage K) = ⊥ := by
  have hf3 : 3≤f := by
    have hf := h.exponent_gt_one
    obtain ⟨n,hn⟩ := h.odd
    omega
  have hseven : 7≤Nat.card F := by
    rw [hF]
    exact (by decide : 7≤2^3).trans (Nat.pow_le_pow_right (by decide) hf3)
  apply center_eq_bot_of_cyclic_odd_sylows h e
  intro p hp hp2 S
  apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF hseven p hp2 _ S
  rw [hF]
  exact (Nat.coprime_two_right.mpr (hp.out.odd_of_ne_two hp2)).pow_right f

private theorem exchangedModel_center_eq_bot (hm : ExchangedModel M K f) :
    center (MarkedModels.actorImage K) = ⊥ := by
  rcases hm with ⟨F,hF,hfin,hc,_,hcard,e,_⟩ | ⟨m,hm,_,e,_⟩
  · exact psl2_center_eq_bot h hcard e
  · apply center_eq_bot_of_cyclic_odd_sylows h e
    intro p hp hp2 S
    exact suzukiSylow_isCyclic_of_ne_two (by omega) hp2 S

private theorem psu3_center_eq_bot {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F=(2^f)^2)
    (hconj : ∀x,J.conj x=x^(2^f))
    (e : sourceImage M K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    center (MarkedModels.actorImage K) = ⊥ := by
  apply center_eq_bot_of_prime_support h
  intro p hp hd
  by_contra hn
  have hp3 : 3<p := by have := hp.two_le; omega
  have hn := HermitianForm.UniversalCover.EvenKernelBound.LargePrimary.not_dvd_cover_kernel
    J h.exponent_gt_one hp hp3 hF hconj (modelCover h e)
  rw [modelCover_ker] at hn
  exact hn hd

private theorem psl3_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=2^f)
    (e : sourceImage M K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    center (MarkedModels.actorImage K) = ⊥ := by
  have hf3 : 3≤f := by
    have hf := h.exponent_gt_one
    obtain ⟨n,hn⟩ := h.odd
    omega
  have hcard : 8≤Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0<2) hf3
  let c := modelCover h e
  let := c.isPerfect
  obtain ⟨s,hs,_⟩ := Matrix.PSL3.UniversalProjection.existsUnique_projection_lift
    c.toMonoidHom c.surjective c.ker_le_center (by omega) (by omega)
  have hsurj := Matrix.PSL3.projection_lift_surjective F c.toMonoidHom c.ker_le_center s hs
  have hd := kernel_card_dvd_of_surjective_factor (Matrix.PSL3.projection F) c.toMonoidHom s hsurj hs
  have hk := (Matrix.PSL3.projection F).ker_eq_bot_iff.mpr
    (BorelReduction.psl3Projection_injective_of_odd hF h.odd)
  rw [hk,card_bot] at hd
  apply card_eq_one.mp
  rw [← modelCover_ker h e]
  exact Nat.dvd_one.mp hd

private theorem sp4_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=2^f)
    (e : sourceImage M K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    center (MarkedModels.actorImage K) = ⊥ := by
  have hi := (modelCover h e).injective_of_universalProjection_ker_eq_bot
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.universalProjection_ker_eq_bot_of_card_pow
      hF h.exponent_gt_one)
  rw [← modelCover_ker h e]
  exact (modelCover h e).toMonoidHom.ker_eq_bot_iff.mpr hi

/-- The genuine marked source models collapse the component center. -/
theorem center_eq_bot (hm : BenderModel M K f ∨ DiagramModel M K T f) :
    center (MarkedModels.actorImage K) = ⊥ := by
  rcases hm with hm | hm
  · rcases hm with hm | ⟨F,hF,hfin,hc,J,hJ,hf,hcard,hconj,hfix,e,hB⟩
    · exact exchangedModel_center_eq_bot h hm
    · exact psu3_center_eq_bot h J hcard hconj e
  · rcases hm with ⟨F,hF,hfin,hc,hf,hcard,e,hB,hd⟩ | ⟨F,hF,hfin,hc,hf,hcard,e,hB,hd⟩
    · exact psl3_center_eq_bot h hcard e
    · have hq : 2 < Nat.card F := by
        rw [hcard]
        exact (by decide : 2 < 2^2).trans_le
          (Nat.pow_le_pow_right (by decide) (by have := h.exponent_gt_one; omega))
      exact sp4_center_eq_bot h hcard (e.trans
        (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq))

/-- The original source kernel collapses by the same literal quotient map. -/
theorem sourceKernel_eq_twoCore (hm : BenderModel M K f ∨ DiagramModel M K T f) :
    sourceKernel M = pCore 2 X := by
  apply le_antisymm _ h.core_le
  have he : (sourceKernel M).map (QuotientGroup.mk' (pCore 2 X)) = ⊥ := by
    rw [h.single.kernel_center,center_eq_bot h hm,Subgroup.map_bot]
  simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he

/-- The component marking uses the canonical restriction of H/O₂(H) → H/J. -/
def componentEquiv (hm : BenderModel M K f ∨ DiagramModel M K T f) :
    MarkedModels.actorImage K ≃* sourceImage M K :=
  MulEquiv.ofBijective (componentToSource h) ⟨by
    apply (componentToSource h).ker_eq_bot_iff.mp
    rw [componentToSource_ker,center_eq_bot h hm],componentToSource_surjective h⟩

theorem componentEquiv_apply (hm : BenderModel M K f ∨ DiagramModel M K T f)
    (k : MarkedModels.actorImage K) : componentEquiv h hm k = componentToSource h k := rfl

theorem componentEquiv_overlap (hm : BenderModel M K f ∨ DiagramModel M K T f) :
    ((MarkedModels.actorImage (M ⊓ K)).subgroupOf (MarkedModels.actorImage K)).map (componentEquiv h hm).toMonoidHom =
      componentOverlap M K := by
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    change actorToSource h k ∈ sourceImage M (M ⊓ K)
    rw [← actorToSource_image h]
    exact mem_map_of_mem _ hk
  · intro hx
    change (x : X ⧸ sourceKernel M) ∈ sourceImage M (M ⊓ K) at hx
    rw [← actorToSource_image h] at hx
    obtain ⟨k,hk,he⟩ := hx
    have hkK : k ∈ MarkedModels.actorImage K := map_mono inf_le_right hk
    exact ⟨⟨k,hkK⟩,hk,Subtype.ext he⟩

/-- Every source Borel pair is carried to the actor using the same isomorphism. -/
theorem modelBorelPair {Y : Type*} [Group Y] (B : Subgroup Y)
    (hm : BenderModel M K f ∨ DiagramModel M K T f) (hb : ModelBorelPair M K B) :
    ∃e : MarkedModels.actorImage K ≃* Y,
      ((MarkedModels.actorImage (M ⊓ K)).subgroupOf (MarkedModels.actorImage K)).map e.toMonoidHom=B := by
  obtain ⟨e,he⟩ := hb
  refine ⟨(componentEquiv h hm).trans e,?_⟩
  change Subgroup.map (e.toMonoidHom.comp (componentEquiv h hm).toMonoidHom) _ = B
  rw [←map_map,componentEquiv_overlap,he]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel.NormalActor
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {H M : Subgroup G} {K : Subgroup H} {f : ℕ}

/-- Keep the normal source clauses correlated with their genuine marking. -/
theorem OddModel.normal_cases (h : OddModel T H M K f) (hn : K.Normal) :
    SingleClauses (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) ∧
      (BenderModel (M.subgroupOf H) K f ∨
        DiagramModel (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) f) :=
  (h.source_cases.resolve_right (fun he => he.1 hn)).2

/-- The cover argument receives the actual three-prime overlap, without any
hypothesis equating the model exponent to the generation parameter. -/
theorem OddModel.normal_input (h : OddModel T H M K f) (hn : K.Normal)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    NormalActor.Input (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) f := by
  refine ⟨h.component,h.quasisimple,h.core_le,(h.normal_cases hn).1,
    h.exponent_gt_one,h.exponent_odd,?_⟩
  have he := Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : M ⊓ H ≤ H)).toEquiv
  rw [inf_subgroupOf_right] at he
  exact fun hd => hthree (he ▸ hd)

/-- On the literal original normal component, the actor center and source
kernel collapse from the already-proved model covering calculations. -/
theorem OddModel.normal_actor_center (h : OddModel T H M K f) (hn : K.Normal)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    center (MarkedModels.actorImage K) = ⊥ ∧
      BorelReduction.sourceKernel H M = pCore 2 H :=
  ⟨NormalActor.center_eq_bot (h.normal_input hn hthree) (h.normal_cases hn).2,
    NormalActor.sourceKernel_eq_twoCore (h.normal_input hn hthree) (h.normal_cases hn).2⟩

/-- The original component marking now uses the literal representation actor. -/
noncomputable def OddModel.normal_componentEquiv (h : OddModel T H M K f) (hn : K.Normal)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    MarkedModels.actorImage K ≃* sourceImage (M.subgroupOf H) K :=
  NormalActor.componentEquiv (h.normal_input hn hthree) (h.normal_cases hn).2

theorem OddModel.normal_componentEquiv_overlap (h : OddModel T H M K f) (hn : K.Normal)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    ((MarkedModels.actorImage (M.subgroupOf H ⊓ K)).subgroupOf (MarkedModels.actorImage K)).map
        (h.normal_componentEquiv hn hthree).toMonoidHom = componentOverlap (M.subgroupOf H) K :=
  NormalActor.componentEquiv_overlap (h.normal_input hn hthree) (h.normal_cases hn).2

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
