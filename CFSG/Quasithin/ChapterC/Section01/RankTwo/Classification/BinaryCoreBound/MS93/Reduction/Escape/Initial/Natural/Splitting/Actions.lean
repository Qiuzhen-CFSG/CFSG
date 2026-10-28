module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Elementary
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# Conjugation on the radius quotient and its radical quotient

For normal local subgroups H and N, the literal quotient H/N carries the
ambient conjugation action. Its displacement image has order [ [H,T] :
[H,T] ∩ N ]. Passing to D = N[H,Q] gives an elementary quotient and an
action of the specified SL₃(2) quotient, with the exact conjugation formula.
These constructions prepare the dual-module recognition step; they assert
neither faithfulness nor natural-module recognition.

Source: Meierfrankenfeld--Stellmacher (1993), notation p.881 and the
application of (1.4)--(1.5) in (4.3.1)(iii), p.883.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting

variable {A : Type*} [Group A] (H N : Subgroup A) [H.Normal] [N.Normal]

private theorem exists_quotientAction : ∃ ρ : A →* MulAut (H ⧸ N.subgroupOf H),
    ∀ (g : A) (v : H), ρ g (QuotientGroup.mk' (N.subgroupOf H) v) =
      QuotientGroup.mk' (N.subgroupOf H)
        ⟨g * (v : A) * g⁻¹, (inferInstance : H.Normal).conj_mem v v.property g⟩ := by
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action ⊤ H N
    le_normalizer_of_normal le_normalizer_of_normal inferInstance
  refine ⟨ρ.comp (topEquiv.symm.toMonoidHom), ?_⟩
  intro g v
  exact hρ ⟨g, mem_top g⟩ v

noncomputable def quotientAction : A →* MulAut (H ⧸ N.subgroupOf H) :=
  (exists_quotientAction H N).choose

theorem quotientAction_apply (g : A) (v : H) :
    quotientAction H N g (QuotientGroup.mk' (N.subgroupOf H) v) =
      QuotientGroup.mk' (N.subgroupOf H)
        ⟨g * (v : A) * g⁻¹, (inferInstance : H.Normal).conj_mem v v.property g⟩ :=
  (exists_quotientAction H N).choose_spec g v

theorem quotientAction_kills (Q : Subgroup A) (hQ : ⁅H, Q⁆ ≤ N) :
    Q ≤ (quotientAction H N).ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  ext w
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) w
  rw [quotientAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change g * (v : A) * g⁻¹ / (v : A) ∈ N
  have hc : ⁅g, (v : A)⁆ ∈ N := by
    rw [commutator_comm] at hQ
    exact hQ (commutator_mem_commutator hg v.property)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hc

theorem quotientAction_displacement_card [Finite A] (T : Subgroup A) :
    Nat.card (commutatorAction (T.map (quotientAction H N)) (H ⧸ N.subgroupOf H)) =
      N.relIndex ⁅H, T⁆ := by
  let ρ := (quotientAction H N).comp (topEquiv.toMonoidHom)
  have hm : (T.subgroupOf (⊤ : Subgroup A)).map ρ = T.map (quotientAction H N) := by
    change (T.subgroupOf (⊤ : Subgroup A)).map ((quotientAction H N).comp topEquiv.toMonoidHom) = _
    rw [← map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, mem_top x⟩, hx, rfl⟩
  have h := quotient_conjugation_commutatorAction_card ⊤ H N T
    le_normalizer_of_normal le_top inferInstance ρ
    (fun g v => quotientAction_apply H N g v)
  rwa [hm] at h

variable (Q : Subgroup A) [Q.Normal]

instance radical_normal : (radicalPreimage Q H N).Normal := by
  unfold radicalPreimage
  infer_instance

noncomputable def radicalProjection :
    (H ⧸ N.subgroupOf H) →*
      (H ⧸ (radicalPreimage Q H N).subgroupOf H) :=
  QuotientGroup.map _ _ (MonoidHom.id H) (by
    intro x hx
    exact (show N ≤ radicalPreimage Q H N from le_sup_left) hx)

theorem radicalProjection_surjective : Function.Surjective (radicalProjection H N Q) := by
  intro w
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective ((radicalPreimage Q H N).subgroupOf H) w
  exact ⟨QuotientGroup.mk' (N.subgroupOf H) v, rfl⟩

theorem radical_elementary [IsElementaryAbelian 2 (H ⧸ N.subgroupOf H)] :
    IsElementaryAbelian 2 (H ⧸ (radicalPreimage Q H N).subgroupOf H) :=
  IsElementaryAbelian.of_surjective (radicalProjection H N Q)
    (radicalProjection_surjective H N Q)

variable (π : A →* SL) (hπ : Function.Surjective π) (hker : π.ker = Q)

noncomputable def headAction : SL →* MulAut (H ⧸ (radicalPreimage Q H N).subgroupOf H) :=
  π.liftOfSurjective hπ ⟨quotientAction H (radicalPreimage Q H N), by
    rw [hker]
    exact quotientAction_kills H (radicalPreimage Q H N) Q le_sup_right⟩

theorem headAction_apply (g : A) (v : H) :
    headAction H N Q π hπ hker (π g)
      (QuotientGroup.mk' ((radicalPreimage Q H N).subgroupOf H) v) =
    QuotientGroup.mk' ((radicalPreimage Q H N).subgroupOf H)
      ⟨g * (v : A) * g⁻¹, (inferInstance : H.Normal).conj_mem v v.property g⟩ := by
  unfold headAction
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  exact quotientAction_apply H (radicalPreimage Q H N) g v

/-- The quotient action agrees with the descended action after the marking. -/
theorem headAction_comp :
    (headAction H N Q π hπ hker).comp π = quotientAction H (radicalPreimage Q H N) := by
  ext g
  unfold headAction
  rw [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]

/-- Enlarging the actor enlarges its actual displacement subgroup. -/
theorem displacement_mono {E : Type*} [Group E] {J K : Subgroup (MulAut E)}
    (h : J ≤ K) : commutatorAction J E ≤ commutatorAction K E := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, v, rfl⟩
  exact ⟨⟨g, h g.property⟩, v, rfl⟩

/-- The actor is an actual nonidentity involution of SL₃(2), and the
bound concerns its displacement on the specified module. -/
@[expose] def HasSmallInvolution {E : Type*} [Group E] (ρ : SL →* MulAut E) : Prop :=
  ∃ t : SL, t ≠ 1 ∧ t ^ 2 = 1 ∧ Nat.card (commutatorAction (zpowers (ρ t)) E) ≤ 2

/-- The recognition output on a literal module. Both summands are intrinsic:
the action commutator and the fixed subgroup. The coordinates intertwine
conjugation with one marking of the matrix natural representation. -/
structure NaturalActionSplitting {E : Type*} [Group E] (ρ : SL →* MulAut E) where
  marking : SL ≃* SL
  coordinates : commutatorAction ρ.range E ≃* Multiplicative (Fin 3 → ZMod 2)
  decomposition : commutatorAction ρ.range E ⊔ FixedPoints.subgroup ρ.range E = ⊤
  disjoint : Disjoint (commutatorAction ρ.range E) (FixedPoints.subgroup ρ.range E)
  action : ∀ (g : SL) (v w : commutatorAction ρ.range E),
    (w : E) = ρ g (v : E) →
    (coordinates w).toAdd = (marking g).val.mulVec (coordinates v).toAdd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
