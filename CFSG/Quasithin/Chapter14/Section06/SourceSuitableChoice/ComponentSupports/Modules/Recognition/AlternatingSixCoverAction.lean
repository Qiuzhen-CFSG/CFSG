module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleLinearThree
public import CFSG.Quasithin.ChapterD.Section02.AlternatingSixTypes
public import Theory.Representation.BinaryOffender.AlternatingSixCentralCover
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.Seed
public import Theory.Representation.BinaryConjugationSection.QuotientStabilizer
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The original A₆ support action and fixed-moving lift

For the selected homogeneous support W, the actual actor Mc ∩ N(W)
surjects onto the quotient stabilizer. Its images of K and N_T(W) are
identified literally; when Mc=KT the latter is Sylow. The original W/Z
coordinates intertwine this action. The genuine I.2.3 cover argument
produces one original involution fixed modulo Z by N_T(W) and moved by K,
including the nonsplit five-dimensional cover.

Source: Aschbacher--Smith I.2.3 and14.6.22--24, pp.413,1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The genuine I.2.3 lift on the original homogeneous A₆ support.
The same u is fixed modulo Z by its full Sylow stabilizer and moved by K. -/
theorem source_normal_a6_seed_fixed_moving
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)) :
    let c := originalSection a
    let W := c.subspacePreimage I
    let A := Mc ⊓ normalizer (W : Set G)
    let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
    let π := c.subspaceActorHom a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
    let J := subspaceStabilizer a.representation I
    centralInvolutions T ≤ W ∧ W ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      K ≤ normalizer (W : Set G) ∧ Function.Surjective π ∧
      (K.subgroupOf A).map π = (actorImage Mc K).subgroupOf J ∧
      (S.subgroupOf A).map π = (actorImage Mc S).subgroupOf J ∧
      (∃ d : BinaryConjugationSection A W (centralInvolutions T)
          ((stabilizerRepresentation a.representation I).comp π),
        ∀ w : W, (d.coordinates w).toAdd.val =
          (c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd) ∧
      ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
        (∀ s ∈ S, ⁅u,s⁆ ∈ centralInvolutions T) ∧
        ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hgeo := source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK a hI.isIrrPlus
  let c := originalSection a
  let W := c.subspacePreimage I
  let A := Mc ⊓ normalizer (W : Set G)
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  let J := subspaceStabilizer a.representation I
  let D := actorImage Mc K
  let L := D.subgroupOf J
  let π := c.subspaceActorHom a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
  let τ := stabilizerRepresentation a.representation I
  let : D.Normal := hnK.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  have hSA : S ≤ A := inf_le_inf hout.1.2 le_rfl
  have hKimage : (K.subgroupOf A).map π = L :=
    c.subspaceActorHom_image a.representation (QuotientGroup.mk' (pCore 2 Mc)) I K
  obtain ⟨d,hd⟩ := c.exists_subspaceActorSection a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
  have hp : IsPGroup 2 ((S.subgroupOf A).map π) :=
    ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).map π
  obtain ⟨v,hm,hf⟩ := A6Lift.exists_stabilizer_fixed_moving a.representation D
    hI.isIrrPlus b.groupEquiv b.linearEquiv b.intertwines ((S.subgroupOf A).map π) hp
  have hm' : v ∉ fixed ((τ.comp π).comp (K.subgroupOf A).subtype) := by
    intro hv
    apply hm
    intro k
    let kJ : L := ⟨⟨k,hI.invariant k.property⟩,k.property⟩
    obtain ⟨x,hx,heq⟩ := show kJ.val ∈ (K.subgroupOf A).map π from hKimage.symm ▸ kJ.property
    have hh := hv (⟨x,hx⟩ : K.subgroupOf A)
    change τ (π x) v = v at hh
    rw [heq] at hh
    exact congrArg Subtype.val hh
  obtain ⟨u,hu,huf,hum⟩ := d.exists_fixed_moving_lift K S hSA v
    (fun s hs => hf ⟨π ⟨s,hSA hs⟩,mem_map_of_mem π hs⟩) hm'
  refine ⟨hgeo.1,hgeo.2.1,hgeo.2.2.1,c.subspaceActorHom_surjective a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
    (QuotientGroup.mk'_surjective _), hKimage,
    c.subspaceActorHom_image a.representation (QuotientGroup.mk' (pCore 2 Mc)) I S,
    ⟨d,hd⟩,u,hu,?_,?_,huf,hum⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) u (c.subspacePreimage_le I hu)
  · rintro rfl
    obtain ⟨k,_,hk⟩ := hum
    exact hk (by simp)

/-- The image of the literal N_T(W) is a Sylow of the full quotient
stabilizer. This uses Mc=KT and the original normal component. -/
theorem source_component_seed_sylow_actor
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal) (hgen : K ⊔ (T : Subgroup G) = Mc)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlus a.representation (actorImage Mc K) I) :
    let c := originalSection a
    let W := c.subspacePreimage I
    let A := Mc ⊓ normalizer (W : Set G)
    let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
    let π := c.subspaceActorHom a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
    ∃ S₀ : Sylow 2 (subspaceStabilizer a.representation I),
      (S.subgroupOf A).map π = (S₀ : Subgroup (subspaceStabilizer a.representation I)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let c := originalSection a
  let W := c.subspacePreimage I
  let A := Mc ⊓ normalizer (W : Set G)
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  let π := c.subspaceActorHom a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
  have hKW := (source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK a hI).2.2.1
  have hKA : K ≤ A := le_inf hKM hKW
  have hSA : S ≤ A := inf_le_inf hout.1.2 le_rfl
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  have hgenA : K ⊔ S = A := by
    apply le_antisymm (sup_le hKA hSA)
    intro x hx
    have hp : x ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK,hgen]
      exact hx.1
    obtain ⟨k,hk,t,ht,rfl⟩ := hp
    have htA : t ∈ A := by
      simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem (hKA hk)) hx
    exact (K ⊔ S).mul_mem ((show K ≤ K ⊔ S from le_sup_left) hk) ((show S ≤ K ⊔ S from le_sup_right) ⟨ht,htA.2⟩)
  obtain ⟨R,hR⟩ := intersection_sylow T K hTK
  have hRS : (R : Subgroup K).map K.subtype ≤ S := by
    rintro x ⟨r,hr,rfl⟩
    have ht : r.val ∈ (T : Subgroup G) := show r ∈ (T : Subgroup G).subgroupOf K from hR ▸ hr
    exact ⟨ht,hKW r.property⟩
  obtain ⟨P,hP⟩ := (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).exists_sylow_sup_of_coprime_index
    K S (inf_le_left.trans hTK) (R : Subgroup K) R.not_dvd_index hRS
  have hPs : ∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = S := by
    rw [←hgenA]
    exact ⟨P,hP⟩
  obtain ⟨P,hP⟩ := hPs
  have hPS : (P : Subgroup A) = S.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSA]
  let S₀ := P.mapSurjective (f := π)
    (c.subspaceActorHom_surjective a.representation (QuotientGroup.mk' (pCore 2 Mc)) I
      (QuotientGroup.mk'_surjective _))
  exact ⟨S₀,congrArg (Subgroup.map π) hPS.symm⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
