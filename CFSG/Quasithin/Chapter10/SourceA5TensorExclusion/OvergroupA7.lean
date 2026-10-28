module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.PGroupCore
public import Theory.Representation.BinaryAlternatingSevenControl.TensorFixedObstruction
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.SieveCohomology
public import CFSG.Quasithin.ChapterB.InternalThompsonSevenAction

/-!
# Removing the A₇ actions from the original tensor overgroup

For a normal elementary module W and a full Sylow subgroup P, every P-fixed
vector in W lies in Ω₁(Z(P)). Thus an old component centralizing that omega
center fixes the whole image-Sylow fixed space. Its literal action image has
an A₅ quotient, so the five-free fixed-space centralizers of the two binary
A₇ models exclude both rows.

The four-dimensional consumer recovers the original dimension using the
proved cohomology result. The deleted consumer constructs the full S₇ action
quotient and transports the old component image through the common kernel.
The final selector preserves the four remaining Lie-type action families.
The fully moved module and the old local A₅ image are independent inputs;
this module proves the alternating-group exclusion, not those earlier steps.

Source: Aschbacher–Smith 9.3.7, combined manuscript of 1 March 2004,
printed p.734, using B.5.1 and its literal action coordinates.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] [Finite D] in
private theorem fixedSpace_le_of_omega_centralizes
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H)) :
    fixedSpace (NormalElementaryQuotient.representation W q hq hk) ((P : Subgroup H).map q) ≤
      fixedSpace (NormalElementaryQuotient.representation W q hq hk) (B.map q) := by
  intro v hv
  have hc := (NormalElementaryQuotient.mem_fixedSpace_image W q hq hk (P : Subgroup H) v).mp hv
  have hW : W ≤ (P : Subgroup H) := (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P
  have hΩ : (v.toMul : H) ∈ omegaCenterIn (P : Subgroup H) :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨hW v.toMul.property,hc,
      elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property⟩
  apply (NormalElementaryQuotient.mem_fixedSpace_image W q hq hk B v).mpr
  intro b hb
  exact (hB hb v.toMul hΩ).symm

omit [Finite D] in
private theorem five_dvd_of_alternatingFive_quotient (B : Subgroup D)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : 5 ∣ Nat.card B := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (show 5 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hc]; decide).trans
    (pCore 2 B).card_quotient_dvd_card

/-- The four-dimensional A7 row cannot occur for the actual conjugation
quotient when an A5 section centralizes the original Sylow omega center. -/
theorem source_tensor_no_alternatingSeven_four
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H))
    (N : Subgroup D) [N.Normal] (eN : N ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (Additive W) = 4)
    (eB : ((B.map q) ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5)) : False := by
  let ρ := NormalElementaryQuotient.representation W q hq hk
  have hi := fixedSpace_le_of_omega_centralizes W P B hB q hq hk
  exact BinaryAlternatingSevenControl.normal_actor_sylow_fixedKernel_five_free ρ
    (NormalElementaryQuotient.representation_injective W q hq hk) hd N eN
    (P.mapSurjective hq) (B.map q) (fun b hb v hv => hi hv ⟨b,hb⟩)
    (five_dvd_of_alternatingFive_quotient _ eB)

/-- The deleted-seven row uses a Sylow of the whole S7 quotient. Its
fixed-space centralizer has no A5 section, including the possible outer actor. -/
theorem source_tensor_no_alternatingSeven_deleted
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (q : H →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H))
    (e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7))
    (he : ∀ g v, e (NormalElementaryQuotient.representation W q hq hk g v) =
      BinaryPermutation.naturalRepresentation (Fin 7) g (e v))
    (eB : ((B.map q) ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5)) : False := by
  let ρ := NormalElementaryQuotient.representation W q hq hk
  have hi := fixedSpace_le_of_omega_centralizes W P B hB q hq hk
  apply BinaryPermutation.SevenSylowFixed.natural_sylow_fixedKernel_five_free
    (P.mapSurjective hq) (B.map q) ?_ (five_dvd_of_alternatingFive_quotient _ eB)
  intro b hb v hv
  obtain ⟨w,rfl⟩ := e.surjective v
  have hw : w ∈ fixedSpace ρ ((P : Subgroup H).map q) := by
    intro p
    apply e.injective
    change e (ρ p.val w) = e w
    rw [he]
    exact hv p
  have hbw := hi hw ⟨b,hb⟩
  exact (he b w).symm.trans (congrArg e hbw)

open ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open SourceA5PointFFModels

/-- Exclude the actual B.5.1 four-dimensional alternative on the original
module. Cohomology supplies the original dimension; no head quotient is assumed. -/
theorem source_tensor_exclude_alternatingSevenFour
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (K : Subgroup H) [K.Normal] (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (eB : ((B.map (actionMk W)) ⧸ pCore 2 (B.map (actionMk W))) ≃*
      alternatingGroup (Fin 5))
    (hAN : K.map (actionMk W) ≤ offenderSubgroup (action W))
    (s : MovedSection ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))))
    (hm : moved ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) = ⊤)
    (hi : ChapterB.QuasisimpleSource.ExtensionConsequences.IrreducibleAlternative
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s)
    (eK : ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) ≃*
      alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) : False := by
  have hmodel := alternatingSevenFour_original_model _ _ s hm hi eK hd
  let A := K.map (actionMk W)
  let : A.Normal := (inferInstance : K.Normal).map (actionMk W) (QuotientGroup.mk'_surjective _)
  let eA : A ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe hAN).symm.trans eK
  exact source_tensor_no_alternatingSeven_four W P B hB (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A eA hmodel.2.2 eB

omit [Finite H] [Finite D] in
private noncomputable def imageEquivOfKerEq
    {E : Type*} [Group E] (f : H →* D) (g : H →* E) (he : f.ker = g.ker)
    (B : Subgroup H) : B.map f ≃* B.map g :=
  (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap B) (f.subgroupMap_surjective B)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (show (f.subgroupMap B).ker = (g.subgroupMap B).ker by
      rw [Subgroup.ker_subgroupMap, Subgroup.ker_subgroupMap, he])).trans
    (QuotientGroup.quotientKerEquivOfSurjective (g.subgroupMap B) (g.subgroupMap_surjective B)))

/-- Exclude the actual B.5.1 deleted-seven alternative. The model producer
retains the full S7 quotient, and the old A5 section is transported through
the common literal centralizer kernel. -/
theorem source_tensor_exclude_alternatingSevenDeleted
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (K : Subgroup H) [K.Normal] (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (eB : ((B.map (actionMk W)) ⧸ pCore 2 (B.map (actionMk W))) ≃*
      alternatingGroup (Fin 5))
    (hAN : K.map (actionMk W) ≤ offenderSubgroup (action W))
    (s : MovedSection ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))))
    (hm : moved ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) = ⊤)
    (hi : ChapterB.QuasisimpleSource.ExtensionConsequences.IrreducibleAlternative
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s)
    (m : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W)))
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) : False := by
  have hc := alternatingSevenDeleted_fixedSpace_eq_bot _ _ s hm hi m
  obtain ⟨q,hq,hk,_,eV,heV⟩ := deleted_seven_quotient_coordinates W K hAN s hm hc m
  let d := imageEquivOfKerEq (actionMk W) q ((QuotientGroup.ker_mk' _).trans hk.symm) B
  let e : ((B.map q) ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eB
  exact source_tensor_no_alternatingSeven_deleted W P B hB q hq hk eV heV e

namespace SourceA5TensorExclusion
open ChapterB.SourceInduction.ProjectiveLine
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The four Lie-type action families left by the tensor overgroup sieve. -/
inductive FourWay (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (s : MovedSection ρ L) : Prop
  | linearThree (F : BinaryField) (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField)
      (action : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (faithful : Function.Injective s.action)
      (action : ActionEquiv (s.action.comp L.subtype) (binaryG2 F))
end SourceA5TensorExclusion

/-- Apply both A7 obstructions to the actual six-way B.5 selector. The
remaining inputs are the independently produced fully moved module and
literal old-component A5 image. -/
theorem source_tensor_fourWay_of_sixWay
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (K : Subgroup H) [K.Normal] (B : Subgroup H)
    (hB : B ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (eB : ((B.map (actionMk W)) ⧸ pCore 2 (B.map (actionMk W))) ≃*
      alternatingGroup (Fin 5))
    (hAN : K.map (actionMk W) ≤ offenderSubgroup (action W))
    (s : MovedSection ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))))
    (hm : moved ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) = ⊤)
    (hs : SixWayWithIrreducible ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s) :
    SourceA5TensorExclusion.FourWay ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s := by
  cases hs with
  | linearThree F hf a => exact .linearThree F hf a
  | doubleThree F a => exact .doubleThree F a
  | symplectic F hl hf a => exact .symplectic F hl hf a
  | g2 F hl hf a => exact .g2 F hl hf a
  | alternatingSevenFour hi eK hd =>
    exact (source_tensor_exclude_alternatingSevenFour W P K B hB eB hAN s hm hi eK hd).elim
  | alternatingSevenDeleted hi m =>
    exact (source_tensor_exclude_alternatingSevenDeleted W P K B hB eB hAN s hm hi m).elim
end CFSG.Quasithin.Chapter10
