module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupA7
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# The A₇ exclusions on the actual moved Omega submodule

The original normal overcomponent makes its moved subspace invariant under
the whole conjugation quotient. Faithfulness of the classified section embeds
the offender subgroup in the action image on that actual moved space; the
old component therefore retains its A₅ section there. Cohomology splits the
component-fixed complement, so the moved space itself has the original four
or deleted-six coordinates. The complement in the whole Omega orbit remains.

Every vector fixed by the original full Sylow in this invariant moved space
lies in Ω₁Z(P), hence is fixed by the old component. The known five-free
Sylow-fixed centralizers exclude both A₇ models. In the deleted case, the
marked S₇ subgroup and the normal-extension theorem recover the full S₇
actor of the moved space. All maps originate in the original conjugation
action, and the six-way consumer returns the same section and four remaining
Lie-type action markings without a full-movement hypothesis.

Source: Aschbacher–Smith, original 9.3.1 and 9.3.7, printed pp.733–734,
using B.5.1 and the binary A₇ module cohomology calculations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open ChapterB.QuasisimpleSource ChapterB.InternalThompsonAction SourceA5PointFFModels

private def mapEquivOn {Q D : Type*} [Group Q] [Group D]
    (f : Q →* D) (N : Subgroup Q) (hf : Function.Injective (f.comp N.subtype))
    (B : Subgroup Q) (hBN : B ≤ N) : B ≃* B.map f :=
  MulEquiv.ofBijective (f.subgroupMap B) ⟨by
    intro b c h
    have he : (⟨b,hBN b.property⟩ : N) = ⟨c,hBN c.property⟩ :=
      hf (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun x : N => (x : Q)) he), f.subgroupMap_surjective B⟩

variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (N A : Subgroup Q) [A.Normal]
    (hAN : A ≤ N) (s : MovedSection (ρ.comp N.subtype) (A.subgroupOf N))

private def extendedMoved : Subrepresentation ρ where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have he : s.space.toSubmodule = moved ρ A := by
      rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    rw [he] at hv ⊢
    exact (MovedSection.ofNormal ρ A).space.apply_mem_toSubmodule g hv

private theorem extendedMoved_faithful_on
    (hf : Function.Injective s.action) :
    Function.Injective ((extendedMoved ρ N A hAN s).toRepresentation.comp N.subtype) := by
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (s.space.toRepresentation a v) =
      Submodule.Quotient.mk (s.space.toRepresentation b v)
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hab v)

private theorem extendedMoved_image_injective_on
    (hf : Function.Injective s.action) :
    Function.Injective ((actionHom (extendedMoved ρ N A hAN s).toRepresentation).comp N.subtype) := by
  intro a b hab
  apply extendedMoved_faithful_on ρ N A hAN s hf
  exact congrArg (imageRepresentation (extendedMoved ρ N A hAN s).toRepresentation) hab

omit [A.Normal] in
private theorem central_eq_bot
    (hc : IsCompl s.space.toSubmodule (fixedSpace (ρ.comp N.subtype) (A.subgroupOf N))) :
    s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hc.disjoint.le_bot ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩

omit [A.Normal] in
private def projectionEquiv
    (hc : IsCompl s.space.toSubmodule (fixedSpace (ρ.comp N.subtype) (A.subgroupOf N))) :
    s.space.toSubmodule ≃ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
  (s.central.toSubmodule.quotEquivOfEqBot (central_eq_bot ρ N A s hc)).symm

omit [A.Normal] in
private theorem projection_intertwines
    (hc : IsCompl s.space.toSubmodule (fixedSpace (ρ.comp N.subtype) (A.subgroupOf N)))
    (g : N) (v : s.space.toSubmodule) :
    projectionEquiv ρ N A s hc (s.space.toRepresentation g v) =
      s.central.quotientRepresentation g (projectionEquiv ρ N A s hc v) := rfl

private theorem extendedMoved_fixed
    (P : Subgroup Q) (B : Subgroup Q)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v) :
    let τ := (extendedMoved ρ N A hAN s).toRepresentation
    ∀ b ∈ B.map (actionHom τ), ∀ v ∈ fixedSpace (imageRepresentation τ) (P.map (actionHom τ)),
      imageRepresentation τ b v = v := by
  dsimp only
  rintro b ⟨b,hb,rfl⟩ v hv
  apply Subtype.ext
  apply hB b hb v.val
  intro p
  exact congrArg Subtype.val (hv ⟨_,mem_map_of_mem _ p.property⟩)

variable [Finite Q] [FiniteDimensional (ZMod 2) V]

include hAN

private theorem no_four_on_moved
    (P : Sylow 2 Q) (B : Subgroup Q) (hBN : B ≤ N)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v)
    (hfive : 5 ∣ Nat.card B)
    (hi : ExtensionConsequences.IrreducibleAlternative (A.subgroupOf N) s)
    (eA : A.subgroupOf N ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) : False := by
  let τ := (extendedMoved ρ N A hAN s).toRepresentation
  let f := actionHom τ
  have hf := extendedMoved_image_injective_on ρ N A hAN s hi.faithful
  have hc := ExtensionConsequences.alternatingSeven_isCompl s hi eA hd
  have hdim : Module.finrank (ZMod 2) s.space.toSubmodule = 4 :=
    (projectionEquiv ρ N A s hc).finrank_eq.trans hd
  let e : A.map f ≃* alternatingGroup (Fin 7) :=
    (mapEquivOn f N hf A hAN).symm.trans ((subgroupOfEquivOfLe hAN).symm.trans eA)
  let : (A.map f).Normal := (inferInstance : A.Normal).map f τ.asGroupHom.rangeRestrict_surjective
  have hfree := BinaryAlternatingSevenControl.normal_actor_sylow_fixedKernel_five_free
    (imageRepresentation τ) (imageRepresentation_injective τ) hdim (A.map f) e
    (P.mapSurjective τ.asGroupHom.rangeRestrict_surjective) (B.map f)
    (extendedMoved_fixed ρ N A hAN s P B hB)
  have he : Nat.card (B.map f) = Nat.card B :=
    Nat.card_congr (mapEquivOn f N hf B hBN).toEquiv.symm
  exact hfree (he.symm ▸ hfive)

private def deleted_component_action
    (hc : IsCompl s.space.toSubmodule (fixedSpace (ρ.comp N.subtype) (A.subgroupOf N)))
    (m : MarkedActionEquiv s.action (offenderSubgroup s.action) (A.subgroupOf N)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    ActionEquiv ((extendedMoved ρ N A hAN s).toRepresentation.comp A.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) where
  groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans m.subgroupEquiv
  linearEquiv := (projectionEquiv ρ N A s hc).trans m.action.linearEquiv
  intertwines a v := by
    change s.space.toSubmodule at v
    let c : A.subgroupOf N := ⟨⟨a,hAN a.property⟩,a.property⟩
    change m.action.linearEquiv (projectionEquiv ρ N A s hc
      (s.space.toRepresentation (c : N) v)) =
      BinaryPermutation.naturalRepresentation (Fin 7) (m.subgroupEquiv c)
        (m.action.linearEquiv (projectionEquiv ρ N A s hc v))
    rw [projection_intertwines]
    exact (m.action.intertwines ⟨c,m.contained c.property⟩
      (projectionEquiv ρ N A s hc v)).trans
      (congrArg (fun g => BinaryPermutation.naturalRepresentation (Fin 7) g
        (m.action.linearEquiv (projectionEquiv ρ N A s hc v))) (m.compatible c))

private theorem no_deleted_on_moved
    (P : Sylow 2 Q) (B : Subgroup Q) (hBN : B ≤ N)
    (hB : ∀ b ∈ B, ∀ v ∈ fixedSpace ρ P, ρ b v = v)
    (hfive : 5 ∣ Nat.card B)
    (hi : ExtensionConsequences.IrreducibleAlternative (A.subgroupOf N) s)
    (m : MarkedActionEquiv s.action (offenderSubgroup s.action) (A.subgroupOf N)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) : False := by
  let τ := (extendedMoved ρ N A hAN s).toRepresentation
  let f := actionHom τ
  let δ := imageRepresentation τ
  have hf := extendedMoved_image_injective_on ρ N A hAN s hi.faithful
  have hc := ExtensionConsequences.symmetricOdd_isCompl s hi.irrPlus (Or.inr rfl) m
  let a0 := deleted_component_action ρ N A hAN s hc m
  let eA := mapEquivOn f N hf A hAN
  let a : ActionEquiv (δ.comp (A.map f).subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) := {
    groupEquiv := eA.symm.trans a0.groupEquiv
    linearEquiv := a0.linearEquiv
    intertwines x v := by
      obtain ⟨k,rfl⟩ := eA.surjective x
      change a0.linearEquiv (τ k v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 7)
          (a0.groupEquiv (eA.symm (eA k))) (a0.linearEquiv v)
      rw [eA.symm_apply_apply]
      exact a0.intertwines k v }
  have hcard : Nat.card (Equiv.Perm (Fin 7)) ≤ Nat.card (actionImage τ) := calc
    Nat.card (Equiv.Perm (Fin 7)) = Nat.card (offenderSubgroup s.action) :=
      Nat.card_congr m.action.groupEquiv.toEquiv.symm
    _ ≤ Nat.card N := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Nat.card (N.map f) := Nat.card_congr (mapEquivOn f N hf N le_rfl).toEquiv
    _ ≤ Nat.card (actionImage τ) := Nat.card_le_card_of_injective _ Subtype.val_injective
  let : (A.map f).Normal := (inferInstance : A.Normal).map f τ.asGroupHom.rangeRestrict_surjective
  obtain ⟨b,hb⟩ := full_deleted_seven_actor δ (imageRepresentation_injective τ) (A.map f) a hcard
  let S : Sylow 2 (actionImage τ) := P.mapSurjective τ.asGroupHom.rangeRestrict_surjective
  have hfix := extendedMoved_fixed ρ N A hAN s P B hB
  have hfree := BinaryPermutation.SevenSylowFixed.natural_sylow_fixedKernel_five_free
    (S.mapSurjective (f := b.groupEquiv.toMonoidHom) b.groupEquiv.surjective)
    ((B.map f).map b.groupEquiv.toMonoidHom) (by
      rintro _ ⟨g,hg,rfl⟩ v hv
      obtain ⟨w,rfl⟩ := b.linearEquiv.surjective v
      have hw : w ∈ fixedSpace δ (S : Subgroup (actionImage τ)) := by
        intro p
        apply b.linearEquiv.injective
        change b.linearEquiv (δ p.val w) = b.linearEquiv w
        rw [b.intertwines]
        exact hv ⟨b.groupEquiv p,mem_map_of_mem b.groupEquiv.toMonoidHom p.property⟩
      exact (b.intertwines g w).symm.trans (congrArg b.linearEquiv (hfix g hg w hw)))
  rw [card_map_of_injective b.groupEquiv.injective] at hfree
  have he : Nat.card (B.map f) = Nat.card B :=
    Nat.card_congr (mapEquivOn f N hf B hBN).toEquiv.symm
  exact hfree (he.symm ▸ hfive)

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF

namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
open ChapterB.QuasisimpleSource ChapterB.InternalThompsonAction SourceA5PointFFModels
open scoped IsMulCommutative
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem omega_fixed
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (K : Subgroup H)
    (hK : K ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H)) :
    ∀ k ∈ K.map (actionMk W), ∀ v ∈ fixedSpace (action W) ((P : Subgroup H).map (actionMk W)),
      action W k v = v := by
  intro k hk v hv
  have hc := (NormalElementaryQuotient.mem_fixedSpace_image W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (P : Subgroup H) v).mp hv
  have hW : W ≤ (P : Subgroup H) := (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P
  have hΩ : (v.toMul : H) ∈ omegaCenterIn (P : Subgroup H) :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨hW v.toMul.property,hc,
      elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property⟩
  have hfix : v ∈ fixedSpace (action W) (K.map (actionMk W)) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image W (actionMk W)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K v).mpr
    intro a ha
    exact (hK ha v.toMul hΩ).symm
  exact hfix ⟨k,hk⟩

private theorem five_dvd_of_a5_quotient {D : Type*} [Group D]
    (B : Subgroup D) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    5 ∣ Nat.card B := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (show 5 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hc]; decide).trans
    (pCore 2 B).card_quotient_dvd_card

/-- The actual normal overcomponent's moved space excludes both A₇ rows.
The original module may retain a component-fixed summand. In particular this
applies to the original reduced Omega orbit in the nonzero-core line argument. -/
theorem fourWay_of_sixWay
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (P : Sylow 2 H) (J : Subgroup H) [J.Normal] (K : Subgroup H)
    (hKJ : K ≤ J)
    (hKOmega : K ≤ centralizer (omegaCenterIn (P : Subgroup H) : Set H))
    (eK : ((K.map (actionMk W)) ⧸ pCore 2 (K.map (actionMk W))) ≃*
      alternatingGroup (Fin 5))
    (hJN : J.map (actionMk W) ≤ offenderSubgroup (action W))
    (s : MovedSection ((action W).comp (offenderSubgroup (action W)).subtype)
      ((J.map (actionMk W)).subgroupOf (offenderSubgroup (action W))))
    (hs : SixWayWithIrreducible ((action W).comp (offenderSubgroup (action W)).subtype)
      ((J.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s) :
    SourceA5TensorExclusion.FourWay ((action W).comp (offenderSubgroup (action W)).subtype)
      ((J.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) s := by
  let A := J.map (actionMk W)
  let N := offenderSubgroup (action W)
  let : A.Normal := (inferInstance : J.Normal).map (actionMk W) (QuotientGroup.mk'_surjective _)
  have hKN : K.map (actionMk W) ≤ N := (map_mono hKJ).trans hJN
  have hfix := omega_fixed W P K hKOmega
  have hfive := five_dvd_of_a5_quotient _ eK
  cases hs with
  | linearThree F hf a => exact .linearThree F hf a
  | doubleThree F a => exact .doubleThree F a
  | symplectic F hl hf a => exact .symplectic F hl hf a
  | g2 F hl hf a => exact .g2 F hl hf a
  | alternatingSevenFour hi eA hd =>
    exact (no_four_on_moved (action W) N A hJN s
      (P.mapSurjective (QuotientGroup.mk'_surjective _)) _ hKN hfix hfive hi eA hd).elim
  | alternatingSevenDeleted hi m =>
    exact (no_deleted_on_moved (action W) N A hJN s
      (P.mapSurjective (QuotientGroup.mk'_surjective _)) _ hKN hfix hfive hi m).elim

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
