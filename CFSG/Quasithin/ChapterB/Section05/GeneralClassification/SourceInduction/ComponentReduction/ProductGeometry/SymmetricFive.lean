module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.Supplements
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryAlternatingFiveNormalizer

/-!
# The marked symmetric-five branch of B.5.10

Let W=[V,L], with the actual LA-action identified with the natural binary
S₅-action and L marked as A₅. Vanishing of H¹(A₅,W), together with the
absence of A₅-fixed vectors in W, gives V=W ⊕ C_V(L), the splitting used
in the source's projective-module argument. The given supplement by C_V(A)
then forces A to centralize C_V(L).

We transport the whole ambient action on W through the same intertwiner.
Normality of L puts that action in the genuine normalizer of the A₅ image;
the proved single-copy normalizer theorem identifies it with the S₅ image.
Thus LA covers the ambient action on W. Faithfulness on V and the direct
sum give the literal identity LA=C_G(C_V(L)), hence ambient normality.
The faithful centerless LA-action and full action-image coverage discharge
all the premises of the existing product constructor.

The final theorem uses only premises supplied by the symmetricFive
constructor and FFHypothesis, with genuine ambient normality of L. No
additional localization, splitting, centralization or product premise remains.
The minimality and order-two facts from B.5.9 are not needed for this step.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.10,
printed pp.108–109; the natural-module cohomology is I.1.6(1), printed p.408.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry

private theorem naturalFive_fixed_zero (v : BinaryPermutation.natural (Fin 5))
    (hv : ∀ g : alternatingGroup (Fin 5),
      BinaryPermutation.alternatingNaturalRepresentation (Fin 5) g v = v) : v = 0 := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let w := e.symm v
  have hw (g : alternatingGroup (Fin 5)) :
      BinaryPermutation.coreRepresentation (Fin 5) g.val w = w := by
    apply e.injective
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    change BinaryPermutation.naturalRepresentation (Fin 5) g.val (e (e.symm v)) =
      e (e.symm v)
    rw [e.apply_symm_apply]
    exact hv g
  have hc : ∀ w : Fin 5 → ZMod 2, (∑ i, w i) = 0 →
      (∀ g : alternatingGroup (Fin 5), ∀ i, w (g.val.symm i) = w i) → w = 0 := by
    decide +kernel
  have hz : w = 0 := Subtype.ext (hc w.val w.property
    (fun g i => congrArg (fun u : BinaryPermutation.core (Fin 5) => u.val i) (hw g)))
  exact e.symm.injective (hz.trans (map_zero e.symm).symm)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A L : Subgroup G} (s : MovedSection ρ L)
  (e : MarkedActionEquiv s.space.toRepresentation (L ⊔ A) L
    (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))

private def alternatingEquiv : ActionEquiv (s.space.toRepresentation.comp L.subtype)
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines l v := by
    have h := e.action.intertwines (⟨l, e.contained l.property⟩ : ↥(L ⊔ A)) v
    rw [e.compatible] at h
    exact h

include e in
theorem symmetricFive_isCompl [Finite G] [Module.Finite (ZMod 2) V] :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  have hh := (H1Congr _ _ (alternatingEquiv s e).groupEquiv
    (alternatingEquiv s e).linearEquiv (alternatingEquiv s e).intertwines).finrank_eq
  have hb := supplement_quotient_finrank_le s
  rw [hh, BinaryPermutation.alternatingFive_natural_finrank_H1] at hb
  have hs : s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp
      ((Module.finrank_zero_iff).mp (Nat.eq_zero_of_le_zero hb))
  refine ⟨?_, codisjoint_iff.mpr hs⟩
  apply Submodule.disjoint_def.mpr
  intro v hv hf
  let w : s.space := ⟨v, hv⟩
  have hz : e.action.linearEquiv w = 0 := by
    apply naturalFive_fixed_zero
    intro g
    obtain ⟨l, rfl⟩ := e.subgroupEquiv.surjective g
    have ht := (alternatingEquiv s e).intertwines l w
    have hl : s.space.toRepresentation l w = w := Subtype.ext (hf l)
    change e.action.linearEquiv (s.space.toRepresentation l w) = _ at ht
    rw [hl] at ht
    exact ht.symm
  exact congrArg Subtype.val (e.action.linearEquiv.injective
    (hz.trans (map_zero e.action.linearEquiv).symm))

include e in
theorem symmetricFive_fixed_le [Finite G] [Module.Finite (ZMod 2) V] [L.Normal]
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    fixedSpace ρ L ≤ fixedSpace ρ A := by
  have hc := symmetricFive_isCompl s e
  intro v hv a
  have hw : ρ a v - v ∈ s.space.toSubmodule := by
    have ht : v ∈ s.space.toSubmodule ⊔ fixedSpace ρ A := hs ▸ Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp ht
    have he : ρ a (w + z) - (w + z) = ρ a w - w := by
      rw [map_add, show ρ a z = z from hz a]
      abel
    rw [he]
    exact s.space.toSubmodule.sub_mem (s.space.apply_mem_toSubmodule a hw) hw
  have hf : ρ a v - v ∈ fixedSpace ρ L := (fixedSpace ρ L).sub_mem
    ((fixedSpace_stable_of_normal ρ L (mem_top a) v).2 hv) hv
  have hz : ρ a v - v ∈ s.space.toSubmodule ⊓ fixedSpace ρ L := ⟨hw, hf⟩
  rw [hc.inf_eq_bot] at hz
  exact sub_eq_zero.mp hz

private theorem naturalFive_faithful :
    Function.Injective (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  intro g h hgh
  apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
  apply MulEquiv.ext
  intro v
  exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun hgh v.toAdd)

include e in
theorem symmetricFive_faithful :
    Function.Injective (s.space.toRepresentation.comp (L ⊔ A).subtype) := by
  intro g h hgh
  apply e.action.groupEquiv.injective
  apply naturalFive_faithful
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := e.action.linearEquiv.surjective v
  rw [← e.action.intertwines, ← e.action.intertwines]
  exact congrArg e.action.linearEquiv (LinearMap.congr_fun hgh w)

include e in
theorem symmetricFive_center : center ↥(L ⊔ A) = ⊥ := by
  apply bot_unique
  intro x hx
  apply e.action.groupEquiv.injective
  rw [map_one]
  have hy := (Subgroup.centerCongr e.action.groupEquiv ⟨x, hx⟩).property
  change e.action.groupEquiv x ∈ center (Equiv.Perm (Fin 5)) at hy
  have hz := (Subgroup.center_le_centralizer (alternatingGroup (Fin 5) : Set _)) hy
  simpa only [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide),
    mem_bot] using hz

private noncomputable def transportedHom :
    G →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))) where
  toFun g :=
    (e.action.linearEquiv.symm.trans
      ((LinearEquiv.ofBijective (s.space.toRepresentation g)
        (s.space.toRepresentation.apply_bijective g)).trans
        e.action.linearEquiv)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (e.action.linearEquiv
      (s.space.toRepresentation 1 (e.action.linearEquiv.symm v.toAdd))) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (e.action.linearEquiv
      (s.space.toRepresentation (g*h) (e.action.linearEquiv.symm v.toAdd))) =
      Multiplicative.ofAdd (e.action.linearEquiv (s.space.toRepresentation g
        (e.action.linearEquiv.symm (e.action.linearEquiv
          (s.space.toRepresentation h (e.action.linearEquiv.symm v.toAdd))))))
    rw [e.action.linearEquiv.symm_apply_apply, map_mul, Module.End.mul_apply]

private theorem transportedHom_on_join (h : ↥(L ⊔ A)) :
    transportedHom s e h =
      BinaryPermutation.naturalMulAction (Fin 5) (e.action.groupEquiv h) := by
  apply MulEquiv.ext
  intro v
  change Multiplicative.ofAdd (e.action.linearEquiv
    (s.space.toRepresentation h (e.action.linearEquiv.symm v.toAdd))) =
    Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 5)
      (e.action.groupEquiv h) v.toAdd)
  have he := e.action.intertwines h (e.action.linearEquiv.symm v.toAdd)
  rw [e.action.linearEquiv.apply_symm_apply] at he
  exact congrArg Multiplicative.ofAdd he

private theorem transportedHom_component :
    L.map (transportedHom s e) = (alternatingGroup (Fin 5)).map
      (BinaryPermutation.naturalMulAction (Fin 5)) := by
  ext f
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨e.subgroupEquiv ⟨l, hl⟩, (e.subgroupEquiv ⟨l, hl⟩).property, ?_⟩
    have he := transportedHom_on_join s e (⟨l, e.contained hl⟩ : ↥(L ⊔ A))
    rw [e.compatible ⟨l, hl⟩] at he
    exact he.symm
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk⟩ := e.subgroupEquiv.surjective ⟨l, hl⟩
    refine ⟨k, k.property, ?_⟩
    have he := transportedHom_on_join s e (⟨k, e.contained k.property⟩ : ↥(L ⊔ A))
    rw [e.compatible k, hk] at he
    exact he

include e in
/-- The actual normalizer on W gives coverage of the full ambient action by LA. -/
theorem symmetricFive_action_coverage [L.Normal] (g : G) :
    ∃ h : ↥(L ⊔ A), s.space.toRepresentation g = s.space.toRepresentation h := by
  have hn : transportedHom s e g ∈ normalizer
      (L.map (transportedHom s e) : Set _) := by
    apply Subgroup.le_normalizer_map (transportedHom s e)
    exact ⟨g, by rw [Subgroup.normalizer_eq_top]; exact mem_top _, rfl⟩
  rw [transportedHom_component s e] at hn
  obtain ⟨σ, hσ⟩ :=
    BinaryPermutation.normalizer_alternatingFive_naturalMulAction_le_range hn
  let h := e.action.groupEquiv.symm σ
  refine ⟨h, ?_⟩
  have he : transportedHom s e h = transportedHom s e g := by
    rw [transportedHom_on_join, e.action.groupEquiv.apply_symm_apply]
    exact hσ
  apply LinearMap.ext
  intro w
  apply e.action.linearEquiv.injective
  have ht := congrArg Multiplicative.toAdd
    (DFunLike.congr_fun he (Multiplicative.ofAdd (e.action.linearEquiv w)))
  change e.action.linearEquiv (s.space.toRepresentation h
      (e.action.linearEquiv.symm (e.action.linearEquiv w))) =
    e.action.linearEquiv (s.space.toRepresentation g
      (e.action.linearEquiv.symm (e.action.linearEquiv w))) at ht
  rw [e.action.linearEquiv.symm_apply_apply] at ht
  exact ht.symm

include e in
/-- In the literal action image of W, the image of LA is the full group. -/
theorem symmetricFive_restrictedSubgroup_eq_top [L.Normal] :
    restrictedSubgroup ρ s.space.toSubmodule (L ⊔ A) = ⊤ := by
  let hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ s.space.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun g _ v hv => s.space.apply_mem_toSubmodule g hv)
  rw [← invariantActionHom_map ρ s.space.toSubmodule hs]
  apply top_unique
  intro x _
  obtain ⟨g, rfl⟩ := invariantActionHom_surjective ρ s.space.toSubmodule hs x
  obtain ⟨h, hh⟩ := symmetricFive_action_coverage s e g
  refine ⟨h, h.property, ?_⟩
  apply subspaceImageRepresentation_injective ρ s.space.toSubmodule
  apply LinearMap.ext
  intro w
  exact (LinearMap.congr_fun hh w).symm

include e in
/-- The fixed space of L is centralized by the full marked symmetric factor. -/
theorem symmetricFive_le_fixed_kernel [Finite G] [Module.Finite (ZMod 2) V] [L.Normal]
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    L ⊔ A ≤ subspaceKernel ρ (fixedSpace ρ L) ⊤ := by
  apply sup_le
  · intro l hl
    exact ⟨mem_top _, fun v hv => hv ⟨l, hl⟩⟩
  · intro a ha
    exact ⟨mem_top _, fun v hv => symmetricFive_fixed_le s e hs hv ⟨a, ha⟩⟩

include e in
/-- Faithfulness and the direct sum turn normalizer coverage into the literal
identity LA = C_G(C_V(L)). -/
theorem symmetricFive_eq_fixed_kernel [Finite G] [Module.Finite (ZMod 2) V] [L.Normal]
    (hf : Function.Injective ρ) (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    L ⊔ A = subspaceKernel ρ (fixedSpace ρ L) ⊤ := by
  have hle := symmetricFive_le_fixed_kernel s e hs
  refine le_antisymm hle ?_
  rintro g ⟨_, hg⟩
  obtain ⟨h, hh⟩ := symmetricFive_action_coverage s e g
  have he : g = (h : G) := by
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ s.space.toSubmodule ⊔ fixedSpace ρ L :=
      (symmetricFive_isCompl s e).sup_eq_top ▸ Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, map_add, hg z hz, (hle h.property).2 z hz]
    exact congrArg (· + z) (congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩))
  exact he ▸ h.property

include e in
/-- The marked symmetric-five factor is normal in the original ambient group. -/
theorem symmetricFive_normal [Finite G] [Module.Finite (ZMod 2) V] [L.Normal]
    (hf : Function.Injective ρ) (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    (L ⊔ A).Normal := by
  rw [symmetricFive_eq_fixed_kernel s e hf hs]
  rw [← invariantActionHom_ker ρ (fixedSpace ρ L) (fixedSpace_stable_of_normal ρ L)]
  infer_instance

include e in
theorem symmetricFive_fixed_eq [Finite G] [Module.Finite (ZMod 2) V] [L.Normal]
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    fixedSpace ρ (L ⊔ A) = fixedSpace ρ L := by
  apply le_antisymm (fixedSpace_antitone ρ le_sup_left)
  intro v hv h
  exact (symmetricFive_le_fixed_kernel s e hs h.property).2 v hv

include e in
/-- B.5.10 in the symmetric-five alternative of B.5.9. All splitting,
normality, faithfulness and action-image premises of the product construction
are discharged on the original marked action. -/
theorem symmetricFive_configuration [Finite G] {K : CFSG.Quasithin.GroupClass}
    (hyp : FFHypothesis K ρ) [L.Normal]
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    Nonempty (ProductConfiguration ρ (L ⊔ A) s.space) := by
  let := hyp.finite_module
  let := symmetricFive_normal s e hyp.faithful hs
  apply configuration_of_offender_image ρ hyp.generated s.space (L ⊔ A)
    (symmetricFive_faithful s e) (symmetricFive_center s e)
  · intro D _
    rw [symmetricFive_restrictedSubgroup_eq_top s e]
    exact le_top
  · left
    rw [symmetricFive_fixed_eq s e hs]
    exact (symmetricFive_isCompl s e).sup_eq_top

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
