module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.DualSection

/-!
# The original dual-section obstruction for the G₂ critical pair

The action on U/C_U(O₂(H)) descends through the literal H/O₂(H) map.
The genuine identity [U,O₂(H)] = V₁ makes this quotient nonzero, and
U = [U,K] makes its action nontrivial on K*. A self-centralizing normal
G₂(2)′ component is the monolith, so the descended action is faithful.
The proved no-transvection theorem therefore applies to this section.

The original 14.5.21 equivariant duality preserves the displacement rank
of the same actor, including the inverse in the contragredient action.
Every nontrivial involution in H* thus moves at least two dimensions of
O₂(H)/C_{O₂(H)}(U). The last theorem expresses this as index at least four
for the literal commutator preimage, consumed by G2SourceNoncontainment.
No natural or alternating module is substituted for either source section.

The consumer G2SourceNoncontainment constructs the earlier duality from the
central commutator pairing. The full identity [U,O₂(H)] = V₁ remains an
explicit 14.5.21(2) input, with final discharge retained by qt-d-14775-source.
This module does not establish the critical actor
identification or the G₂ residual exclusion.

Source: Aschbacher–Smith, 14.5.21(1)–(2), printed pp.1019–1020;
14.7.62(1), printed p.1068; the general G₂ exclusion of transvections
is the proved B.4/F.9 input used in 13.8.27.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source CriticalFusion.Source.CriticalIntersections
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W X Y : Type u}
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

omit [Finite G] in
private theorem point_centralizes_H : F.Vi 1 ≤ centralizer (F.H : Set G) := by
  apply le_centralizer_iff.mp
  exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))

omit [Finite G] in
private theorem point_le_dual_kernel :
    F.Vi 1 ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) :=
  le_inf ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (point_centralizes_H.trans (centralizer_le (pCoreIn_le 2 F.H)))

omit [Finite G] in
include c in
/-- Descend the original U-centralizer quotient through the same star map. -/
theorem source_dual_action_descends (s : SourceDuality F X Y) :
    ∃ τ : Representation (ZMod 2) (HStar F.H) X,
      τ.comp (starMap F) = s.uAction := by
  have hk : pCore 2 F.H ≤ s.uAction.ker := by
    intro q hq
    apply (s.uSection.action_mem_ker_iff q).mpr
    intro v hv
    exact point_le_dual_kernel (core_commutator c
      (commutator_mem_commutator (mem_map_of_mem F.H.subtype hq) hv))
  let : Representation.IsTrivial (s.uAction.comp (pCore 2 F.H).subtype) :=
    ⟨fun q => hk q.property⟩
  exact ⟨s.uAction.ofQuotient (pCore 2 F.H),rfl⟩

private theorem source_component_properties
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple (star F (K F)) ∧ centralizer (star F (K F) : Set (HStar F.H)) = ⊥ := by
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup (star F (K F)) := e.isSimpleGroup
  let : Group.IsPerfect (star F (K F)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (star F (K F)) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))
  refine ⟨⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩,
    bot_unique ?_⟩
  intro x hx
  have hxL : x ∈ star F (K F) := by
    rw [← hfit] at hx ⊢
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hh : (⟨x,hxL⟩ : star F (K F)) ∈ center (star F (K F)) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hx l l.property)
  rw [hz,mem_bot] at hh
  exact congrArg Subtype.val hh

/-- Generation and the nonzero core pairing make the descended action faithful. -/
theorem source_dual_action_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (s : SourceDuality F X Y) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (τ : Representation (ZMod 2) (HStar F.H) X)
    (hτ : τ.comp (starMap F) = s.uAction) : Function.Injective τ := by
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  obtain ⟨hq,hcent⟩ := source_component_properties hcomponent hfit eK
  let := hq
  apply faithful_of_nontrivial_on_monolith τ (star F (K F))
    (Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.monolith _ hcent)
  by_contra! hn
  have hKU : ⁅K F,F.U⁆ ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) := by
    apply commutator_le.mpr
    intro k hk v hv
    let kH : F.H := ⟨k,map_subtype_le _ hk⟩
    apply (s.uSection.action_mem_ker_iff kH).mp _ v hv
    apply LinearMap.ext
    intro x
    change s.uAction kH x = x
    rw [← hτ]
    exact hn (starMap F kH) (mem_map_of_mem _ (show kH ∈ (K F).subgroupOf F.H from hk)) x
  have hU : F.U ≤ centralizer (F.H.pCoreIn 2 : Set G) := by
    rw [commutator_comm,commutator_U h F] at hKU
    exact hKU.trans inf_le_right
  have hz : F.Vi 1 = ⊥ := hcomm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hU)
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  rw [hz,card_bot] at hc
  omega

include c in
/-- The same nontrivial star involution moves at least two dimensions on the dual core section. -/
theorem source_dual_displacement_ge_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (s : SourceDuality F X Y) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (hne : starMap F a ≠ 1) (hpow : starMap F a ^ 2 = 1) :
    2 ≤ Module.finrank (ZMod 2) (s.qAction a - LinearMap.id).range := by
  let : Finite X := Finite.of_surjective (fun v : F.U => (s.uSection.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.uSection.onto)
  let : Finite Y := Finite.of_surjective (fun q : F.H.pCoreIn 2 => (s.qSection.coordinates q).toAdd)
    (Multiplicative.toAdd.surjective.comp s.qSection.onto)
  obtain ⟨τ,hτ⟩ := source_dual_action_descends c s
  have hf := source_dual_action_faithful h hcomponent hfit eK s hcomm τ hτ
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  obtain ⟨hq,hcent⟩ := source_component_properties hcomponent hfit eK
  let := hq
  let e := (Chapter13.Section08.Components.componentStarEquiv F.H (K F)
    (map_subtype_le _) hcomponent).symm.trans eK
  have hn := Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.no_transvection
    τ (star F (K F)) hf hcent e (starMap F a) hne hpow
  have hp := fixedCodim_pos_of_faithful τ hf
    (show zpowers (starMap F a) ≠ ⊥ by simpa using hne)
  have he : fixedCodim s.qAction (zpowers a) = fixedCodim τ (zpowers (starMap F a)) := by
    calc
      fixedCodim s.qAction (zpowers a) = fixedCodim s.uAction.dual (zpowers a) := by
        have hh := fixedCodim_map_equivariant s.qAction s.uAction.dual
          (MonoidHom.id F.H) s.duality.toLinearEquiv
          (fun g v => LinearMap.congr_fun (s.duality.isIntertwining' g) v) (zpowers a)
        simpa only [Subgroup.map_id] using hh
      _ = fixedCodim s.uAction (zpowers a) := fixedCodim_zpowers_dual s.uAction a
      _ = fixedCodim τ (zpowers (starMap F a)) := by
        rw [← hτ,fixedCodim,fixedSpace_comp_map,MonoidHom.map_zpowers]
        rfl
  rw [fixedCodim_zpowers_eq_displacement_rank] at he
  omega

include c in
/-- The literal dual-section commutator preimage has index at least four. -/
theorem source_dual_fixed_index_ge_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (s : SourceDuality F X Y) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (A : Subgroup G) (hAH : A ≤ F.H) (a : F.H) (ha : (a : G) ∈ A)
    (hne : starMap F a ≠ 1) (hpow : starMap F a ^ 2 = 1) :
    4 ≤ (commutatorPreimage (F.H.pCoreIn 2) A
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) := by
  let : Finite Y := Finite.of_surjective
    (fun q : F.H.pCoreIn 2 => (s.qSection.coordinates q).toAdd)
    (Multiplicative.toAdd.surjective.comp s.qSection.onto)
  let r := s.qAction a - LinearMap.id
  let f : F.H.pCoreIn 2 →* Multiplicative r.range :=
    (AddMonoidHom.toMultiplicative r.rangeRestrict.toAddMonoidHom).comp s.qSection.coordinates
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨v,hv⟩ := y.toAdd.property
    obtain ⟨q,hq⟩ := s.qSection.onto (Multiplicative.ofAdd v)
    refine ⟨q,?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change r (s.qSection.coordinates q).toAdd = y.toAdd.val
    rw [hq]
    exact hv
  have hi : 4 ≤ f.ker.index := by
    rw [Subgroup.index_ker,f.range_eq_top_of_surjective hf,Subgroup.card_top]
    change 4 ≤ Nat.card r.range
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (source_dual_displacement_ge_two c h hcomponent hfit eK s hcomm a hne hpow)
  have hle : (commutatorPreimage (F.H.pCoreIn 2) A
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).subgroupOf (F.H.pCoreIn 2) ≤ f.ker := by
    rw [CriticalIntersections.DualSection.commutatorPreimage_eq_fixed_preimage s A hAH]
    intro q hq
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change s.qAction a (s.qSection.coordinates q).toAdd -
      (s.qSection.coordinates q).toAdd = 0
    exact sub_eq_zero.mpr (hq ⟨a,ha⟩)
  exact hi.trans (Subgroup.index_antitone hle)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
