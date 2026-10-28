module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Invariance
public import Theory.Representation.BinaryOffender.CentralizerField
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Offender placement in the non-natural branches of B.5.9

For an inner actor A on a centerless component L, multiplication in
L C_G(L) constructs both actual projections. The centralizer projection is
a two-group. B.7.2 makes it preserve every Irr⁺ member, and the proved
odd-order centralizer theorem makes it fix that member pointwise. If these
members span W=[V,L], the projection fixes W. The supplement by C_V(A)
also makes it fix V/W. The joint kernel is a normal two-subgroup, hence is
trivial when O₂(G)=1. Thus A≤L.

The final two applications construct the doubled-natural and four-dimensional
ComponentActionCase conclusions with containment proved. The natural actions,
Irr⁺ spanning, inner action, centerlessness and supplement still need their
source classification; this module does not prove the preliminary classifier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed pp.107–108; A.1.41 and B.7.2(1).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem section_kernel_le_twoCore (hf : Function.Injective ρ) (W : Subrepresentation ρ) :
    W.toRepresentation.ker ⊓ W.quotientRepresentation.ker ≤ pCore 2 G := by
  let N := W.toRepresentation.ker ⊓ W.quotientRepresentation.ker
  have hp : IsPGroup 2 N := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hf
    ext v
    have hq := LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property.2) (W.toSubmodule.mkQ v)
    change W.toSubmodule.mkQ (ρ x v) = W.toSubmodule.mkQ v at hq
    have hd : ρ x v - v ∈ W.toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change W.toSubmodule.mkQ (ρ x v - v) = 0
      rw [map_sub, hq, sub_self]
    have hfix := congrArg Subtype.val
      (LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property.1) ⟨ρ x v - v, hd⟩)
    change ρ x (ρ x v - v) = ρ x v - v at hfix
    rw [map_sub] at hfix
    have htwo (w : V) : w + w = 0 := by
      calc
        w + w = ((1 : ZMod 2) + 1) • w := by rw [add_smul, one_smul]
        _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
    have hs : ρ x (ρ x v) = v := by
      apply add_right_cancel (b := v)
      exact (sub_eq_sub_iff_add_eq_add.mp hfix).trans ((htwo _).trans (htwo v).symm)
    change ρ ((x : G) ^ (2 ^ 1)) v = ρ (1 : G) v
    simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hs
  exact le_sSup ⟨inferInstance, hp⟩

theorem twoGroup_fixes_irrPlus [Module.Finite (ZMod 2) V]
    {L Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hc : Q ≤ centralizer (L : Set G)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ L I) (hs : Q ≤ subspaceStabilizer ρ I) :
    Q ≤ subspaceKernel ρ I ⊤ := by
  obtain ⟨hLI,hfull,hirr⟩ := hI
  let σ := (invariantSubspace ρ L I hLI).toRepresentation
  let τ := (invariantSubspace ρ Q I hs).toRepresentation
  let f : Q →* Representation.CentralizerField.linearCentralizer σ :=
    τ.asGroupHom.codRestrict _ (by
      intro q
      apply (Representation.CentralizerField.mem_linearCentralizer_iff σ _).mpr
      intro l v
      apply Subtype.ext
      change ρ q (ρ l v) = ρ l (ρ q v)
      simp only [← Module.End.mul_apply, ← map_mul, hc q.property l l.property])
  have ho := (Representation.BinaryOffender.CentralizerField.centralizer_cyclic_odd
    ρ L I hLI hfull hirr).2
  have hp : IsPGroup 2 f.range := hQ.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hzero (q : Q) : f q = 1 := by
    by_contra hn
    have hn' : f.rangeRestrict q ≠ 1 := fun h => hn (congrArg Subtype.val h)
    have hd := hp.dvd_orderOf hn'
    have hc' : orderOf (f.rangeRestrict q) ∣ Nat.card (Representation.CentralizerField.linearCentralizer σ) :=
      (_root_.orderOf_dvd_natCard _).trans (Subgroup.card_subgroup_dvd_card _)
    exact ho.not_two_dvd_nat (hd.trans hc')
  intro q hq
  refine ⟨mem_top _, fun v hv => ?_⟩
  exact congrArg (fun c : Representation.CentralizerField.linearCentralizer σ =>
    ((c.val.val ⟨v,hv⟩ : I) : V)) (hzero ⟨q,hq⟩)

structure InnerProjections (A L : Subgroup G) where
  left : A →* L
  right : A →* centralizer (L : Set G)
  mul_eq : ∀ a, (left a : G) * (right a : G) = (a : G)

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem exists_innerProjections {A L : Subgroup G} (hi : InducesInner A L)
    (hd : Disjoint L (centralizer (L : Set G))) : Nonempty (InnerProjections A L) := by
  have hle : A ≤ L ⊔ centralizer (L : Set G) := by
    intro a ha
    obtain ⟨l,hl,he⟩ := hi a ha
    have hc : l⁻¹ * a ∈ centralizer (L : Set G) := by
      intro x hx
      have hh := congrArg (fun y => l⁻¹ * y * a) (he x hx)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh.symm
    have hprod := (L ⊔ centralizer (L : Set G)).mul_mem
      ((le_sup_left : L ≤ L ⊔ centralizer (L : Set G)) hl)
      ((le_sup_right : centralizer (L : Set G) ≤ L ⊔ centralizer (L : Set G)) hc)
    simpa only [mul_inv_cancel_left] using hprod
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    L (centralizer (L : Set G)) hd (le_centralizer_iff.mpr le_rfl)
  let f := e.symm.toMonoidHom.comp (Subgroup.inclusion hle)
  refine ⟨⟨(MonoidHom.fst _ _).comp f, (MonoidHom.snd _ _).comp f, ?_⟩⟩
  intro a
  exact (he (f a).1 (f a).2).symm.trans
    (congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hle a)))

namespace InnerProjections
variable {A L : Subgroup G} (p : InnerProjections A L)

def centralGroup : Subgroup G := ((centralizer (L : Set G)).subtype.comp p.right).range

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem centralGroup_two (hA : IsPGroup 2 A) : IsPGroup 2 p.centralGroup :=
  hA.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem centralGroup_le_centralizer : p.centralGroup ≤ centralizer (L : Set G) := by
  rintro _ ⟨a,rfl⟩
  exact (p.right a).property

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem right_eq (a : A) : (p.right a : G) = (p.left a : G)⁻¹ * a := by
  rw [← p.mul_eq a, inv_mul_cancel_left]

theorem centralGroup_stabilizes {I : Submodule (ZMod 2) V}
    (hL : L ≤ subspaceStabilizer ρ I) (hA : A ≤ subspaceStabilizer ρ I) :
    p.centralGroup ≤ subspaceStabilizer ρ I := by
  rintro _ ⟨a,rfl⟩
  change (p.right a : G) ∈ subspaceStabilizer ρ I
  rw [p.right_eq]
  exact (subspaceStabilizer ρ I).mul_mem
    ((subspaceStabilizer ρ I).inv_mem (hL (p.left a).property)) (hA a.property)

theorem centralGroup_quotient_kernel (W : Subrepresentation ρ)
    (hm : W.toSubmodule = moved ρ L) (hs : W.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    p.centralGroup ≤ W.quotientRepresentation.ker := by
  have hLker : L ≤ W.quotientRepresentation.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro q
    obtain ⟨v,rfl⟩ := W.toSubmodule.mkQ_surjective q
    change W.toSubmodule.mkQ (ρ l v) = W.toSubmodule.mkQ v
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [hm]
    exact Submodule.subset_span ⟨l,hl,v,Submodule.mem_top,rfl⟩
  have hAker : A ≤ W.quotientRepresentation.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro q
    obtain ⟨v,rfl⟩ := W.toSubmodule.mkQ_surjective q
    obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp (hs ▸ (Submodule.mem_top : v ∈ ⊤))
    change W.toSubmodule.mkQ (ρ a (w+c)) = W.toSubmodule.mkQ (w+c)
    have hca : ρ a c = c := hc ⟨a,ha⟩
    rw [map_add, hca, map_add, map_add]
    have hz : W.toSubmodule.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
    have haz : W.toSubmodule.mkQ (ρ a w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (W.apply_mem_toSubmodule a hw)
    rw [hz,haz]
  rintro _ ⟨a,rfl⟩
  change (p.right a : G) ∈ W.quotientRepresentation.ker
  rw [p.right_eq]
  exact W.quotientRepresentation.ker.mul_mem
    (W.quotientRepresentation.ker.inv_mem (hLker (p.left a).property)) (hAker a.property)
end InnerProjections

/-- The non-IV projection argument: a minimal offender inducing inner
    automorphisms lies in L when the moved module is spanned by Irr⁺ members
    and supplements the offender's fixed space. -/
theorem minimalOffender_le_component_of_irrPlus_span [Finite G]
    [Module.Finite (ZMod 2) V] (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L)
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hspan : s.space.toSubmodule ≤ sSup {I | IsIrrPlus ρ L I}) : A ≤ L := by
  obtain ⟨p⟩ := exists_innerProjections hi hd
  let : IsElementaryAbelian 2 A := hA.1.1.2
  have hQ := p.centralGroup_two (IsElementaryAbelian.isPGroup 2 A)
  have hfix : s.space.toSubmodule ≤ fixedSpace ρ p.centralGroup := by
    apply hspan.trans
    apply sSup_le
    intro I hI
    have hAI := minimalOffender_stabilizes_irrPlus ρ hf hA hL hLA hI
    have hQI := p.centralGroup_stabilizes ρ hI.choose hAI
    have hz := twoGroup_fixes_irrPlus ρ hQ p.centralGroup_le_centralizer hI hQI
    intro v hv q
    exact (hz q.property).2 v hv
  have hk : p.centralGroup ≤ s.space.toRepresentation.ker := by
    intro q hq
    apply MonoidHom.mem_ker.mpr
    ext v
    exact hfix v.property ⟨q,hq⟩
  have hq := p.centralGroup_quotient_kernel ρ s.space s.space_eq hs
  have hzero : p.centralGroup = ⊥ := by
    apply le_bot_iff.mp
    calc
      p.centralGroup ≤ s.space.toRepresentation.ker ⊓ s.space.quotientRepresentation.ker := le_inf hk hq
      _ ≤ pCore 2 G := section_kernel_le_twoCore ρ hf s.space
      _ = ⊥ := hcore
  intro a ha
  have he : (p.right ⟨a,ha⟩ : G) = 1 :=
    hzero.le (show (p.right ⟨a,ha⟩ : G) ∈ p.centralGroup from ⟨⟨a,ha⟩,rfl⟩)
  have hm := p.mul_eq ⟨a,ha⟩
  rw [he,mul_one] at hm
  simpa only [hm] using (p.left ⟨a,ha⟩).property

/-- Case (III), retaining one compatible actor on both natural summands.
The containment conclusion is proved by the projection argument. -/
theorem doubleThree_case_of_span [Finite G] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L)
    (F : BinaryField) (ho : Odd F.degree)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2)
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hspan : s.space.toSubmodule ≤ sSup {I | IsIrrPlus ρ L I}) :
    ComponentActionCase ρ A L s L :=
  .doubleThree F ho hn
    (minimalOffender_le_component_of_irrPlus_span ρ hf hcore hA hL hLA s hi hd hs hspan) hs

/-- Cases (I) and (V) require just the single Irr⁺ member W. -/
theorem minimalOffender_le_component_of_irrPlus [Finite G] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L)
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) : A ≤ L :=
  minimalOffender_le_component_of_irrPlus_span ρ hf hcore hA hL hLA s hi hd hs (le_sSup hI)

/-- The actual four-dimensional-cover consumer of the same projection argument. -/
theorem fourCover_case_of_irrPlus [Finite G] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L)
    (hc : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype))
    (hk : Nonempty (A ≃* Multiplicative (Fin 2 → ZMod 2)))
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) : ComponentActionCase ρ A L s L :=
  .fourCover hc hk
    (minimalOffender_le_component_of_irrPlus ρ hf hcore hA hL hLA s hi hd hs hI) hs
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
