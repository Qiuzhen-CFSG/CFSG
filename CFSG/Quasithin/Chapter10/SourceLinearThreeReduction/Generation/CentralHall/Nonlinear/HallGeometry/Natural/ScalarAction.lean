module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Natural.FixedLifting
public import Theory.Representation.SemilinearFixedPointCentralizer

/-!
# Elimination of the natural Hall coefficient action

Extend the actual natural section action to the common normalizer of its
numerator and component. Its scalar commutant makes this action semilinear.
Every quotient vector fixed by the Sylow component stabilizer lifts to a
fixed vector in the original moved subgroup. The central Hall hypothesis
therefore fixes all these quotient vectors. Fixed-field descent makes the
odd Hall action linear over the original field, retaining the central kernel.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

theorem exists_natural_hall_linear_action
    (geometry : ModuleGeometry D) (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (d : NaturalSection D n e) :
    ∃ η : Representation (ZMod 2) B (Fin 2 → GaloisField 2 n),
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        η b (d.coordinates w).toAdd =
          (d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
            (mem_normalizer_iff.mp (hall_normalizes_moved D c
              (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩).toAdd) ∧
      (∀ (b : B) (l : L) (v : (Fin 2 → GaloisField 2 n)),
        η b (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
          SL2.BinarySmall.natural
            (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l))) (η b v)) ∧
      ∀ (b : B) (a : GaloisField 2 n) (v : (Fin 2 → GaloisField 2 n)), η b (a • v) = a • η b v := by
  let : NeZero n := ⟨by omega⟩
  let W : Subgroup G := ⁅D.fullModule,L⁆
  let P : Subgroup G := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hWV : W ≤ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact hh.trans (le_of_eq geometry.full_eq_local)
  let := D.module_elementary
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_injective (inclusion hWV) (inclusion_injective hWV)
  have hSP : S ≤ P := by
    intro s hs
    refine ⟨hs.2,?_⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom = _
    rw [map_commutator,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T hs.1)),
      mem_normalizer_iff_map_conj_eq.mp hs.2]
  have hBP : B.map H.subtype ≤ P := le_inf (hall_normalizes_component D c)
    (hall_normalizes_moved D c)
  obtain ⟨τ,hτ⟩ := d.exists_original_quotient_action
    (show P ≤ normalizer (W : Set G) from inf_le_right)
    ((le_inf (show P ≤ normalizer (W : Set G) from inf_le_right)
      ((show P ≤ normalizer (L : Set G) from inf_le_left).trans
        (normalizer_le_normalizer_centralizer L))).trans
          inf_normalizer_le_normalizer_inf)
  let β : P →* MulAut (L ⧸ pCore 2 L) :=
    (normalizerPCoreQuotientAction L).comp (inclusion inf_le_left)
  have ht (p : P) (l : L) (v : (Fin 2 → GaloisField 2 n)) :
      τ p (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
        SL2.BinarySmall.natural
          (e (β p (QuotientGroup.mk' (pCore 2 L) l))) (τ p v) := by
    obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv]
    let l' := L.normalizerMonoidHom (inclusion (show P ≤ normalizer (L : Set G) from inf_le_left) p) l
    have hl' : β p (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 L) l' := quotientAut_apply_mk _ _ _
    rw [hl']
    change τ p (((SL2.BinarySmall.natural).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) l (d.coordinates w).toAdd) = _
    rw [←d.equivariant,hτ,hτ]
    refine Eq.trans ?_ (d.equivariant l' (W.normalizerMonoidHom
      (inclusion (show P ≤ normalizer (W : Set G) from inf_le_right) p) w))
    congr 2
    apply Subtype.ext
    change (p : G)*((l : G)*(w : G)*(l : G)⁻¹)*(p : G)⁻¹ =
      ((p : G)*(l : G)*(p : G)⁻¹)*((p : G)*(w : G)*(p : G)⁻¹)*
        ((p : G)*(l : G)*(p : G)⁻¹)⁻¹
    group
  have hsemi : ∀ p : P, ∃ σ : GaloisField 2 n ≃+* GaloisField 2 n,
      ∀ a v, τ p (a • v) = σ a • τ p v := by
    intro p
    apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (specialLinearNatural 2 (k := GaloisField 2 n))
      (fun f hf => SL2NaturalOffenders.centralizer_scalar f hf)
      (MulAut.congr e (β p)) (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom p))
    intro g v
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    subst g
    change τ p (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
      SL2.BinarySmall.natural
        (e (β p (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (τ p v)
    rw [e.symm_apply_apply]
    exact ht p l v
  let f : B →* P := (H.subtype.comp B.subtype).codRestrict P
    (fun b => hBP (mem_map_of_mem H.subtype b.property))
  let η := τ.comp f
  refine ⟨η,fun b w => hτ (f b) w,fun b l v => ht (f b) l v,?_⟩
  intro b
  apply SemilinearFixedPointCentralizer.linear_of_odd_of_fixes_invariants
    τ hsemi (S.subgroupOf P)
    ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).of_injective
      (subgroupOfEquivOfLe hSP).toMonoidHom (subgroupOfEquivOfLe hSP).injective)
    (f b) ((hall_odd D c).of_dvd_nat
      ((orderOf_map_dvd f b).trans (orderOf_dvd_natCard b)))
  intro v hv
  obtain ⟨w,hw,hwS⟩ := natural_section_fixed_lift D n hn
    (GaloisField.card 2 n (NeZero.ne n)) e d S inf_le_right
    (hSP.trans inf_le_right) (τ.comp (inclusion hSP))
    (fun s w => hτ (inclusion hSP s) w) v (by
      intro s
      exact hv ⟨⟨s,hSP s.property⟩,s.property⟩)
  rw [←hw,hτ]
  exact congrArg Multiplicative.toAdd
    (natural_hall_fixed_coordinates D c geometry n e d w hwS b)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
