module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FixedVectors
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.ComponentAction
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.Suzuki.NaturalCentralizer
public import Theory.Representation.Suzuki.SmallDegree.Models
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SemilinearFixedPointCentralizer

/-!
# Field linearity of the original Suzuki Hall action

The common normalizer of the component and its moved subgroup acts on the
supplied whole natural module. Its additive scalar commutant makes the
normalizer action semilinear. The central Hall hypothesis fixes the vectors
fixed by the original Sylow component stabilizer. Fixed-field descent then
kills the Hall coefficient action on the defining field.

The action and quotient map are the original ones. This supplies the field
step toward `SuzukiActionTrivialAt`; the remaining source assembly is owned
by qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith, 10.1.2(5), 10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
open BenderSuzuki.MatrixGroups SuzukiNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
theorem exists_suzuki_hall_linear_action
    (geometry : ModuleGeometry D) (m : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SuzukiNatural.natural m).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ η : Representation (ZMod 2) B (SuzukiNatural.W m),
      (∀ (b : B) (w : (⁅D.fullModule,L⁆ : Subgroup G)),
        η b (d.coordinates w).toAdd =
          (d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
            (mem_normalizer_iff.mp (hall_normalizes_moved D c
              (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩).toAdd) ∧
      (∀ (b : B) (l : L) (v : SuzukiNatural.W m),
        η b (SuzukiNatural.natural m (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
          SuzukiNatural.natural m
            (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l))) (η b v)) ∧
      ∀ (b : B) (a : SuzukiNatural.F m) (v : SuzukiNatural.W m), η b (a • v) = a • η b v := by
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
    (show P ≤ normalizer ((⊥ : Subgroup G) : Set G) from by rw [normalizer_eq_top]; exact le_top)
  let β : P →* MulAut (L ⧸ pCore 2 L) :=
    (normalizerPCoreQuotientAction L).comp (inclusion inf_le_left)
  have ht (p : P) (l : L) (v : SuzukiNatural.W m) :
      τ p (SuzukiNatural.natural m (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
        SuzukiNatural.natural m
          (e (β p (QuotientGroup.mk' (pCore 2 L) l))) (τ p v) := by
    obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv]
    let l' := L.normalizerMonoidHom (inclusion (show P ≤ normalizer (L : Set G) from inf_le_left) p) l
    have hl' : β p (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 L) l' := quotientAut_apply_mk _ _ _
    rw [hl']
    change τ p (((SuzukiNatural.natural m).comp
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
  have hsemi : ∀ p : P, ∃ σ : SuzukiNatural.F m ≃+* SuzukiNatural.F m,
      ∀ a v, τ p (a • v) = σ a • τ p v := by
    intro p
    apply OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (SuzukiSmallDegree.naturalField m) (SuzukiNatural.commuting_addHom_eq_scalar m)
      (MulAut.congr e (β p)) (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom p))
    intro g v
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    subst g
    change τ p (SuzukiNatural.natural m (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
      SuzukiNatural.natural m
        (e (β p (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (τ p v)
    rw [e.symm_apply_apply]
    exact ht p l v
  let f : B →* P := (H.subtype.comp B.subtype).codRestrict P
    (fun b => hBP (mem_map_of_mem H.subtype b.property))
  let η := τ.comp f
  have hi : Function.Injective d.coordinates :=
    (MonoidHom.ker_eq_bot_iff d.coordinates).mp (by rw [d.kernel_eq,bot_subgroupOf])
  refine ⟨η,fun b w => hτ (f b) w,fun b l v => ht (f b) l v,?_⟩
  intro b
  apply SemilinearFixedPointCentralizer.linear_of_odd_of_fixes_invariants
    τ hsemi (S.subgroupOf P)
    ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).of_injective
      (subgroupOfEquivOfLe hSP).toMonoidHom (subgroupOfEquivOfLe hSP).injective)
    (f b) ((hall_odd D c).of_dvd_nat
      ((orderOf_map_dvd f b).trans (orderOf_dvd_natCard b)))
  intro v hv
  obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
  have hcoord : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [←hcoord,hτ]
  apply congrArg Multiplicative.toAdd
  exact hall_fixed_coordinates D c geometry d
    (d.centralizer_le_kernel_of_fixed_eq_zero (by
      intro x hx
      apply SuzukiNatural.natural_fixed_eq_zero m x
      intro g
      obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
      exact hx l)) w (by
        intro s hs
        let p : S.subgroupOf P := ⟨⟨s,hSP hs⟩,hs⟩
        have he := hv p
        rw [←hcoord,hτ] at he
        have he' := hi (Multiplicative.toAdd.injective he)
        have hc := congrArg Subtype.val he'
        change s*(w : G)*s⁻¹ = (w : G) at hc
        exact mul_inv_eq_iff_eq_mul.mp hc) b
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
