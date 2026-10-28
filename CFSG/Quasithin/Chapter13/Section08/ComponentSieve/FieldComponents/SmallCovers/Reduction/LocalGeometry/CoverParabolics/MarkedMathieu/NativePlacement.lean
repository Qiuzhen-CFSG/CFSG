module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.NativeWitness
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups
public import Theory.GroupTheory.SylowNormalIntersection


/-!
# The marked native hexad in the cubic Mathieu cover

The literal theta identity and Y < L₁ force a three-divisible image of
L₁ in M₂₂: otherwise every order-three generator would lie in the
central preimage and hence in its two-residual Y. Relative normality and
the Sylow intersection theorem provide the other native classification
inputs. Transporting the actual conjugation action to the full design
group makes T stabilize the same hexad as K ∩ M.

This selects a T-normalized hexad lift containing L₁, with its native
intersection an ordinary maximal subgroup of order 384. Placement in the
solvable residual of that lift is proved separately.

Source: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
open Theory.GroupAction.PCoreCentralModelAction
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
namespace MarkedMathieu
variable {G : Type*} [Group G]

noncomputable def nativeImage (K X : Subgroup G)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) : Subgroup M22 :=
  (X.subgroupOf K).map (mathieuProjection K e)

variable {H K L₁ T G₁ M : Subgroup G} (s : MarkedSetup H K L₁ T G₁ M)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
include s

theorem seed_le_component_overlap : L₁ ≤ K ⊓ M :=
  le_inf s.seed_le_component (s.seed_le_overlap.trans inf_le_right)

theorem native_seed_le_overlap : nativeImage K L₁ e ≤ nativeImage K (K ⊓ M) e :=
  map_mono (comap_mono (seed_le_component_overlap s))

theorem native_seed_normal :
    ((nativeImage K L₁ e).subgroupOf (nativeImage K (K ⊓ M) e)).Normal := by
  have hn : K ⊓ M ≤ normalizer (L₁ : Set G) :=
    (inf_le_inf_right M s.component_le).trans
      ((normal_subgroupOf_iff_le_normalizer s.seed_le_overlap).mp s.seed_normal)
  have hnK : (K ⊓ M).subgroupOf K ≤ normalizer (L₁.subgroupOf K : Set K) :=
    (comap_mono hn).trans (le_normalizer_comap _)
  exact normal_subgroupOf_of_le_normalizer
    ((map_mono hnK).trans (le_normalizer_map _))

theorem native_seed_solvable : Group.IsSolvable (nativeImage K L₁ e) := by
  let := s.seed_solvable
  let : Group.IsSolvable (L₁.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe s.seed_le_component).toMonoidHom)
      (subgroupOfEquivOfLe s.seed_le_component).injective
  exact Group.isSolvable_of_surjective
    ((mathieuProjection K e).subgroupMap_surjective (L₁.subgroupOf K))

/-- Properness of the residual forces an order-three generator to survive
in the native quotient, even though the kernel has a cubic section. -/
theorem native_seed_three_dvd : 3 ∣ Nat.card (nativeImage K L₁ e) := by
  by_contra hthree
  have hle : L₁ ≤ coverResidualIn K := by
    rw [s.theta]
    apply (closure_le _).mpr
    intro x hx
    have hxL : x ∈ L₁ := s.theta.symm ▸ subset_closure hx
    let k : K := ⟨x, s.seed_le_component hxL⟩
    have hk3 : orderOf k = 3 := (orderOf_coe k).symm.trans hx.2
    have himg : mathieuProjection K e k ∈ nativeImage K L₁ e :=
      mem_map.mpr ⟨k, hxL, rfl⟩
    have horder : orderOf (mathieuProjection K e k) ∣ 3 :=
      hk3 ▸ orderOf_map_dvd (mathieuProjection K e) k
    have he : mathieuProjection K e k = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp horder with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact (hthree (h ▸ (nativeImage K L₁ e).orderOf_dvd_natCard himg)).elim
    have hkC : k ∈ centralPreimage (pCore 2 K) := by
      rw [← mathieuProjection_ker K e]
      exact he
    have hr : (⟨k, hkC⟩ : centralPreimage (pCore 2 K)) ∈
        pResidual 2 (centralPreimage (pCore 2 K)) := by
      apply mem_pResidual_of_orderOf_coprime
      rw [← orderOf_coe, hk3]
      decide
    exact mem_map.mpr ⟨k, mem_map.mpr ⟨⟨k, hkC⟩, hr, rfl⟩, rfl⟩
  exact (not_le_of_gt s.proper_residual) hle

variable [Finite G]

theorem native_overlap_contains_sylow :
    ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ nativeImage K (K ⊓ M) e := by
  let := s.component_normal
  obtain ⟨S, hS⟩ := s.sylow
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let d : K.subgroupOf H ≃* K := subgroupOfEquivOfLe s.component_le
  let f : K.subgroupOf H →* M22 := (mathieuProjection K e).comp d.toMonoidHom
  have hf : Function.Surjective f := (mathieuProjection_surjective K e).comp d.surjective
  refine ⟨P.mapSurjective hf, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxT : x.val.val ∈ T := by
    rw [hP] at hx
    rw [← hS]
    exact mem_map.mpr ⟨x.val, hx, rfl⟩
  exact ⟨d x, ⟨x.property, s.sylow_le_M hxT⟩, rfl⟩


omit [Finite G] in
theorem sylow_normalizes_overlap : T ≤ normalizer (K ⊓ M : Set G) := by
  let := s.component_normal
  exact (le_inf
    (((Chapter1.isSylowIn_iff.mp s.sylow).2.1).trans
      (le_normalizer_of_normal_subgroupOf s.component_le))
    (s.sylow_le_M.trans M.le_normalizer)).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
noncomputable def designAction : H →* m22DesignAut :=
  M22ValueBound.Concrete.designAutEquiv.symm.toMonoidHom.comp
    (centralModelAction H K
      ((normal_subgroupOf_iff_le_normalizer s.component_le).mp s.component_normal) e)

omit [Finite G] in
theorem designAction_inner (k : K) :
    designAction s e (inclusion s.component_le k) =
      M22ValueBound.Concrete.inclusion (mathieuProjection K e k) := by
  apply M22ValueBound.Concrete.designAutEquiv.injective
  change M22ValueBound.Concrete.designAutEquiv
    (M22ValueBound.Concrete.designAutEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply, centralModelAction_inner,
    M22ValueBound.Concrete.designAutEquiv_inclusion]
  rfl

omit [Finite G] in
theorem designAction_image (X : Subgroup G) (hXK : X ≤ K) :
    (X.subgroupOf H).map (designAction s e) =
      (nativeImage K X e).map M22ValueBound.Concrete.inclusion := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K := ⟨x.val, hXK hx⟩
    exact mem_map.mpr ⟨mathieuProjection K e k,
      mem_map.mpr ⟨k, hx, rfl⟩, (designAction_inner s e k).symm⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨inclusion s.component_le k, hk, designAction_inner s e k⟩

omit [Finite G] in
theorem design_sylow_normalizes_overlap :
    (T.subgroupOf H).map (designAction s e) ≤
      normalizer ((nativeImage K (K ⊓ M) e).map
        M22ValueBound.Concrete.inclusion : Set m22DesignAut) := by
  rw [← designAction_image s e (K ⊓ M) inf_le_left]
  have hn : T.subgroupOf H ≤ normalizer ((K ⊓ M).subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht j hj
    exact (le_normalizer_iff (H := T) (K := K ⊓ M)).mp
      (sylow_normalizes_overlap s) t.val ht j.val hj
  exact (map_mono hn).trans (le_normalizer_map _)

omit [Finite G] in
theorem normalizes_hexadLift_of_design {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hfix : (T.subgroupOf H).map (designAction s e) ≤
      MulAction.stabilizer m22DesignAut B) :
    T ≤ normalizer (hexadLift K e B : Set G) := by
  let hn := (normal_subgroupOf_iff_le_normalizer s.component_le).mp s.component_normal
  intro t ht
  let tH : H := ⟨t, (Chapter1.isSylowIn_iff.mp s.sylow).2.1 ht⟩
  apply centralModelAction_normalizes_lift H K hn e m22_center_eq_bot
    (MulAction.stabilizer M22 B) tH
  apply MathieuSolvableSpan.innerHexad_normalized ⟨B, hB⟩
  have hf := hfix (mem_map.mpr ⟨tH, ht, rfl⟩)
  exact Subtype.ext hf

theorem exists_native_hexad :
    ∃ B ∈ m22Blocks,
      nativeImage K (K ⊓ M) e ≤ MulAction.stabilizer M22 B ∧
      IsCoatom ((nativeImage K (K ⊓ M) e).subgroupOf (MulAction.stabilizer M22 B)) ∧
      m22HexadPointwiseKernel B ≤ nativeImage K (K ⊓ M) e ∧
      Nat.card (nativeImage K (K ⊓ M) e) = 384 ∧
      T ≤ normalizer (hexadLift K e B : Set G) := by
  obtain ⟨B, hB, hX, hmax, hk, hc, hn⟩ :=
    M22SolvableSylow.hexad_of_solvable_normal_three
      (nativeImage K (K ⊓ M) e) (nativeImage K L₁ e)
      (native_seed_le_overlap s e) (native_seed_normal s e) (native_seed_solvable s e)
      (native_seed_three_dvd s e) (native_overlap_contains_sylow s e)
  exact ⟨B, hB, hX, hmax, hk, hc, normalizes_hexadLift_of_design s e hB
    ((design_sylow_normalizes_overlap s e).trans hn)⟩

omit [Finite G] in
theorem seed_le_hexadLift {B : Finset (Fin 22)}
    (hX : nativeImage K (K ⊓ M) e ≤ MulAction.stabilizer M22 B) :
    L₁ ≤ hexadLift K e B := by
  intro x hx
  exact mem_map.mpr ⟨⟨x, s.seed_le_component hx⟩,
    hX (mem_map.mpr ⟨⟨x, s.seed_le_component hx⟩,
      seed_le_component_overlap s hx, rfl⟩), rfl⟩

theorem native_overlap_solvable : Group.IsSolvable (nativeImage K (K ⊓ M) e) :=
  M22SolvableSylow.solvable_of_solvable_normal_three
    (nativeImage K (K ⊓ M) e) (nativeImage K L₁ e)
    (native_seed_le_overlap s e) (native_seed_normal s e) (native_seed_solvable s e)
    (native_seed_three_dvd s e) (native_overlap_contains_sylow s e)

end MarkedMathieu
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
