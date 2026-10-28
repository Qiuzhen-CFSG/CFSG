module
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.Tactic

/-!
# Returning points under a full four-group action

A full conjugation action on an elementary four-group is transitive on
its order-two subgroups. If the normalizer of a marked point preserves
an abelian subgroup U containing the plane, any returning conjugate of
U equals a conjugate under the acting group and centralizes the plane.

The same full action extends to every overgroup normalizing the plane.
Its literal centralizer quotient has trivial two-core, so the plane is
reduced there. When the action kernel is the two-core, this also constructs
the actual quotient isomorphism with S₃.

These finite-group arguments supply the returning-point and reducedness
premises in Aschbacher–Smith, proof of 14.7.32 and application of 14.7.31(2),
printed p.1058, refs/quasithin.pdf. Conjugation is displayed as the literal
map x ↦ g x g⁻¹; source consumers translate their right-conjugation convention.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_mul (A : Subgroup G) (a b : G) :
    A.map (MulAut.conj (a * b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
/-- A conjugate of a marked order-two subgroup in the plane can be
reached by an element of the full acting group. -/
theorem full_four_action_point_orbit
    (Y P Z : Subgroup G) [IsKleinFour P]
    (hZ : Nat.card Z = 2) (hZP : Z ≤ P)
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹)
    (g : G) (hg : Z.map (MulAut.conj g).toMonoidHom ≤ P) :
    ∃ y ∈ Y, Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj y).toMonoidHom := by
  classical
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hgen : zpowers (z : G) = Z := by
    have hh := congrArg (Subgroup.map Z.subtype) (zpowers_eq_top_of_prime_card hZ hz)
    rwa [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
  let zP : P := ⟨z,hZP z.property⟩
  let w : G := (MulAut.conj g) z
  have hwP : w ∈ P := hg (mem_map_of_mem _ z.property)
  have hw1 : w ≠ 1 := fun he => hz1 ((MulAut.conj g).injective
    (he.trans (map_one _).symm))
  let wP : P := ⟨w,hwP⟩
  let a : MulAut P := IsKleinFour.mulEquiv (Equiv.swap zP wP)
    (Equiv.swap_apply_of_ne_of_ne
      (fun he => hz1 (congrArg Subtype.val he).symm)
      (fun he => hw1 (congrArg Subtype.val he).symm))
  obtain ⟨y,hy⟩ := hσ a
  have he : (y : G) * z * (y : G)⁻¹ = w := by
    have hh := congrArg (fun f : MulAut P => (f zP : G)) hy
    simpa only [hconj,a,IsKleinFour.mulEquiv,IsKleinFour.mulEquiv',
      MulEquiv.coe_mk,Equiv.swap_apply_left] using hh
  refine ⟨y,y.property,?_⟩
  rw [←hgen,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  exact congrArg zpowers he.symm

omit [Finite G] in
/-- Transport the abelian subgroup attached to a returning point into
the plane centralizer, retaining an actual internal conjugator. -/
theorem full_four_action_returning
    (Y P Z U : Subgroup G) [IsKleinFour P] [IsMulCommutative U]
    (hZ : Nat.card Z = 2) (hZP : Z ≤ P) (hPU : P ≤ U) (hUY : U ≤ Y)
    (hYN : Y ≤ normalizer (P : Set G))
    (hNU : normalizer (Z : Set G) ≤ normalizer (U : Set G))
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹)
    (g : G) (hg : Z.map (MulAut.conj g).toMonoidHom ≤ P) :
    ∃ y ∈ Y, U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj y).toMonoidHom ∧
      U.map (MulAut.conj g).toMonoidHom ≤ Y ⊓ centralizer (P : Set G) := by
  obtain ⟨y,hy,he⟩ := full_four_action_point_orbit Y P Z hZ hZP σ hσ hconj g hg
  have hnZ : y⁻¹ * g ∈ normalizer (Z : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Z.map (MulAut.conj (y⁻¹ * g)).toMonoidHom = Z
    rw [map_conj_mul,he,←map_conj_mul,inv_mul_cancel]
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hid,map_id]
  have heU : U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj y).toMonoidHom := by
    calc
      _ = U.map (MulAut.conj (y * (y⁻¹ * g))).toMonoidHom := by rw [mul_inv_cancel_left]
      _ = (U.map (MulAut.conj (y⁻¹ * g)).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := map_conj_mul U y (y⁻¹ * g)
      _ = _ := by
        have hh : U.map (MulAut.conj (y⁻¹ * g)).toMonoidHom = U :=
          mem_normalizer_iff_map_conj_eq.mp (hNU hnZ)
        rw [hh]
  refine ⟨y,hy,heU,?_⟩
  rw [heU]
  have hYP : P.map (MulAut.conj y).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (hYN hy)
  have hUC : U ≤ centralizer (P : Set G) := (le_centralizer U).trans (centralizer_le hPU)
  apply le_inf
  · exact (map_mono hUY).trans_eq (mem_normalizer_iff_map_conj_eq.mp (Y.le_normalizer hy))
  · have hm := map_mono (f := (MulAut.conj y).toMonoidHom) hUC
    exact (hm.trans (map_centralizer_le_centralizer_image _ _)).trans_eq
      (congrArg (fun A : Subgroup G => centralizer (A : Set G)) hYP)

omit [Finite G] in
/-- A full conjugation action stays full in every normalizing overgroup. -/
theorem full_conjugation_surjective_overgroup
    (Y A P : Subgroup G) (hYA : Y ≤ A) (hAN : A ≤ normalizer (P : Set G))
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹) :
    Function.Surjective (P.normalizerMonoidHom.comp (inclusion hAN)) := by
  intro a
  obtain ⟨y,hy⟩ := hσ a
  refine ⟨inclusion hYA y,?_⟩
  rw [←hy]
  ext v
  exact (hconj y v).symm

/-- The actual plane is reduced when its conjugation action is full. -/
theorem full_four_action_reduced
    (Y P : Subgroup G) [IsElementaryAbelian 2 P] [IsKleinFour P]
    (hPY : P ≤ Y) (hYN : Y ≤ normalizer (P : Set G))
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹) :
    Theory.GroupTheory.IsPReduced 2 (P.subgroupOf Y) := by
  let hn : (P.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hPY).mpr hYN
  let := hn
  have hk : σ.ker = centralizer (P.subgroupOf Y : Set Y) := by
    ext y
    constructor
    · intro hy x hx
      have he := congrArg (fun a : MulAut P => (a ⟨x,hx⟩ : G)) hy
      rw [hconj] at he
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hy
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [hconj]
      have he := congrArg Subtype.val (hy ⟨v,hPY v.property⟩ v.property)
      change (v : G) * (y : G) = (y : G) * v at he
      change (y : G) * (v : G) * (y : G)⁻¹ = v
      rw [←he,mul_inv_cancel_right]
  have hred : pCore 2 (MulAut P) = ⊥ := by
    have hh := IsKleinFour.twoCore_le_ker_of_surjective P
      (MonoidHom.id (MulAut P)) Function.surjective_id
    simpa only [MonoidHom.ker_id,le_bot_iff] using hh
  refine ⟨hn,IsElementaryAbelian.subgroupOf hPY,?_⟩
  let e := QuotientGroup.liftEquiv (centralizer (P.subgroupOf Y : Set Y)) hσ hk.symm
  have hm := pCore_map_iso 2 e
  rw [hred] at hm
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hm

omit [Finite G] in
/-- A full four-group action with two-core kernel constructs the S₃ quotient. -/
theorem full_four_action_core_quotient
    (Y P : Subgroup G) [IsKleinFour P]
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹)
    (hcore : Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2) :
    Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) := by
  have hk : σ.ker = (centralizer (P : Set G)).subgroupOf Y := by
    ext y
    constructor
    · intro hy x hx
      have he := congrArg (fun a : MulAut P => (a ⟨x,hx⟩ : G)) hy
      rw [hconj] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hy
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [hconj]
      change (y : G) * (v : G) * (y : G)⁻¹ = v
      have hh : (v : G) * (y : G) = (y : G) * v := hy v v.property
      rw [←hh,mul_inv_cancel_right]
  have he : σ.ker = pCore 2 Y := by
    apply map_injective Y.subtype_injective
    rw [hk,subgroupOf_map_subtype]
    exact (inf_comm _ _).trans hcore
  exact ⟨(QuotientGroup.liftEquiv (pCore 2 Y) hσ he.symm).trans
    (IsKleinFour.autEquivPermThree P)⟩


end Subgroup
