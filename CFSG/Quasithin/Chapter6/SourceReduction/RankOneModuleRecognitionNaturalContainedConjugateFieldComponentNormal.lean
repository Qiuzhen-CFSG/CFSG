module
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.SolvableRadical
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Identifying the normal component above the field residual

A normal containing C-component has a proper centralizer kernel, hence a
solvable kernel. Its join with the centralizer Sylow is solvable and lies
in M by the previously proved weak-closure control. Frattini then puts the
whole C-component in M. The local perfect subgroup is normal there, so
minimality of the C-component identifies them. All normality is relative
to the group in which the argument is applied.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671, using 1.2.4 and A.3.3.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A normal containing C-component is controlled by the solvable kernel
of its action. Frattini then identifies the perfect local subgroup with it. -/
theorem field_component_normal_of_solvable_control
    (C K D M R : Subgroup G) [C.Normal] [K.Normal]
    (hK : K.IsCComponent) (hDK : D ≤ K) (hDper : Group.IsPerfect D)
    (hDC : ¬ D ≤ C) (hDM : K ⊓ M ≤ normalizer (D : Set G))
    (hR : Chapter1.IsSylowIn 2 R C) (hNR : normalizer (R : Set G) ≤ M)
    (hsolv : ∀ X : Subgroup G, Group.IsSolvable X → X ≤ C → R ≤ X → X ≤ M) :
    D.Normal := by
  let A := K ⊓ C
  have hAC : A ≤ C := inf_le_right
  have hAK : A ≤ K := inf_le_left
  have hAper : C.subgroupOf K ≠ ⊤ := by
    intro he
    apply hDC
    intro d hd
    have hh : (⟨d, hDK hd⟩ : K) ∈ C.subgroupOf K := he ▸ mem_top _
    exact hh
  let : Group.IsSolvable (C.subgroupOf K) :=
    hK.isSolvable_of_subnormal_lt_top
      (inferInstance : (C.subgroupOf K).Normal).isSubnormal hAper
  let f : A →* C.subgroupOf K :=
    { toFun a := ⟨⟨a, a.property.1⟩, a.property.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := f) (fun a b he => Subtype.ext (congrArg (fun x : C.subgroupOf K => (x : G)) he))
  have hRp : IsPGroup 2 R := (Chapter1.isSylowIn_iff.mp hR).1
  have hRC : R ≤ C := (Chapter1.isSylowIn_iff.mp hR).2.1
  let : Group.IsNilpotent R := hRp.isNilpotent
  let X := A ⊔ R
  let : Group.IsSolvable X := Group.isSolvable_sup_of_normal_left A R
  have hXC : X ≤ C := sup_le hAC hRC
  have hXM : X ≤ M := hsolv X inferInstance hXC le_sup_right
  have hXeq : X = (K ⊔ R) ⊓ C := by
    apply le_antisymm (le_inf (sup_le (hAK.trans le_sup_left) le_sup_right) hXC)
    rintro x ⟨hx, hxC⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_sup_of_normal_left.mp hx
    have hkC : k ∈ C := by
      have hh := C.mul_mem hxC (C.inv_mem (hRC hr))
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem (mem_sup_left ⟨hk, hkC⟩) (mem_sup_right hr)
  have hXKR : X ≤ K ⊔ R := hXeq.le.trans inf_le_left
  have hnorm : K ⊔ R ≤ normalizer (X : Set G) := by
    rw [hXeq]
    exact (le_inf (K ⊔ R).le_normalizer (by rw [normalizer_eq_top]; exact le_top)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨S, hS⟩ := hR.restrict (show R ≤ X from le_sup_right) hXC
  have hKM : K ≤ M := by
    have hf := le_normalizer_sylow_sup X (K ⊔ R) hXKR hnorm S
    rw [hS] at hf
    exact (le_sup_left.trans hf).trans (sup_le hNR hXM)
  have hnD : (D.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDK).mpr
      ((le_inf le_rfl hKM).trans hDM)
  have hDsub : D.IsSubnormal := by
    have hh := hnD.isSubnormal.trans' (inferInstance : K.Normal).isSubnormal
    simpa only [map_subgroupOf_eq_of_le hDK] using hh
  have hDne : D ≠ ⊥ := fun he => hDC (he ▸ bot_le)
  have he : D = K := le_antisymm hDK (hK.minimal D hDK hDne hDper hDsub)
  exact he ▸ inferInstance
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
