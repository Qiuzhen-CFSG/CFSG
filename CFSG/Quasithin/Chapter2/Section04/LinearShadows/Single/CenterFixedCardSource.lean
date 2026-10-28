module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterDisplacementSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource

/-!
# The actual fixed-center order of a noncentral involution

Transport the Singer-normalizer fixed-space count through the literal
conjugation action on Z(R). Its fixed subgroup has order 2^m with n=2m.
This is the numerical center calculation in Aschbacher–Smith, 2.4.14(2),
used in the original transfer argument on printed p.539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_center_involution_fixed_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (a : G) (haT : a ∈ T) (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    a ∉ centralizer (Z : Set G) →
    ∃ m : ℕ, 0 < m ∧ n=2*m ∧ Nat.card (Z ⊓ centralizer ({a} : Set G) : Subgroup G)=2^m := by
  intro R Z han
  obtain ⟨hTZ,hEA,C,hC,hreg,hn⟩ := source_centerless_center_action_normalizer
    d hG T hST hsingle hL hM hTM hunique c hZ
  let := hEA
  let := hC
  let α := Z.normalizerMonoidHom.comp (inclusion hTZ)
  let t := α ⟨a,haT⟩
  have ht : t ≠ 1 := by
    intro he
    apply han
    intro w hw
    have hh := congrArg (fun f : MulAut Z => (f ⟨w,hw⟩ : G)) he
    change a*w*a⁻¹=w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have ht2 : t^2=1 := by
    have hh : (⟨a,haT⟩ : T)^2=1 := Subtype.ext ha2
    change (α ⟨a,haT⟩)^2=1
    rw [←map_pow,hh,map_one]
  have hc := regular_cyclic_automorphism_normalizer_involution_fixed_card C hreg t ht ht2
    (hn ⟨⟨a,haT⟩,rfl⟩)
  let F := Z ⊓ centralizer ({a} : Set G)
  let e : t.toMonoidHom.eqLocus (MonoidHom.id Z) ≃ F := {
    toFun := fun z => ⟨z.val, z.val.property, mem_centralizer_singleton_iff.mpr (by
      have he := congrArg Subtype.val z.property
      change a * z.val.val * a⁻¹ = z.val.val at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm)⟩
    invFun := fun z => ⟨⟨z.val,z.property.1⟩, Subtype.ext (by
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp z.property.2).symm)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e] at hc
  have hzdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  rw [distinguishedZ_of_centerless d hZ] at hzdata
  rw [hzdata.2.1] at hc
  obtain ⟨m,hm⟩ := ((IsElementaryAbelian.isPGroup 2 Z).to_le
    (show F≤Z from inf_le_left)).exists_card_eq
  rw [hm,←pow_mul] at hc
  have hn : m*2=n := Nat.pow_right_injective (by decide : 1<2) hc
  refine ⟨m,?_,by omega,hm⟩
  have := hL.1
  omega
end CFSG.Quasithin.Chapter2.LinearShadows.Single
