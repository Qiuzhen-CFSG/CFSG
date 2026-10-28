module

public import Theory.Representation.BinaryConjugationSection.CoprimeRootFixedLifting

/-!
# Factoring the actual fixed core through two root centralizers

When the two root-fixed subspaces span the fixed space of their coprime
normalizer, lift both coordinates while retaining that normalizer. The
remaining coordinate kernel is central, so it can be absorbed in the first
factor. This is a literal elementwise product, stronger than generation.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W]
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- The whole actual fixed core is the product of its two root centralizers,
with the factors in the specified order and the central kernel retained. -/
theorem fixed_core_two_root_factorization (d : BinaryConjugationSection H U Z ρ)
    (A R S : Subgroup G) (hAH : A≤H) (hRH : R≤H) (hSH : S≤H)
    (hsolv : Group.IsSolvable U) (hcop : Nat.Coprime (Nat.card A) (Nat.card U))
    (hR : ⁅R,A⁆=R) (hS : ⁅S,A⁆=S) (hZH : Z≤centralizer (H:Set G))
    (hspan : fixedSpace ρ (R.subgroupOf H) ⊔ fixedSpace ρ (S.subgroupOf H)=
      fixedSpace ρ (A.subgroupOf H)) :
    ∀ v∈U⊓centralizer (A:Set G),
      ∃ a∈U⊓centralizer (A:Set G)⊓centralizer (R:Set G),
      ∃ b∈U⊓centralizer (A:Set G)⊓centralizer (S:Set G), v=a*b := by
  intro v hv
  let vU : U := ⟨v,hv.1⟩
  have hw : (d.coordinates vU).toAdd∈fixedSpace ρ (A.subgroupOf H) := by
    intro a
    change ρ (a:H) (d.coordinates vU).toAdd=(d.coordinates vU).toAdd
    rw [←d.equivariant (a:H) vU]
    congr 2
    apply Subtype.ext
    change (a:G)*v*(a:G)⁻¹=v
    rw [hv.2 a a.property,mul_inv_cancel_right]
  rw [←hspan,Submodule.mem_sup] at hw
  obtain ⟨x,hx,y,hy,hxy⟩ := hw
  have hZA : Z≤centralizer (A:Set G) := hZH.trans (centralizer_le hAH)
  obtain ⟨a,ha,hax⟩ := d.exists_centralizing_root_lift A R hAH hRH hsolv hcop hR hZA
    x hx (hspan ▸ (show x∈fixedSpace ρ (R.subgroupOf H) ⊔ fixedSpace ρ (S.subgroupOf H) from
      (show fixedSpace ρ (R.subgroupOf H)≤_ from le_sup_left) hx))
  obtain ⟨b,hb,hby⟩ := d.exists_centralizing_root_lift A S hAH hSH hsolv hcop hS hZA
    y hy (hspan ▸ (show y∈fixedSpace ρ (R.subgroupOf H) ⊔ fixedSpace ρ (S.subgroupOf H) from
      (show fixedSpace ρ (S.subgroupOf H)≤_ from le_sup_right) hy))
  let z : U := vU/(a*b)
  have hzZ : (z:G)∈Z := by
    apply (d.coordinates_eq_one_iff z).mp
    change d.coordinates (vU/(a*b))=1
    rw [map_div,div_eq_one,map_mul]
    apply Multiplicative.toAdd.injective
    change (d.coordinates vU).toAdd=(d.coordinates a).toAdd+(d.coordinates b).toAdd
    rw [hax,hby]
    exact hxy.symm
  refine ⟨(z:G)*a,⟨⟨U.mul_mem z.property a.property,
    (centralizer (A:Set G)).mul_mem (hZA hzZ) ha.1⟩,
    (centralizer (R:Set G)).mul_mem (hZH.trans (centralizer_le hRH) hzZ) ha.2⟩,
    b,⟨⟨b.property,hb.1⟩,hb.2⟩,?_⟩
  change v=(((v/((a:G)*b))*(a:G))*(b:G))
  rw [div_eq_mul_inv]
  group

end Representation.BinaryConjugationSection
