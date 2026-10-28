module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.Quotient
/-!
# Odd residuals from a permuted family of supports

If the support permutation group is a two-group, the two-residual fixes each
support. Perfectness maps it into each support image's two-residual. When
the supports span and the original action is faithful, the resulting map
into their product is injective. Odd support residuals therefore give an odd
ambient two-residual.

Application: the two-factor case of Aschbacher–Smith 15.1.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation
variable {G V ι : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype ι]

theorem odd_twoResidual_of_permuted_supports
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (W : ι → Submodule (ZMod 2) V) (hfull : iSup W = ⊤)
    (π : G →* Equiv.Perm ι) (hπ : IsPGroup 2 (Equiv.Perm ι))
    (hp : ∀ g i, (W i).map (ρ g) = W (π g i))
    (hodd : ∀ i, Odd (Nat.card (pResidual 2 (subspaceActionImage ρ (W i))))) :
    Odd (Nat.card (pResidual 2 G)) := by
  classical
  let R := pResidual 2 G
  have hR : R ≤ π.ker := pResidual_le_ker_of_isPGroup 2 π hπ
  have hWi (i : ι) : R ≤ subspaceStabilizer ρ (W i) := by
    apply le_subspaceStabilizer
    intro g hg w hw
    have he := hp g i
    have hgπ : π g = 1 := hR hg
    rw [hgπ] at he
    change (W i).map (ρ g) = W i at he
    exact he ▸ Submodule.mem_map_of_mem hw
  let f (i : ι) : R →* subspaceActionImage ρ (W i) :=
    subgroupActionHom ρ (W i) R (hWi i)
  have hri (i : ι) (r : R) : f i r ∈ pResidual 2 (subspaceActionImage ρ (W i)) := by
    have he : pResidual 2 R = ⊤ := (pResidual_eq_top_iff 2 R).mpr (isPPerfect_pResidual 2)
    apply map_pResidual_le 2 (f i)
    exact mem_map_of_mem (f i) (he ▸ mem_top r)
  let q : R →* (∀ i, pResidual 2 (subspaceActionImage ρ (W i))) :=
    MonoidHom.pi fun i => (f i).codRestrict _ (hri i)
  have hq : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    apply hf
    have hh : ∀ i, W i ≤ LinearMap.eqLocus (ρ a) (ρ b) := by
      intro i w hw
      have he := congrArg (fun x => ((subspaceImageRepresentation ρ (W i)) (x i)
        ⟨w,hw⟩ : V)) hab
      exact he
    have hall : (⊤ : Submodule (ZMod 2) V) ≤ LinearMap.eqLocus (ρ a) (ρ b) := by
      rw [←hfull]
      exact iSup_le hh
    ext w
    exact hall (Submodule.mem_top)
  apply Odd.of_dvd_nat _ (card_dvd_of_injective q hq)
  rw [Nat.card_pi]
  have hprod : ∀ s : Finset ι,
      Odd (∏ i ∈ s, Nat.card (pResidual 2 (subspaceActionImage ρ (W i)))) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih => simpa only [Finset.prod_insert hi] using (hodd i).mul ih
  exact hprod Finset.univ
end Representation
