module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import BenderSuzuki.External.Huppert.XI.SubgroupNonsolvable
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Simple sections of the concrete Suzuki groups

Every subgroup is either solvable or isomorphic to a positive-parameter
Suzuki group. In the latter case simplicity makes any simple quotient
isomorphic to that subgroup. Thus every simple section is prime cyclic or
Suzuki, and belongs to the constructed part of the full catalogue.

Sources: Huppert–Blackburn, *Finite Groups III*, XI.3.6 and XI.3.12(e),
using XI.11.15; Aschbacher–Smith, Theorem 0.1.2(1), printed p.4.
The conclusion uses actual model equivalences, including across universes.
The full-K conclusion still requires inclusion of this partial catalogue
in the complete known-simple catalogue, which the main assembly must supply.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open BenderSuzuki.MatrixGroups BenderSuzuki.External

/-- All simple sections of a Suzuki model belong to the constructed catalogue. -/
public theorem suzuki_isKGroup_constructed {m : ℕ} (hm : 1 ≤ m)
    {G : Type*} [Group G] (e : G ≃* SuzukiMatrixGroup m) :
    IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  by_cases hsolv : Group.IsSolvable U
  · let := hsolv
    let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
    exact .cyclic (primeCyclic_of_solvable_simple S)
  · let eU := Subgroup.equivMapOfInjective U e.toMonoidHom e.injective
    have hnot : ¬ Group.IsSolvable (U.map e.toMonoidHom) := by
      intro hs
      let := hs
      exact hsolv (Group.isSolvable_of_isSolvable_injective
        (f := eU.toMonoidHom) eU.injective)
    obtain ⟨k, hk, ⟨a⟩⟩ :=
      suzukiSubgroup_exists_mulEquiv_of_not_isSolvable (by omega) _ hnot
    let := (huppert_blackburn_XI_3_6 k hk).1
    let : IsSimpleGroup U := (eU.trans a).isSimpleGroup
    have hinj : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff f).mp
      rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨s, hs⟩ := exists_ne (1 : S)
        obtain ⟨u, rfl⟩ := hf s
        have hu : u ∈ f.ker := by rw [h]; trivial
        exact hs hu
    exact .suzuki k (by omega)
      ⟨(MulEquiv.ofBijective f ⟨hinj, hf⟩).symm.trans (eU.trans a)⟩

/-- The main assembly may enlarge the proved concrete section list to full K. -/
public theorem suzuki_properK_of_catalogue {G : Type*} [Group G] [Finite G]
    {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m) :
    HasProperKSubgroups K G := by
  apply IsKGroup.properK
  intro S _ hS U f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (suzuki_isKGroup_constructed hm e S hS U f hf)

end CFSG.Quasithin.MainConverse
