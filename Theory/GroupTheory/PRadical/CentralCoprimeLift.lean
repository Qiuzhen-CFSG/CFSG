module
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.PRadical.NormalComponentImages
/-!
# Radical subgroups through central coprime covers

A prime subgroup lifts uniquely through a central coprime kernel, with its
full normalizer. Prime cores map onto prime cores across central covers;
injectivity on the lifted prime core then reflects radicality. This keeps
the scalar center in the SL₃-to-PSL₃ application rather than discarding it.

Source application: Aschbacher--Smith 4.3.16, printed p.618.
-/
public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
/-- A radical prime subgroup lifts with its full normalizer through a central
prime-to-p kernel. -/
theorem exists_radical_lift_of_central_coprime (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hcop : Nat.Coprime p (Nat.card f.ker))
    (R : Subgroup H) (hR : R.IsPRadical p) :
    ∃ A : Subgroup G, A.IsPRadical p ∧ A.map f = R ∧
      (normalizer (R : Set H)).comap f = normalizer (A : Set G) := by
  obtain ⟨A,hA,hm,hn,_,_⟩ := exists_prime_lift_of_central_coprime f hf hk hcop R hR.isPGroup
  let N := normalizer (A : Set G)
  let U := N.pCoreIn p
  let g := f.subgroupMap N
  have hg : g.ker ≤ center N := by
    intro x hx
    have hh : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hh) y)
  have he := g.map_pCore_of_central_kernel (f.subgroupMap_surjective N) hg (p := p)
  have hU := congrArg (map (N.map f).subtype) he
  change ((pCore p N).map g).map (N.map f).subtype = (N.map f).pCoreIn p at hU
  rw [map_map] at hU
  have hgf : (N.map f).subtype.comp g = f.comp N.subtype := rfl
  rw [hgf,←map_map] at hU
  have hn' : N.map f = normalizer (R : Set H) := by
    rw [show N = (normalizer (R : Set H)).comap f from hn.symm,
      map_comap_eq_self_of_surjective hf]
  change U.map f = _ at hU
  rw [hn',pCoreIn,hR.2] at hU
  have hAU : A ≤ U := le_map_pCore_normalizer hA
  have hUA : U ≤ A := by
    intro x hx
    obtain ⟨a,ha,hax⟩ := hm.symm ▸ hU ▸ mem_map_of_mem f hx
    have hi := injective_comp_subtype_of_coprime_ker f hcop U (isPGroup_pCoreIn p N)
    have he : (⟨a,hAU ha⟩ : U) = ⟨x,hx⟩ := hi hax
    have heq : a = x := congrArg Subtype.val he
    exact heq ▸ ha
  refine ⟨A,⟨?_,le_antisymm hUA hAU⟩,hm,hn⟩
  intro he
  exact hR.1 (by rw [←hm,he,map_bot])
end Subgroup
