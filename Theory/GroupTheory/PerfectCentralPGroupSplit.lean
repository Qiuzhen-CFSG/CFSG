module

public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Splitting central p-group extensions of perfect groups

A finite central extension of a perfect group with cyclic Sylow p-subgroups
splits when its kernel is a p-group. The derived subgroup is perfect and
still surjects onto the quotient. Transfer excludes p from the order of
its kernel, so that restricted projection is an isomorphism. Its inverse
is the section of the original projection constructed here.

This isolates the central-kernel argument used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.1.33(2), printed p.29,
using the transfer theorem recorded in I.1.2, printed p.407.
-/

open Subgroup

namespace PerfectCentralCovering

/-- The section is a homomorphism right inverse to the given projection. -/
public theorem exists_section_of_central_pGroup_kernel
    {E B : Type*} [Group E] [Finite E] [Group B] [Finite B] [Group.IsPerfect B]
    {p : ℕ} [Fact p.Prime] (f : E →* B) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hp : IsPGroup p f.ker)
    (hcyclic : ∀ S : Sylow p B, IsCyclic S) :
    ∃ s : B →* E, f.comp s = MonoidHom.id B := by
  let D := commutator E
  let g : D →* B := f.comp D.subtype
  have hD : D.map f = ⊤ := by
    change (commutator E).map f = ⊤
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hg : Function.Surjective g := by
    intro b
    have hb : b ∈ D.map f := by rw [hD]; trivial
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨⟨d, hd⟩, hdb⟩
  let : Group.IsPerfect D := commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
  have hgc : g.ker ≤ center D := by
    intro d hd
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp (hc hd) x)
  let k : g.ker →* f.ker :=
    (D.subtype.comp g.ker.subtype).codRestrict f.ker (fun x => x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : E)) h
  have hgp : IsPGroup p g.ker := hp.of_injective k hki
  let cover : Cover D B := {
    toMonoidHom := g
    surjective := hg
    isPerfect := inferInstance
    ker_le_center := hgc }
  have hgker : g.ker = ⊥ := by
    rcases hgp.card_eq_or_dvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exact (cover.not_dvd_card_multiplier_of_isCyclic_sylow hcyclic h).elim
  let e : D ≃* B := MulEquiv.ofBijective g
    ⟨(g.ker_eq_bot_iff.mp hgker), hg⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, ?_⟩
  ext b
  exact e.apply_symm_apply b

end PerfectCentralCovering

