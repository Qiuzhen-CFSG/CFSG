module

public import Stellmacher.SectionThree.LemmaThreeFour
public import Theory.Frattini.PGroup

/-!
# Transferring `Φ₂` to an odd `p`-group image

For a surjection from a finite subgroup `U` to an odd `p`-group, the normal
`2`-core of `U` vanishes in the image. The induced quotient map therefore
sends `Φ(U/O₂(U))`, and hence Stellmacher's ambient `Φ₂(U)`, into the
ordinary Frattini subgroup of the image. This is the non-Frattini transfer
used while lifting Lemma (3.6).
-/

namespace Stellmacher.SectionThree

universe u v

@[expose] public section

theorem phiTwo_map_le_frattini_of_surjective_odd_pGroup
    {G : Type u} {V : Type v}
    [Group G] [Finite G] [Group V] [Finite V]
    (U : Subgroup G) (f : U →* V) (hf : Function.Surjective f)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hVp : IsPGroup p V) :
    ((phiTwo U).subgroupOf U).map f ≤ frattini V := by
  classical
  let O : Subgroup U := pCore 2 U
  have hOtwo : IsPGroup 2 O := pCore_isPGroup
  have hOmapTwo : IsPGroup 2 (O.map f) := IsPGroup.map hOtwo f
  have hOmapP : IsPGroup p (O.map f) := hVp.to_subgroup (O.map f)
  have hpne : 2 ≠ p := by
    intro h
    subst p
    obtain ⟨n, hn⟩ := hpodd
    omega
  have hOmapBot : O.map f = ⊥ := by
    have hdisj : Disjoint (O.map f) (O.map f) :=
      IsPGroup.disjoint_of_ne 2 p hpne (O.map f) (O.map f)
        hOmapTwo hOmapP
    exact disjoint_self.mp hdisj
  have hOleKer : O ≤ f.ker := (Subgroup.map_eq_bot_iff O).mp hOmapBot
  let fbar : U ⧸ O →* V := QuotientGroup.lift O f hOleKer
  have hfbar : Function.Surjective fbar := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' O x, by simp [fbar]⟩
  have hPhi : frattini (U ⧸ O) ≤ (frattini V).comap fbar :=
    frattini_le_comap_frattini_of_surjective hfbar
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  change (x : G) ∈ phiTwo U at hx
  rcases hx with ⟨z, hz, hzx⟩
  have hzxU : z = x := U.subtype_injective hzx
  subst z
  change QuotientGroup.mk' O x ∈ frattini (U ⧸ O) at hz
  have := hPhi hz
  change fbar (QuotientGroup.mk' O x) ∈ frattini V at this
  simpa [fbar] using this

end

end Stellmacher.SectionThree
