module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import BenderSuzuki.External.Huppert.XI.SubgroupNonsolvable
public import Theory.ElementaryAbelian.Quotient

/-!
# Solvability of the embedded centralizer

A nonsolvable subgroup of a Suzuki group is itself a positive-parameter
Suzuki group. Its Sylow two-subgroups have order q², whereas their first
omega subgroups have order q. Thus a subgroup with an elementary abelian
Sylow two-subgroup must be solvable. Applying this to the literal embedding
of J into L discharges the solvability conclusion once the conjugate-subgroup
argument of Lemma 14.3 has proved U elementary abelian.

Source: GLS4, Chapter 2, Lemma 14.3(b), using Chapter 4, Lemma 3.8, and
Huppert–Blackburn, Finite Groups III, XI.11.15.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.centralizer_solvable_of_elementary_sylow
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (U : Subgroup G) (hU : IsElementaryAbelian 2 U)
    (hs : ∃ V : Sylow 2 (centralizer (residualGenerated M z t : Set G)),
      (V : Subgroup (centralizer (residualGenerated M z t : Set G))).map
        (centralizer (residualGenerated M z t : Set G)).subtype = U) :
    Group.IsSolvable (centralizer (residualGenerated M z t : Set G)) := by
  let J := centralizer (residualGenerated M z t : Set G)
  let g := d.model.toMonoidHom.comp f
  have hg : Function.Injective g := d.model.injective.comp hf
  let e := MonoidHom.ofInjective hg
  by_contra hsol
  have hr : ¬ Group.IsSolvable g.range := by
    intro h
    let := h
    exact hsol (Group.isSolvable_of_isSolvable_injective e.injective)
  obtain ⟨k, hk, ⟨ek⟩⟩ := External.suzukiSubgroup_exists_mulEquiv_of_not_isSolvable
    d.parameter_pos g.range hr
  obtain ⟨V, hV⟩ := hs
  let eV : V ≃* U := ((V : Subgroup J).equivMapOfInjective J.subtype
    J.subtype_injective).trans (MulEquiv.subgroupCongr hV)
  let := hU
  have : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.of_surjective eV.symm.toMonoidHom eV.symm.surjective
  have hc := suzukiSylow_omega_card hk (e.trans ek) V
  rw [omegaOneAmbient_eq_self, suzukiSylow_card hk (e.trans ek) V] at hc
  have hq : 1 < 2 ^ (2 * k + 1) := Nat.one_lt_pow (by omega) (by decide)
  nlinarith

end BenderSuzuki.ZD.SuzukiExclusion
