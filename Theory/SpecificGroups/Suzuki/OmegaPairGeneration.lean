module
public import Theory.SpecificGroups.Suzuki.OmegaGeneration
public import Theory.SpecificGroups.Suzuki.TwoConjugateWitness.RootPair
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Two conjugate Suzuki Sylow centers generate

For q > 2, the first omega of a Sylow two-subgroup and one of its
conjugates generate the actual Suzuki group. Align the Sylow with the
standard root. The elementary opposite-pair calculation puts the Weyl
involution in the generated pair, and root-omega generation finishes.
Transport both subgroups through that same aligned equivalence.

The source application uses the image of the actual radius-one span,
proved to be a Sylow center in DGS (12.3)(a), to construct the two actors
needed in (12.6). No generation witness is assumed there. This lemma does
not cover Sz(2), where two involutions cannot generate the group of order 20.

Sources: GLS IV, 4.3.2(h); Huppert--Blackburn III, XI.3.12(e), XI.11.15;
DGS85, Groups and Graphs, (12.6), printed p.183.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- A conjugate of the full Sylow omega supplies a second generator subgroup. -/
theorem suzukiSylow_exists_omega_pair {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 0 < n)
    (e : G ≃* SuzukiMatrixGroup n) (P : Sylow 2 G) :
    ∃ g : G, omegaOneAmbient (P : Subgroup G) ⊔
      (omegaOneAmbient (P : Subgroup G)).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨f,hP,_⟩ := suzukiSylow_aligned_equiv hn e P
  let E := omegaOneAmbient (SuzukiRootSubgroup n)
  let := suzukiRootSubgroup_omega_elementary n hn
  have hne : E ≠ ⊥ := by
    intro he
    have hc := suzukiRootSubgroup_omega_card n hn
    rw [show omegaOneAmbient (SuzukiRootSubgroup n) = ⊥ from he,card_bot] at hc
    have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*n+1 ≠ 0)
    omega
  have hw : suzukiWeyl n ∉ SuzukiBorelSubgroup n := by
    intro hh
    have he : suzukiWeyl n • suzukiOvoidInfinity n = suzukiOvoidInfinity n := by
      simpa only [suzukiBorelSubgroup_eq_stabilizer n hn, MulAction.mem_stabilizer_iff] using hh
    rw [suzukiWeyl_smul_infinity] at he
    exact suzukiOvoidInfinity_ne_zero n he.symm
  have hgen : E ⊔ E.map (MulAut.conj (suzukiWeyl n)).toMonoidHom = ⊤ := by
    apply top_unique
    rw [← suzukiRootSubgroup_omega_sup_zpowers_eq_top n hn (suzukiWeyl n) hw]
    exact sup_le le_sup_left (zpowers_le.mpr
      (suzuki_weyl_mem_elementary_pair hn E (omegaOneAmbient_le _) hne))
  have hE : E.map f.toMonoidHom = omegaOneAmbient (P : Subgroup G) := by
    rw [map_omegaOneAmbient_injective f.toMonoidHom f.injective,hP]
  refine ⟨f (suzukiWeyl n),?_⟩
  have he : f.toMonoidHom.comp (MulAut.conj (suzukiWeyl n)).toMonoidHom =
      (MulAut.conj (f (suzukiWeyl n))).toMonoidHom.comp f.toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  have hh := congrArg (Subgroup.map f.toMonoidHom) hgen
  rw [Subgroup.map_sup,map_map,he,←map_map,hE,Subgroup.map_top_of_surjective _ f.surjective] at hh
  exact hh

end BenderSuzuki.MatrixGroups

