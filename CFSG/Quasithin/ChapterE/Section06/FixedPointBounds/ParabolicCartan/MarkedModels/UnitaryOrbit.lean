module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.OrbitDegree
public import Theory.SpecificGroups.SU3.IsotropicBorelAction
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional

/-!
# The normal unitary Borel orbit obstruction

The literal normal-core quotient acts faithfully on its marked PSU₃ factor:
the factor centralizer lies in the Sylow image and hence in the overlap,
whose normal core is trivial. Its two-rank is at most n+1. This does not
identify the overlap core with O₂(H); a possible odd scalar center remains.

The marked isotropic-point orbit has size 2^(3n)+1. A nonzero invariant
binary polar form and a spanning Borel-fixed seed cannot admit a totally
singular subspace of codimension at most n+2. This is the normal unitary
branch of the argument leading to Aschbacher–Smith 14.2.16, pp.985–986.
-/

public section
open Subgroup Module Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G W : Type*} [Group G]
variable [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The unitary isotropic-point orbit is too large for the source singular codimension. -/
theorem ModelBorelPair.unitary_polar_false
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (M K S : Subgroup G) [K.Normal] (hgen : K ⊔ S = ⊤) (hSM : S ≤ M)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2^n)
    (hm : ModelBorelPair M K (unitaryBorel J hJ))
    (ρ : Representation (ZMod 2) G W) (v : W)
    (hfix : ∀ g ∈ M, ρ g v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g v)) = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (hmE : finrank (ZMod 2) (W ⧸ E) ≤ n+2) : False := by
  obtain ⟨hc,a,o,ho,htwo⟩ := HermitianForm.IsotropicBorelAction.exists_action J hJ
    (2^n) hF hfixed
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J)
    (BenderSuzuki.Converse.psuOmega J) := a
  have hm' : ModelBorelPair M K
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) o) := ho.symm ▸ hm
  have hb := hm'.orbit_degree_bound M K S hgen hSM o htwo
    ρ v hfix hspan B hB hne hinv E hE (n+2) hmE
  rw [hc] at hb
  have hp : 2^(n*3)+1 ≤ 2*(n*3+1)+1 := by
    rw [pow_mul]
    omega
  have he := UniformBinaryPolar.linear_field_degree (n*3) (by omega) hp
  omega

variable {H : Type*} [Group H] [Finite H]

/-- The faithful normal-core quotient has two-rank at most the unitary automorphism rank. -/
theorem ModelBorelPair.unitary_source_actor_two_rank
    (S : Sylow 2 H) (N K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (S : Subgroup H) = ⊤) (hSN : (S : Subgroup H) ≤ N)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^n))
    (hfixed : Nat.card {x : F // J.conj x = x} = 2^n)
    (hm : ModelBorelPair N K (unitaryBorel J hJ)) :
    primeRank 2 (H ⧸ sourceKernel N) ≤ n+1 := by
  obtain ⟨e,_⟩ := hm
  let q := QuotientGroup.mk' (sourceKernel N)
  let L := K.map q
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (sourceKernel N))
  let eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J := e
  have hLs : L ⊔ (S' : Subgroup (H ⧸ sourceKernel N)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup H).map q = ⊤
    rw [←Subgroup.map_sup,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hnfix : ∃ x : F, J.conj x ≠ x := by
    by_contra! h
    have hc : Nat.card {x : F // J.conj x = x} = Nat.card F :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hF,hfixed] at hc
    have hp : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  have hLZ : center L = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hh : eL k ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) :=
      (centerCongr eL ⟨k,hk⟩).property
    rw [HermitianForm.EvenTwoRank.standard_center_eq_bot J hJ hnfix,mem_bot] at hh
    exact mem_bot.mpr (eL.injective (by simpa only [map_one] using hh))
  let C := centralizer (L : Set (H ⧸ sourceKernel N))
  have hCL : C ≤ S' := centralizer_le_sylow_of_centerless_supplement L S' hLs hLZ
  have hCN : C.comap q ≤ N := by
    intro x hx
    have hxS : q x ∈ (S : Subgroup H).map q := hCL hx
    obtain ⟨s,hs,he⟩ := hxS
    have hk : s⁻¹*x ∈ sourceKernel N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (s⁻¹*x) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hh := N.mul_mem (hSN hs) (N.normalCore_le hk)
    simpa only [mul_inv_cancel_left] using hh
  have hCJ : C.comap q ≤ sourceKernel N := normal_le_normalCore.mpr hCN
  have hC : C = ⊥ := by
    apply bot_unique
    intro c hc
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (sourceKernel N) c
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr (hCJ hc))
  let a : (H ⧸ sourceKernel N) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr eL).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 a ha).trans
    (HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hF hconj)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
