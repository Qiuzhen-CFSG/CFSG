module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Defs

/-!
# The actual odd quotient of Ξ_p(L)

The image of the residual under L → L/O₂(L) is exactly Ω₁(O_p(L/O₂(L))).
The restricted kernel is a two-group; the odd image has trivial two-core.
The core-lifting theorem identifies that kernel with the intrinsic two-core
of the residual, and the first isomorphism theorem gives the equivalences.
The last equivalence also transports the residual from L to the ambient G.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, construction
before Lemma 1.3.3, printed p.509. This construction retains the omega layer
when the p-core is homocyclic of higher exponent.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- The odd quotient of the residual inside L is its omega image. -/
noncomputable def xiPInQuotientEquivOmega {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (L₀ : Subgroup G) :
    (xiPIn p L₀) ⧸ pCore 2 (xiPIn p L₀) ≃* xiOmegaCore p L₀ := by
  let q : xiPIn p L₀ →* XiQuotient L₀ :=
    (QuotientGroup.mk' (pCore 2 L₀)).comp (xiPIn p L₀).subtype
  have hq : q.range = xiOmegaCore p L₀ := by
    rw [MonoidHom.range_comp, range_subtype]
    exact xiPIn_map_quotient hp L₀
  have hker : IsPGroup 2 q.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 L₀)).comp
      (xiPIn p L₀).subtype).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (xiPIn p L₀).subtype_injective
  have hω : IsPGroup p q.range := by
    rw [hq]
    exact ((pCore_isPGroup (p := p) (G := XiQuotient L₀)).to_subgroup _).map _
  have hbot : pCore 2 q.range = ⊥ :=
    disjoint_top.mp (pCore_isPGroup.disjoint_of_coprime
      (hω.to_subgroup ⊤) (Nat.coprime_two_left.mpr hp))
  have he : q.ker = pCore 2 (xiPIn p L₀) := by
    have hh := q.rangeRestrict.comap_pCore_of_ker_isPGroup (p := 2) q.rangeRestrict_surjective
      (hker.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict q)).symm)
    rw [hbot, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] at hh
    exact hh
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    ((QuotientGroup.quotientKerEquivRange q).trans (MulEquiv.subgroupCongr hq))

/-- The actual quotient Ξ_p(L)/O₂(Ξ_p(L)) is the first omega subgroup of the odd core. -/
noncomputable def xiPQuotientEquivOmega {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (L₀ : Subgroup G) : XiQuotient (XiP p L₀) ≃* omega (pCore p (XiQuotient L₀)) (p := p) 1 := by
  let e : xiPIn p L₀ ≃* XiP p L₀ :=
    (xiPIn p L₀).equivMapOfInjective L₀.subtype L₀.subtype_injective
  exact (QuotientGroup.congr (pCore 2 (XiP p L₀)) (pCore 2 (xiPIn p L₀)) e.symm
    (pCore_map_iso 2 e.symm)).trans ((xiPInQuotientEquivOmega hp L₀).trans
      ((omega (pCore p (XiQuotient L₀)) (p := p) 1).equivMapOfInjective
        (pCore p (XiQuotient L₀)).subtype (pCore p (XiQuotient L₀)).subtype_injective).symm)

end CFSG.Quasithin.Chapter1
