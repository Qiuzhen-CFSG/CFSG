module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# Faithfulness of the actual binary linear rank-one cover

The canonical panel projection on Rᵢ = ⟨Uᵢ,Uᵢ^{sᵢ}⟩ has a central odd
kernel contained in the derived subgroup. Identify its image with the
supplied PSL₂(F). Every odd Sylow subgroup of SL₂(F) is cyclic, by the
existing faithful eigenline argument. Its full Sylow preimage is abelian,
since it has cyclic quotient modulo a central kernel. Central Sylow transfer
then kills every prime-order element of the kernel.

The resulting isomorphism is the original panel projection, not an unrelated
model tag. It includes F₂ and F₄, uses no perfectness of Rᵢ, and keeps the full
rank-one group. The earlier radical-to-panel-kernel containment and actual
local PSL₂ comparison remain explicit source inputs.

Source: Fong--Seitz I (5C), printed pp.25--26, and the rank-one identifications
used in II §7, printed p.192. This supplies the local group, not the coupled
natural/tensor radical modules or the G₂ mixed-root equations.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {F E : Type*} [Field F] [Finite F] [CharP F 2] [Group E] [Finite E]

theorem odd_stem_linear_injective (f : E →* Matrix.SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (ho : Nat.Coprime 2 (Nat.card f.ker)) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpker
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact Nat.prime_two.not_dvd_one (ho.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpker)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' p hpker
  have horder : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  have hzp : IsPGroup p (zpowers (z : E)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,horder,pow_one])
  obtain ⟨S,hS⟩ := hzp.exists_le_sylow
  let T := S.mapSurjective hf
  let : IsCyclic T := Matrix.SL2.odd_pGroup_isCyclic_of_injective T.isPGroup' hp2
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype_injective
  let g : S →* T := (f.comp (S : Subgroup E).subtype).codRestrict T
    (fun x => mem_map_of_mem f x.property)
  have hgc : g.ker ≤ center S := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hc (congrArg Subtype.val hx)) y)
  let : IsMulCommutative S := g.isMulCommutative_of_isCyclic_of_ker_le_center hgc
  have hzS : (z : E) ∈ (S : Subgroup E) := hS (mem_zpowers _)
  have hzcomm := center_inf_commutator_inf_sylow_le_commutator S
    ⟨⟨hc z.property, hd z.property⟩, hzS⟩
  have hbot : ⁅(S : Subgroup E),(S : Subgroup E)⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  have hzone : (z : E) = 1 := mem_bot.mp (hbot ▸ hzcomm)
  rw [hzone,orderOf_one] at horder
  exact hp.ne_one horder.symm
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem rankOne_projection_injective (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    Function.Injective (RootLocalCover.projection Q split i) := by
  let e := μ.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let f := e.toMonoidHom.comp (RootLocalCover.projection Q split i)
  obtain ⟨hs,hc,ho,hd⟩ := RootLocalCover.central_odd_cover Q split i hV
  have hk : f.ker = (RootLocalCover.projection Q split i).ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  have hi : Function.Injective f := odd_stem_linear_injective f
    (e.surjective.comp hs) (hk.symm ▸ hc) (hk.symm ▸ hd) (hk.symm ▸ ho)
  exact fun x y h => hi (congrArg e h)

/-- The original panel action identifies the whole root-generated group with Lᵢ. -/
def rankOnePanelEquiv (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    rankOne Q split i ≃* localGroup Q split i :=
  MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨rankOne_projection_injective Q split i hV μ,
      (RootLocalCover.central_odd_cover Q split i hV).1⟩

@[simp] theorem rankOnePanelEquiv_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (r : rankOne Q split i) :
    rankOnePanelEquiv Q split i hV μ r = RootLocalCover.projection Q split i r := rfl

/-- The full source rank-one group is SL₂(F), also at orders two and four. -/
def rankOneLinearEquiv (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    rankOne Q split i ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  ((rankOnePanelEquiv Q split i hV μ).trans μ).trans
    (Theory.PSL2.sl2QuotientEquiv F).symm

/-- This comparison retains the prescribed local isomorphism and panel map. -/
theorem rankOneLinearEquiv_projection (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (r : rankOne Q split i) :
    Theory.PSL2.quotientMap F (rankOneLinearEquiv Q split i hV μ r) =
      μ (RootLocalCover.projection Q split i r) :=
  (Theory.PSL2.sl2QuotientEquiv F).apply_symm_apply _
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
