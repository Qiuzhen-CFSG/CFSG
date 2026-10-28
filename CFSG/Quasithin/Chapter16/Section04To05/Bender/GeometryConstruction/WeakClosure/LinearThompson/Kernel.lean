module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.Action
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Omega
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Linear.Model
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner

/-!
# The pointwise action kernel in the center-free linear branch

The actual quotient isomorphism L/Z(L) ≃ PSL₂(F), together with Z(L) = 1,
identifies T ∩ L with an elementary abelian Sylow subgroup of the model.
Hence U_L is all of T ∩ L. The model pointwise-fixer theorem, transported
through that quotient, makes every pointwise fixer inner on L. An involution
in this kernel belongs to U_C U_L by the center-free lifting calculation.

This includes every binary field degree. It asserts innerness only for
pointwise fixers, not for all two-elements of Aut(L).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, using the pointwise-fixer fact in 16.1.6, p.1172.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L R : Subgroup G} {n : ℕ}

/-- The rank-one model makes the entire component Sylow elementary. -/
theorem componentSylow_elementary_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n)) :
    IsElementaryAbelian 2 (componentSylow T L) := by
  classical
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eL : L ≃* PSL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀
  obtain ⟨S, hS⟩ := h.toCentralComponentSetup.exists_component_sylow
  let Q := S.mapSurjective (f := eL.toMonoidHom) eL.surjective
  let P := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  have hP : IsElementaryAbelian 2 P := by
    rw [show (P : Subgroup PSL(2,F)) =
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F from
      Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F]
    exact TorusConstruction.Linear.kernel_elementary F
  let := hP
  let : IsElementaryAbelian 2 Q :=
    IsElementaryAbelian.of_surjective (P.equiv Q).toMonoidHom (P.equiv Q).surjective
  let eS : S ≃* Q := (S : Subgroup L).equivMapOfInjective eL.toMonoidHom eL.injective
  let : IsElementaryAbelian 2 S :=
    IsElementaryAbelian.of_surjective eS.symm.toMonoidHom eS.symm.surjective
  have hmap : (S : Subgroup L).map L.subtype = componentSylow T L := by
    rw [hS, subgroupOf_map_subtype]
    rfl
  rw [← hmap]
  exact IsElementaryAbelian.map L.subtype

/-- A pointwise fixer of U_L induces an inner automorphism of the actual L. -/
theorem omega_fixer_inner_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (t : T) (ht : omegaAction h t = 1) :
    ∃ b : L, L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩ = MulAut.conj b := by
  let := componentSylow_elementary_psl2 h hZ hmodel
  have hfix : ∀ x ∈ componentSylow T L, (t : G) * x * (t : G)⁻¹ = x := by
    intro x hx
    have hxU : x ∈ omegaOneAmbient (componentSylow T L) := by
      rwa [omegaOneAmbient_eq_self]
    let u : componentOmegaInSylow T L := ⟨⟨x, hx.1⟩, hxU⟩
    have he := congrArg (fun a : MulAut (componentOmegaInSylow T L) =>
      ((a u : T) : G)) ht
    exact he
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := h.component.quasisimple
  obtain ⟨S, hS⟩ := h.toCentralComponentSetup.exists_component_sylow
  obtain ⟨b, _, hb⟩ := MulAut.fixing_sylow_inner_of_centralQuotient e₀
    (fun Q a ha => Theory.PSL2.aut_fixing_sylow_inner Q a ha) S
    (L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩) (by
      intro x hx
      apply Subtype.ext
      apply hfix
      refine ⟨?_, x.property⟩
      change x ∈ (S : Subgroup L) at hx
      rw [hS] at hx
      exact hx)
  exact ⟨b, hb⟩

/-- An inner action is precisely enough for placement in C_G(L)L. -/
theorem mem_centralizer_sup_of_inner (h : StandardSetup T z L) (t : T)
    (hinner : ∃ b : L,
      L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩ = MulAut.conj b) :
    (t : G) ∈ centralizer (L : Set G) ⊔ L := by
  obtain ⟨b, hb⟩ := hinner
  have hc : (b : G)⁻¹ * (t : G) ∈ centralizer (L : Set G) := by
    intro x hx
    have he := congrArg L.subtype (DFunLike.congr_fun hb ⟨x, hx⟩)
    change (t : G) * x * (t : G)⁻¹ = (b : G) * x * (b : G)⁻¹ at he
    have he' := mul_inv_eq_iff_eq_mul.mp he
    calc
      x * ((b : G)⁻¹ * (t : G)) = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * (t : G)) := by group
      _ = (b : G)⁻¹ * ((t : G) * x) := by rw [← he']
      _ = ((b : G)⁻¹ * (t : G)) * x := (mul_assoc _ _ _).symm
  simpa only [mul_inv_cancel_left] using
    (centralizer (L : Set G) ⊔ L).mul_mem
      ((le_sup_right : L ≤ centralizer (L : Set G) ⊔ L) b.property)
      ((le_sup_left : centralizer (L : Set G) ≤ centralizer (L : Set G) ⊔ L) hc)

/-- The involutions in the pointwise kernel lie in the Bender space. -/
theorem kernel_involution_mem_space_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (t : T) (ht : omegaAction h t = 1) (ht2 : t ^ 2 = 1) :
    (t : G) ∈ benderSpace T L := by
  exact TorusConstruction.involution_mem_space h
    (TorusConstruction.involutionLifting_of_center_eq_bot hZ) t.property
    (congrArg (fun t : T => (t : G)) ht2)
    (mem_centralizer_sup_of_inner h t (omega_fixer_inner_psl2 h hZ hmodel t ht))

/-- The whole Bender space fixes U_L pointwise. The commuting factor needs
no elementary hypothesis for this assertion. -/
theorem omegaAction_eq_one_of_mem_space (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))]
    (t : T) (ht : (t : G) ∈ benderSpace T L) : omegaAction h t = 1 := by
  have hC : benderSpace T L ≤
      centralizer (omegaOneAmbient (componentSylow T L) : Set G) := by
    apply sup_le
    · exact ((omegaOneAmbient_le _).trans inf_le_right).trans
        (centralizer_le ((omegaOneAmbient_le _).trans inf_le_right))
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change (t : G) * ((u : T) : G) * (t : G)⁻¹ = ((u : T) : G)
  have hu : ((u : T) : G) * (t : G) = (t : G) * ((u : T) : G) := hC ht _ u.property
  rw [← hu, mul_inv_cancel_right]

/-- For involutions, the pointwise U_L kernel equals the inner-action kernel.
This is the exact comparison needed to bound elementary images by the cyclic
field outer quotient. -/
theorem omegaAction_eq_one_iff_inner_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n)) (t : T) (ht2 : t ^ 2 = 1) :
    omegaAction h t = 1 ↔ ∃ b : L,
      L.normalizerMonoidHom ⟨t, h.sylow_normalizes t.property⟩ = MulAut.conj b := by
  constructor
  · exact omega_fixer_inner_psl2 h hZ hmodel t
  · intro ht
    let := componentSylow_elementary_psl2 h hZ hmodel
    let : IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L)) := by
      rw [omegaOneAmbient_eq_self]
      infer_instance
    apply omegaAction_eq_one_of_mem_space h
    exact TorusConstruction.involution_mem_space h
      (TorusConstruction.involutionLifting_of_center_eq_bot hZ) t.property
      (congrArg (fun t : T => (t : G)) ht2) (mem_centralizer_sup_of_inner h t ht)

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
