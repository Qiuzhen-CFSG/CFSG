module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicFull
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import Theory.Representation.IsotypicCopies

/-!
# Literal natural multiplicities on the full chosen orbit

The homogeneous quotient of 11.0.3 has the same simple type as the embedded
chosen seed. Its canonical isotypic component therefore supplies finite
copy coordinates. Vanishing of C_{V_M}(L) in the full SL₃ row lifts these
coordinates to V_M itself. Every copy retains the original quotient map
L → L/O₂(L) and the original natural marking, without a central splitting
or an automorphism change.

The multiplicity is positive and the binary dimension is exactly 3ns.
One copy is the original seed; two copies give the precise product marking
consumed by CubicFull. Consequently a strict bound dim(V_M) < 9n suffices
for the original order-three and elementary-three-subgroup conclusions.
That numerical bound is still an explicit premise. Its proof, and the
unconditional 11.0.4 assembly, remain with
qt-d-1222-natural-preliminary-source, before the final local-geometry
application owned by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, 11.0.3--4, printed p.760, and the multiplicity
premise of A.3.19, printed pp.54--55, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups MonoidAlgebra IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
section Coordinates
variable {H W E : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [AddCommGroup E] [Module (ZMod 2) E]

private theorem homogeneous_natural_coordinates
    (ρ : Representation (ZMod 2) H W) (μ : Representation (ZMod 2) H E)
    (hμ : IsIrreducible μ)
    (hhom : ∃ I : Subrepresentation ρ, IsIrreducible I.toRepresentation ∧
      homogeneousPart I ⊤ = ⊤)
    (j : μ.IntertwiningMap ρ) (hj : Function.Injective j) :
    ∃ s : ℕ, ∃ e : W ≃ₗ[ZMod 2] (Fin s → E),
      ∀ g v, e (ρ g v) = fun i => μ g (e v i) := by
  obtain ⟨I,hi,hh⟩ := hhom
  let := simple_asSubmodule I hi
  have htop : isotypicComponent (ZMod 2)[H] ρ.asModule I.asSubmodule = ⊤ := by
    apply top_unique
    intro v _
    have hle : homogeneousPart I ⊤ ≤
        (Subrepresentation.ofSubmodule'
          (isotypicComponent (ZMod 2)[H] ρ.asModule I.asSubmodule)).toSubmodule := by
      refine iSup_le fun J => iSup_le fun hJ => ?_
      exact show J.asSubmodule ≤ isotypicComponent (ZMod 2)[H] ρ.asModule I.asSubmodule from
        le_sSup ((sameModule_iff_linearEquiv _ _).mp hJ.2.symm)
    exact hle (by rw [hh]; exact Submodule.mem_top)
  have ht : IsIsotypicOfType (ZMod 2)[H] ρ.asModule I.asSubmodule :=
    IsIsotypicOfType.of_isotypicComponent_eq_top htop
  let f := IntertwiningMap.equivLinearMapAsModule μ ρ j
  let a := LinearEquiv.ofInjective f hj
  let := hμ
  let : IsSimpleModule (ZMod 2)[H] f.range := a.isSimpleModule_iff.mp inferInstance
  let b : μ.asModule ≃ₗ[(ZMod 2)[H]] I.asSubmodule := a.trans (ht f.range).some
  have htμ : isotypicComponent (ZMod 2)[H] ρ.asModule μ.asModule = ⊤ := by
    apply top_unique
    rw [← htop]
    refine sSup_le fun J hJ => ?_
    exact le_sSup ⟨hJ.some.trans b.symm⟩
  obtain ⟨s,e,he⟩ := SchurCopies.isotypic_finite_rep_coordinates ρ μ
  let P := Subrepresentation.ofSubmodule'
    (isotypicComponent (ZMod 2)[H] ρ.asModule μ.asModule)
  have hP : P.toSubmodule = ⊤ := by
    ext v
    change ρ.asModuleEquiv.symm v ∈ isotypicComponent (ZMod 2)[H] ρ.asModule μ.asModule ↔ True
    rw [htμ]
    simp
  let c : W ≃ₗ[ZMod 2] P.toSubmodule :=
    Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ hP.symm)
  refine ⟨s,c.trans e,?_⟩
  intro g v
  exact he g (c v)
end Coordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Actual repeated natural coordinates on the full normalizer orbit. Every
copy uses the original marking of L/O₂(L), including its full center. -/
@[expose] def FullModuleNaturalCopies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) (s : ℕ) : Prop :=
  letI := fullModule_elementary D S
  ∃ e : Additive (componentOrbit V (normalizer (L : Set G))) ≃ₗ[ZMod 2]
      (Fin s → Fin 3 → S.field.Carrier),
    ∀ (l : L) v, e (fullModuleConjugation D S (inclusion L.le_normalizer l) v) =
      fun i => (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (e v i)

/-- Homogeneity and fixed-space vanishing supply genuine finite natural
coordinates, without any assumed bound on their multiplicity. -/
theorem fullModule_sl3_natural_copies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    ∃ s : ℕ, 0 < s ∧ FullModuleNaturalCopies D S m s := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let C := (centralizer (L : Set G)).subgroupOf U
  have hC : C = ⊥ := by
    apply bot_unique
    intro u hu
    exact Subtype.ext (mem_bot.mp ((sl3_centralizers_eq_bot D S m).2 ▸
      (show (u : G) ∈ U ⊓ centralizer (L : Set G) from ⟨u.property,hu⟩)))
  let q : Additive U →ₗ[ZMod 2] Additive (U ⧸ C) :=
    (QuotientGroup.mk' C).toAdditive.toZModLinearMap 2
  have hq : Function.Bijective q := by
    change Function.Bijective (QuotientGroup.mk' C)
    refine ⟨?_,QuotientGroup.mk'_surjective C⟩
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk',hC]
  let b := LinearEquiv.ofBijective q hq
  obtain ⟨σ,hhom,hσ⟩ := fullModule_sl3_homogeneous D S m
  let N := L.subgroupOf M
  let a : N ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let μ : Representation (ZMod 2) N D.chosenCentralQuotient :=
    D.chosenCentralAction.comp a.toMonoidHom
  have hμ : IsIrreducible μ :=
    (irreducible_comp_surjective_iff a.toMonoidHom a.surjective _).mpr
      ((irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
        (QuotientGroup.mk'_surjective _) _).mpr D.centralQuotientAction_irreducible)
  let j : μ.IntertwiningMap (σ.comp N.subtype) := {
    toLinearMap := seedQuotientMap D U (le_componentOrbit V M)
    isIntertwining' n := LinearMap.ext (fun v =>
      seedQuotientMap_equivariant D U (le_componentOrbit V M)
        (L.le_normalizer.trans (le_normalizer_componentOrbit V M))
        (σ.comp (inclusion L.le_normalizer))
        (fun l u => hσ (inclusion L.le_normalizer l) u) (a n) v) }
  obtain ⟨s,e,he⟩ := homogeneous_natural_coordinates (σ.comp N.subtype) μ hμ hhom j
    (seedQuotientMap_injective D U (le_componentOrbit V M))
  let c : Additive U ≃ₗ[ZMod 2] (Fin s → Fin 3 → S.field.Carrier) :=
    b.trans (e.trans (LinearEquiv.piCongrRight fun _ => m.linearEquiv))
  have hs : 0 < s := by
    by_contra! hs
    have hz : s = 0 := by omega
    have : Subsingleton (Fin s → Fin 3 → S.field.Carrier) := by rw [hz]; infer_instance
    let : Subsingleton U := c.injective.subsingleton
    have hne : U ≠ ⊥ := fun h => D.ne_bot (bot_unique ((le_componentOrbit V M).trans h.le))
    exact hne (Subgroup.eq_bot_of_subsingleton U)
  refine ⟨s,hs,c,?_⟩
  intro l v
  have hb : b (fullModuleConjugation D S (inclusion L.le_normalizer l) v) =
      σ (inclusion L.le_normalizer l) (b v) := (hσ (inclusion L.le_normalizer l) v.toMul).symm
  change (fun i => m.linearEquiv (e (b (fullModuleConjugation D S
    (inclusion L.le_normalizer l) v)) i)) = _
  rw [hb]
  have hl := he (⟨inclusion L.le_normalizer l,l.property⟩ : N) (b v)
  change e (σ (inclusion L.le_normalizer l) (b v)) =
    (fun i => D.chosenCentralAction l (e (b v) i)) at hl
  rw [hl]
  funext i
  exact m.intertwines (QuotientGroup.mk' (pCore 2 L) l) (e (b v) i)

/-- The number of natural copies gives the exact binary dimension of the
literal full orbit. -/
theorem FullModuleNaturalCopies.finrank
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)} {s : ℕ}
    (h : FullModuleNaturalCopies D S m s) :
    letI := fullModule_elementary D S
    Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) =
      s * (3 * S.field.degree) := by
  let := fullModule_elementary D S
  obtain ⟨e,_⟩ := h
  have hF : Module.finrank (ZMod 2) S.field.Carrier = S.field.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S.field.Carrier)
    rw [Nat.card_zmod,S.field.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  rw [e.finrank_eq]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,hF]

/-- One natural copy makes the original seed equal to its full orbit. -/
theorem FullModuleNaturalCopies.eq_seed
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    (h : FullModuleNaturalCopies D S m 1) :
    componentOrbit V (normalizer (L : Set G)) = V := by
  let := fullModule_elementary D S
  obtain ⟨e,_⟩ := h
  have hq : Function.Bijective D.toCentralQuotient := by
    refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,D.toCentralQuotient_surjective⟩
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact mem_bot.mp ((sl3_centralizer_eq_bot D S m) ▸
      (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
        ⟨v.property,(quotient_eq_one_iff D v).mp hv⟩))
  have hV : Nat.card V = Nat.card (Fin 3 → S.field.Carrier) :=
    (Nat.card_congr (MulEquiv.ofBijective D.toCentralQuotient hq).toEquiv).trans
      (Nat.card_congr m.linearEquiv.toEquiv)
  have hU : Nat.card (componentOrbit V (normalizer (L : Set G))) =
      Nat.card (Fin 3 → S.field.Carrier) := by
    have hc := Nat.card_congr e.toEquiv
    change Nat.card (componentOrbit V (normalizer (L : Set G))) =
      Nat.card (Fin 1 → Fin 3 → S.field.Carrier) at hc
    simpa only [Nat.card_fun,Nat.card_fin,pow_one] using hc
  exact (Subgroup.eq_of_le_of_card_ge (le_componentOrbit V _) (by rw [hU,hV])).symm

/-- Two copies supply exactly the product marking required by the cubic
selection theorem. -/
theorem FullModuleNaturalCopies.double
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    (h : FullModuleNaturalCopies D S m 2) : FullModuleDoubleNatural D S m := by
  let := fullModule_elementary D S
  obtain ⟨e,he⟩ := h
  refine ⟨e.trans (LinearEquiv.finTwoArrow (ZMod 2) _),?_⟩
  intro l v
  exact congrArg (fun f : Fin 2 → Fin 3 → S.field.Carrier => (f 0,f 1)) (he l v)

/-- A strict three-constituent dimension bound discharges the full-module
multiplicity premise, with no extra choice of field or component marking. -/
theorem fullModule_eq_or_double_of_finrank_lt
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hd : letI := fullModule_elementary D S
      Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) <
        9 * S.field.degree) :
    componentOrbit V (normalizer (L : Set G)) = V ∨ FullModuleDoubleNatural D S m := by
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  rw [h.finrank] at hd
  have hb : s ≤ 2 := by nlinarith [S.field.degree_pos]
  have hcases : s = 1 ∨ s = 2 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl (h.eq_seed D S)
  · exact Or.inr (h.double D S)

/-- The original cubic conclusion from the precise remaining numerical
premise. The preliminary source owner must prove this strict degree bound
before claiming the unconditional 11.0.4 application. -/
theorem sl3_orderThree_mem_of_fullModule_finrank_lt
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hd : letI := fullModule_elementary D S
      Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) <
        9 * S.field.degree)
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L :=
  sl3_orderThree_mem_of_fullModule_multiplicity D S m heven
    (fullModule_eq_or_double_of_finrank_lt D S m hd) hxM hx

/-- The elementary-three subgroup form used by the original local
normalizer arguments, under the same numerical input. -/
theorem sl3_elementaryThreeSubgroup_le_of_fullModule_finrank_lt
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hd : letI := fullModule_elementary D S
      Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) <
        9 * S.field.degree)
    (P : Subgroup G) [IsElementaryAbelian 3 P]
    (hPM : P ≤ normalizer (L : Set G)) : P ≤ L := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ L.one_mem
  · exact sl3_orderThree_mem_of_fullModule_finrank_lt D S m heven hd (hPM hx)
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
