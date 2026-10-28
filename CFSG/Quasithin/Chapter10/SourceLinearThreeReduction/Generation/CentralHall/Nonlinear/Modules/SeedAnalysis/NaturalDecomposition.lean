module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalMultiplicity
public import Theory.Representation.SL2.NaturalMultiplicity

/-!
# Natural decomposition on the literal moved subgroup

Two natural copies in W = [V_M,L] give an action of the full component
stabilizer on their coefficient plane. The original orbit-index bound
and semilinear descent supply a stable natural subspace. Stabilizer
minimality forces that proper subspace to equal W, a contradiction.
The coordinates live on W itself; no inclusion of W in R₂(L₀T), and
hence no prior full/local module equality, is assumed.

Source: Aschbacher--Smith D.3.21(3) and the reselection in 3.2.6,
printed pp.204--207,581. Separation and the earlier constituent degree
bound remain with qt-d-10-nona5-central-hall-orders.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance naturalDecompositionElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The complete two-natural-copy alternative is impossible on the actual W.
This does not assume W lies in the original local reduced module. -/
theorem no_two_natural_copies_on_moved
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (E : (Fin 2 → (Fin 2 → F)) ≃ₗ[ZMod 2] Additive (⁅D.fullModule,L⁆ : Subgroup G))
    (hL : ∀ (l : L) x,
      ((E (fun i => naturalComponent e l (x i))).toMul : G) =
        (l : G) * ((E x).toMul : G) * (l : G)⁻¹) : False := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  have hNW : N ≤ normalizer (W : Set G) := by
    intro n hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hn.1),
      mem_normalizer_iff_map_conj_eq.mp hn.2]
  let r : Representation (ZMod 2) N (Additive W) :=
    Representation.elementaryRepresentation (W.normalizerMonoidHom.comp (inclusion hNW))
  let ρ := (E.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp r
  have hr (n : N) x : ((E (ρ n x)).toMul : G) =
      (n : G) * ((E x).toMul : G) * (n : G)⁻¹ := by
    change ((E (E.symm (r n (E x)))).toMul : G) = _
    rw [E.apply_symm_apply]
    rfl
  let α : N →* MulAut (SL(2,F)) :=
    (MulAut.congr e).toMonoidHom.comp
      ((normalizerPCoreQuotientAction L).comp (inclusion inf_le_right))
  have hJ : Function.Injective (fun x => ((E x).toMul : G)) := by
    intro x y hh
    exact E.injective (Subtype.ext hh)
  have hcomponent (l : L) x :
      ((E (fun i => (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (x i))).toMul : G) =
        (l : G) * ((E x).toMul : G) * (l : G)⁻¹ := by
    have hx : (fun i => (e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (x i)) =
        (fun i => naturalComponent e l (x i)) := by
      funext i
      exact (Representation.SL2AutomorphismNatural.action_conj _ _).symm
    rw [hx,hL]
  have hcov : ∀ n g x, ρ n (fun i => g.val.mulVec (x i)) =
      fun i => (α n g).val.mulVec (ρ n x i) := by
    intro n g x
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    let l' : L := L.normalizerMonoidHom (inclusion (show N ≤ normalizer (L : Set G) from inf_le_right) n) l
    have ha : α n (e (QuotientGroup.mk' (pCore 2 L) l)) =
        e (QuotientGroup.mk' (pCore 2 L) l') := by
      change e (normalizerPCoreQuotientAction L (inclusion inf_le_right n)
        (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
      rw [e.symm_apply_apply]
      change e (quotientAut (pCore 2 L) _ _) = _
      rw [quotientAut_apply_mk]
    dsimp only [Function.comp_apply]
    rw [ha]
    apply hJ
    dsimp only
    rw [hr,hcomponent,hcomponent,hr]
    change (n : G) * ((l : G) * _ * (l : G)⁻¹) * (n : G)⁻¹ =
      ((n : G) * (l : G) * (n : G)⁻¹) * ((n : G) * _ * (n : G)⁻¹) *
        ((n : G) * (l : G) * (n : G)⁻¹)⁻¹
    group
  obtain ⟨μ,hμ,hdiag,τ,hsemi⟩ :=
    Representation.SL2AutomorphismNatural.exists_two_copy_coefficients ρ α hcov
  let q := μ.asGroupHom.rangeRestrict
  let : Finite μ.asGroupHom.range := Finite.of_surjective q μ.asGroupHom.rangeRestrict_surjective
  let ν : Representation (ZMod 2) μ.asGroupHom.range (Fin 2 → F) :=
    (Units.coeHom _).comp μ.asGroupHom.range.subtype
  have hν : Function.Injective ν := by
    intro a b hh
    exact Subtype.ext (Units.ext hh)
  have hN : localOrbit T L ≤ N := le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D c.nonnormal)
  let K := q.ker.map N.subtype
  have hLK : L ≤ K := by
    intro l hl
    let n : N := ⟨l,hN (le_componentOrbit L T hl)⟩
    have hn : ∀ x, ρ n x = fun i =>
        (e (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)).val.mulVec (x i) := by
      intro x
      apply hJ
      dsimp only
      rw [hr,hcomponent]
    refine ⟨n,MonoidHom.mem_ker.mpr ?_,rfl⟩
    exact Subtype.ext (hdiag n _ hn)
  have hp : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  have hLtK : L.map (MulAut.conj t).toMonoidHom ≤ K := by
    intro l hl
    let n : N := ⟨l,hN (hp ▸ mem_sup_right hl)⟩
    have hn (x) : ρ n x = x := by
      apply hJ
      dsimp only
      rw [hr]
      have hc := mem_centralizer_iff.mp
        (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep (E x).toMul.property) l hl
      change l * _ * l⁻¹ = _
      rw [hc,mul_assoc,mul_inv_cancel,mul_one]
    refine ⟨n,MonoidHom.mem_ker.mpr ?_,rfl⟩
    exact Subtype.ext (hdiag n 1 (by intro x; simpa using hn x))
  have hOK : localOrbit T L ≤ K := by rw [hp]; exact sup_le hLK hLtK
  have hkill : (localOrbit T L).subgroupOf N ≤ q.ker := by
    intro n hn
    obtain ⟨m,hm,he⟩ := hOK hn
    have he' : m = n := Subtype.ext he
    exact he' ▸ hm
  obtain ⟨b,hb,hfix⟩ := multiplicity_fixed_vector D c.nonnormal e q
    μ.asGroupHom.rangeRestrict_surjective hkill ν hν τ hsemi
  let f : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → (Fin 2 → F)) := {
    toFun v i := b i • v
    map_add' v w := by funext i; exact smul_add _ _ _
    map_smul' a v := by funext i; exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    obtain ⟨i,hi⟩ : ∃ i, b i ≠ 0 := by
      by_contra! hh
      exact hb (funext hh)
    intro v w hh
    exact (smul_right_injective (Fin 2 → F) hi) (congrFun hh i)
  let k := E.toLinearMap.comp f
  let j : Multiplicative (Fin 2 → F) →* G :=
    W.subtype.comp k.toAddMonoidHom.toMultiplicativeLeft
  have hj : Function.Injective j := W.subtype_injective.comp (E.injective.comp hf)
  have hstable : N ≤ normalizer (j.range : Set G) := by
    apply le_normalizer_iff.mpr
    intro n hn x hx
    obtain ⟨v,rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd (SL2AutomorphismNatural.action (α ⟨n,hn⟩) v.toAdd),?_⟩
    have hh := hr ⟨n,hn⟩ (f v.toAdd)
    change ((E (ρ ⟨n,hn⟩ (fun i => b i • v.toAdd))).toMul : G) = _ at hh
    rw [hμ] at hh
    have hfixed : μ ⟨n,hn⟩ b = b := hfix (q ⟨n,hn⟩)
    rw [hfixed] at hh
    exact hh
  have hle : j.range ≤ W := by rintro _ ⟨v,rfl⟩; exact (k v.toAdd).toMul.property
  have hne : j.range ≠ ⊥ := by
    intro hz
    have hzero : j = 1 := MonoidHom.range_eq_bot_iff.mp hz
    have he : (1 : Fin 2 → F) = 0 := by
      have heq : j (Multiplicative.ofAdd (1 : Fin 2 → F)) =
          j (Multiplicative.ofAdd (0 : Fin 2 → F)) := by rw [hzero]; rfl
      exact congrArg Multiplicative.toAdd (hj heq)
    exact one_ne_zero he
  have he := (moved_minimal_under_component_stabilizer_of_seed_separated
    D c ht htn hsep j.range hle hstable).resolve_right hne
  have hcard : Nat.card (Fin 2 → (Fin 2 → F)) = Nat.card (Fin 2 → F) := by
    calc
      _ = Nat.card W := (Nat.card_congr E.toEquiv).trans (Nat.card_congr Additive.toMul)
      _ = Nat.card j.range := congrArg (fun X : Subgroup G => Nat.card X) he.symm
      _ = Nat.card (Fin 2 → F) :=
        (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans
          (Nat.card_congr Multiplicative.toAdd)
  rw [Nat.card_fun,Nat.card_fin] at hcard
  have hpos : 1 < Nat.card (Fin 2 → F) := Finite.one_lt_card
  nlinarith

/-- D.3.21's two-natural-copy alternative on the literal central quotient is
excluded using the proved vanishing of that exact centralizer kernel. -/
theorem no_two_natural_copies_on_moved_quotient
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (C : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((naturalComponent e).prod (naturalComponent e))) : False := by
  have hi : Function.Injective C.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [C.kernel_eq,movedFixed_eq_bot_of_seed_separated D c ht htn hsep,bot_subgroupOf]
  let a := LinearEquiv.ofBijective (C.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hi,C.onto⟩
  let E := (LinearEquiv.finTwoArrow (ZMod 2) (Fin 2 → F)).trans a.symm
  apply no_two_natural_copies_on_moved D c ht htn hsep e E
  intro l x
  have h := C.equivariant l (E x).toMul
  have hx : (C.coordinates (E x).toMul).toAdd = (x 0,x 1) := a.apply_symm_apply _
  rw [hx] at h
  have hh := congrArg a.symm h
  have hinv (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
      a.symm (C.coordinates w).toAdd = Additive.ofMul w := a.symm_apply_apply _
  rw [hinv] at hh
  exact (congrArg (fun w : Additive (⁅D.fullModule,L⁆ : Subgroup G) => (w.toMul : G)) hh).symm

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
