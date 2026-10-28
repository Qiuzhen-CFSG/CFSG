module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.CentralKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.TwoNoncentralLayers
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# The central-cover input to field-four component uniqueness

A surjective map to the natural plane sends the moved space onto that plane.
Consequently the original central kernel surjects onto the quotient by the
moved space. The central-cover Irr⁺ theorem and 11.0.3's bound on C_V(L) give
an Irr⁺ moved space and quotient of binary dimension at most n. At q=4 the
small-quotient component argument therefore proves the literal 11.1.3.

All actions are original conjugation and the kernel is exactly C_V(L) inside
V₂. The map and its intertwining identity are preceding flag/model inputs,
owned by qt-d-1222-natural-flag-cartan; the containing-component conclusion
is owned by this relative-components task. The parent local-geometry assembly
retains discharge of the preceding inputs. No claim is made that this small
quotient argument alone covers n>2.

Source: Aschbacher--Smith 11.0.3(3) and 11.1.3, printed pp.760,765,
with the central-cover correction to the whole-plane Irr⁺ assertion.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem moved_of_central_cover
    {H U W : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H U) (A : Subgroup H) [Group.IsPerfect A]
    (σ : Representation (ZMod 2) A W) (p : U →ₗ[ZMod 2] W)
    (hp : Function.Surjective p)
    (hact : ∀ a : A, ∀ v, p (ρ a v) = σ a (p v))
    (hk : p.ker ≤ fixedSpace ρ A) (hi : IsIrrPlus σ ⊤ ⊤) :
    IsIrrPlus ρ A (subspaceCommutator ρ ⊤ A) ∧
      Module.finrank (ZMod 2) (U ⧸ subspaceCommutator ρ ⊤ A) ≤
        Module.finrank (ZMod 2) p.ker := by
  let τ := ρ.comp A.subtype
  have hm : subspaceCommutator τ ⊤ (⊤ : Subgroup A) = subspaceCommutator ρ ⊤ A := by
    rw [subspaceCommutator_comp_map,← MonoidHom.range_eq_map,range_subtype]
  have hk' : p.ker ≤ fixedSpace τ ⊤ := fun _ hv a => hk hv a.val
  have hi' := IsIrrPlus.of_central_surjection τ σ ⊤ p hp
    (fun a v => hact a.val v) hk' hi
  have hA : A.subgroupOf A = ⊤ := subgroupOf_self _
  have hirr : IsIrrPlus ρ A (subspaceCommutator ρ ⊤ A) := by
    apply (IsIrrPlus.subgroupOf_iff ρ A A le_rfl _).mp
    rw [hA,← hm]
    exact hi'
  refine ⟨hirr,?_⟩
  let I := subspaceCommutator ρ ⊤ A
  have hmap : I.map p = ⊤ := by
    change (subspaceCommutator ρ ⊤ A).map p = ⊤
    rw [← hm,map_moved_of_surjective_intertwining τ σ ⊤ p hp
      (fun a v => hact a.val v),hi.choose_spec.1]
  let q : p.ker →ₗ[ZMod 2] (U ⧸ I) := I.mkQ.comp p.ker.subtype
  apply LinearMap.finrank_le_finrank_of_surjective (f := q)
  intro x
  obtain ⟨v,rfl⟩ := I.mkQ_surjective x
  obtain ⟨i,hi,hiv⟩ := (show p v ∈ I.map p from hmap.symm ▸ Submodule.mem_top)
  have hker : v-i ∈ p.ker := by
    change p (v-i) = 0
    rw [map_sub,hiv,sub_self]
  refine ⟨⟨v-i,hker⟩,?_⟩
  change I.mkQ (v-i) = I.mkQ v
  rw [map_sub,show I.mkQ i = 0 from (Submodule.Quotient.mk_eq_zero I).mpr hi,sub_zero]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The already proved 11.0.3 central-rank bound for any of the three markings. -/
theorem flag_centralizer_rank_le : rank (V ⊓ centralizer (L : Set G)) ≤ S.field.degree := by
  cases S.natural with
  | sl3 m =>
    rw [Preliminary.sl3_centralizer_eq_bot D S m.some]
    simp [rank]
  | sp4 m => exact Preliminary.sp4_centralizer_rank_le D S m.some
  | g2 m => exact Preliminary.g2_centralizer_rank_le D S m.some

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Identifying the kernel with the actual C_V(L) identifies its binary dimension.
The ambient inclusion of that central part is retained in both directions. -/
theorem second_cover_kernel_finrank (p : Additive (f.Vi 1) →ₗ[ZMod 2] W)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    Module.finrank (ZMod 2) p.ker = rank (V ⊓ centralizer (L : Set G)) := by
  let e : p.ker ≃ (V ⊓ centralizer (L : Set G) : Subgroup G) :=
    { toFun v := ⟨v.val.toMul,
        D.centralQuotientPreimage_le _ v.val.toMul.property,(hk v.val).mp v.property⟩
      invFun v := ⟨Additive.ofMul ⟨v.val,f.centralizer_le_Vi 1 v.property⟩,
        (hk _).mpr v.property.2⟩
      left_inv v := rfl
      right_inv v := rfl }
  rw [rank,← Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod,Nat.log_pow (by decide : 1 < 2)]

/-- A literal natural central cover yields Irr⁺ on [V₂,L₂] and bounds the
remaining quotient by n, without assuming an action on that quotient. -/
theorem secondMoved_of_cover
    (σ : Representation (ZMod 2) ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) W)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] W) (hp : Function.Surjective p)
    (hact : ∀ a : (f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G)), ∀ v,
      p (flagAction f 1 a v) = σ a (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hi : IsIrrPlus σ ⊤ ⊤) :
    IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) (secondMoved f) ∧
      Module.finrank (ZMod 2) (Additive (f.Vi 1) ⧸ secondMoved f) ≤ S.field.degree := by
  let A := (f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))
  have hLH : f.Li 1 ≤ normalizer (f.Vi 1 : Set G) := (localResidual_le _).trans inf_le_right
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLH).symm.surjective
  have hker : p.ker ≤ fixedSpace (flagAction f 1) A := by
    intro v hv a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a.val.val : G) * (v.toMul : G) * (a.val.val : G)⁻¹ = (v.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hk v).mp hv _
      ((localResidual_le _ a.property).1))
  obtain ⟨hirr,hd⟩ := moved_of_central_cover (flagAction f 1) A σ p hp hact hker hi
  refine ⟨hirr,hd.trans ?_⟩
  rw [second_cover_kernel_finrank S f p hk]
  exact flag_centralizer_rank_le S

/-- Source 11.1.3 in field four from the actual central cover and second
component membership. The central-rank and moved-space premises are discharged. -/
theorem uniqueNoncentral_second_fieldFour_of_cover (hfour : S.field.degree = 2)
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (σ : Representation (ZMod 2) ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) W)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] W) (hp : Function.Surjective p)
    (hact : ∀ a : (f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G)), ∀ v,
      p (flagAction f 1 a v) = σ a (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hi : IsIrrPlus σ ⊤ ⊤)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  obtain ⟨hirr,hd⟩ := secondMoved_of_cover S f σ p hp hact hk hi
  exact uniqueNoncentral_second_of_small_moved_quotient f S hL hirr (hd.trans_eq hfour) hcore

private theorem natural_top_isIrrPlus
    {A E : Type*} [Group A] [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    (π : A →* SL(2,E)) (hπ : Function.Surjective π) :
    IsIrrPlus ((restrictScalars (k := ZMod 2) (specialLinearNatural (k := E) 2)).comp π)
      ⊤ ⊤ := by
  let σ := (restrictScalars (k := ZMod 2) (specialLinearNatural (k := E) 2)).comp π
  have htrans (v w : Fin 2 → E) (hv : v ≠ 0) (hw : w ≠ 0) :
      ∃ a : A, σ a v = w := by
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq E v w hv hw
    obtain ⟨a,rfl⟩ := hπ g
    exact ⟨a,hg⟩
  have hdich (J : Submodule (ZMod 2) (Fin 2 → E))
      (hs : (⊤ : Subgroup A) ≤ subspaceStabilizer σ J) : J = ⊥ ∨ J = ⊤ := by
    by_cases hz : J = ⊥
    · exact Or.inl hz
    right
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ J.zero_mem
    obtain ⟨a,rfl⟩ := htrans v w hv0 hw
    exact (hs (mem_top a) v).mpr hv
  have hn : ¬ (⊤ : Submodule (ZMod 2) (Fin 2 → E)) ≤ fixedSpace σ ⊤ := by
    intro hf
    obtain ⟨a,ha⟩ := htrans ![1,0] ![0,1] (by simp) (by simp)
    have hh := hf (show (![1,0] : Fin 2 → E) ∈ (⊤ : Submodule (ZMod 2) _) from trivial)
      (⟨a,mem_top a⟩ : (⊤ : Subgroup A))
    have h0 := congrFun (ha.symm.trans hh) 0
    simp at h0
  have hm : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    rcases hdich _ (subspaceCommutator_invariant σ ⊤ ⊤) with hb | ht
    · exact (hn ((subspaceCommutator_eq_bot_iff σ ⊤ ⊤).mp hb)).elim
    · exact ht
  apply isIrrPlus_of_minimal σ (le_subspaceStabilizer σ ⊤ (by intros; trivial)) hm hn
  intro J hJ _
  rcases hdich J hJ with hb | ht
  · exact Or.inr (hb ▸ bot_le)
  · exact Or.inl ht

/-- Field-four source consumer stated with the original residual-to-SL₂ map
and its actual plane projection. Naturality supplies the quotient Irr⁺ premise. -/
theorem uniqueNoncentral_second_fieldFour_of_natural_cover (hfour : S.field.degree = 2)
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  let A := (f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))
  let e : A ≃* f.Li 1 := subgroupOfEquivOfLe
    ((localResidual_le _).trans inf_le_right)
  let πA := π.comp e.toMonoidHom
  let σ := (restrictScalars (k := ZMod 2)
    (specialLinearNatural (k := S.field.Carrier) 2)).comp πA
  exact uniqueNoncentral_second_fieldFour_of_cover S f hfour hL σ p hp
    (fun a v => hact (e a) v) hk
    (natural_top_isIrrPlus πA (hπ.comp e.surjective)) hcore

/-- The local sieve's literal second-normalizer output feeds the repaired
field-four consumer. The triangle branch at the first normalizer is independent. -/
theorem uniqueNoncentral_second_fieldFour_of_reduction (hfour : S.field.degree = 2)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (href : RefinementReduction L (f.Li 0) (f.Li 1) K X 1 S.field.degree)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G))
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second_fieldFour_of_natural_cover S f hfour _ π hπ p hp hact hk hcore
  rw [href.second_eq]
  exact hK.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
