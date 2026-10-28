module
public import Theory.Representation.SL2.NaturalSelfExtensionSection
public import Theory.Representation.SubspaceQuotient

/-!
# Splitting binary natural self-extensions of SL₂

Let an SL₂(F)-module over F₂ have a specified invariant submodule and quotient,
both identified with the natural module, where F is finite of characteristic
two. There is an invariant complement to that specified submodule, and the
complement is naturally identified with the same natural module.

Choose a quotient section commuting with the Weyl involution and the diagonal
torus. Its failure of equivariance is a normalized derivation, hence principal.
Subtracting its principal term gives an equivariant section. Its range is the
required complement, with coordinates supplied by its inverse.

Source application: DGS85, (9.10)(6), printed pp.149–150, including the chosen
subgroup W with W∩V=Z and Q=VW. The subgroup pullback is handled by
`BinaryConjugationSection.exists_complementary_section`.
-/

public noncomputable section

open scoped MatrixGroups
namespace Representation.SL2NaturalSelfExtension
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

/-- A natural self-extension splits relative to its specified natural submodule. -/
theorem exists_natural_complement
    (ρ : Representation (ZMod 2) SL(2,F) Y) (X : Subrepresentation ρ)
    (eX : X.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
    (eQ : (Y ⧸ X.toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F))
    (heX : ∀ g x, eX (X.toRepresentation g x) = natRep g (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) = natRep g (eQ x)) :
    ∃ K : Subrepresentation ρ, IsCompl X.toSubmodule K.toSubmodule ∧
      ∃ eK : K.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F),
        ∀ g k, eK (K.toRepresentation g k) = natRep g (eK k) := by
  classical
  let i : (Fin 2 → F) →ₗ[ZMod 2] Y := X.toSubmodule.subtype.comp eX.symm.toLinearMap
  let q : Y →ₗ[ZMod 2] (Fin 2 → F) := eQ.toLinearMap.comp X.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp eX.symm.injective
  have hq : Function.Surjective q := eQ.surjective.comp X.toSubmodule.mkQ_surjective
  have hie (g : SL(2,F)) (v : Fin 2 → F) : ρ g (i v) = i (natRep g v) := by
    have hh := heX g (eX.symm v)
    rw [eX.apply_symm_apply] at hh
    have hh' := congrArg eX.symm hh
    rw [eX.symm_apply_apply] at hh'
    exact congrArg Subtype.val hh'
  have hqe (g : SL(2,F)) (y : Y) : q (ρ g y) = natRep g (q y) :=
    heQ g (X.toSubmodule.mkQ y)
  have hqi (v : Fin 2 → F) : q (i v) = 0 := by
    change eQ (X.toSubmodule.mkQ (eX.symm v).val) = 0
    rw [show X.toSubmodule.mkQ (eX.symm v).val = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (eX.symm v).property, map_zero]
  have hqker (y : Y) : q y = 0 ↔ y ∈ X.toSubmodule := by
    change eQ (X.toSubmodule.mkQ y) = 0 ↔ _
    rw [eQ.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨j,hqj,hwj,htj⟩ := exists_normalized_section ρ q hq hqe
  let δ (g : SL(2,F)) : (Fin 2 → F) →ₗ[ZMod 2] Y :=
    (ρ g).comp j - j.comp (natRep g)
  have hδ (g : SL(2,F)) (v : Fin 2 → F) : δ g v ∈ X.toSubmodule := by
    apply (hqker _).mp
    change q (ρ g (j v) - j (natRep g v)) = 0
    rw [map_sub,hqe,hqj,hqj,sub_self]
  let d (g : SL(2,F)) : Module.End (ZMod 2) (Fin 2 → F) :=
    eX.toLinearMap.comp ((δ g).codRestrict X.toSubmodule (hδ g))
  have hid (g : SL(2,F)) (v : Fin 2 → F) :
      i (d g v) = ρ g (j v) - j (natRep g v) := by
    change (eX.symm (eX ⟨δ g v,hδ g v⟩)).val = _
    rw [eX.symm_apply_apply]
    rfl
  have hd (g h : SL(2,F)) (v : Fin 2 → F) :
      d (g*h) v = natRep g (d h v) + d g (natRep h v) := by
    apply hi
    rw [hid,map_add,←hie,hid,hid,map_sub,map_mul,map_mul,
      Module.End.mul_apply,Module.End.mul_apply]
    abel
  have hw : d swap = 0 := by
    apply LinearMap.ext
    intro v
    apply hi
    rw [hid,LinearMap.zero_apply,map_zero,hwj,sub_self]
  have ht (x : F) (hx : x ≠ 0) : d (diagonal x hx) = 0 := by
    apply LinearMap.ext
    intro v
    apply hi
    rw [hid,LinearMap.zero_apply,map_zero]
    apply sub_eq_zero.mpr
    simpa only [torus_apply,Units.val_mk0] using htj (Units.mk0 x hx) v
  obtain ⟨T,hT⟩ := normalized_principal d hd hw ht
  let j' : (Fin 2 → F) →ₗ[ZMod 2] Y := j - i.comp T
  have hj' (v : Fin 2 → F) : j' v = j v-i (T v) := rfl
  have hqj' (v : Fin 2 → F) : q (j' v) = v := by
    rw [hj',map_sub,hqj,hqi,sub_zero]
  have hje (g : SL(2,F)) (v : Fin 2 → F) : ρ g (j' v) = j' (natRep g v) := by
    have hh := hid g v
    rw [hT,map_sub,←hie] at hh
    rw [hj',hj',map_sub]
    calc
      ρ g (j v) - ρ g (i (T v)) =
          (ρ g (j v) - j (natRep g v)) - (ρ g (i (T v)) - i (T (natRep g v))) +
            (j (natRep g v) - i (T (natRep g v))) := by abel
      _ = _ := by rw [hh,sub_self,zero_add]
  have hji : Function.Injective j' := fun v w h => by
    have hh := congrArg q h
    rwa [hqj',hqj'] at hh
  let K : Subrepresentation ρ := {
    toSubmodule := LinearMap.range j'
    apply_mem_toSubmodule g := by
      rintro y ⟨v,rfl⟩
      exact ⟨natRep g v,(hje g v).symm⟩ }
  have hdisj : Disjoint X.toSubmodule K.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    rintro y hy ⟨v,rfl⟩
    have hv : v = 0 := (hqj' v).symm.trans ((hqker _).mpr hy)
    rw [hv,map_zero]
  have hsup : X.toSubmodule ⊔ K.toSubmodule = ⊤ := by
    apply top_unique
    intro y _
    apply Submodule.mem_sup.mpr
    refine ⟨y-j' (q y),?_,j' (q y),⟨q y,rfl⟩,sub_add_cancel _ _⟩
    apply (hqker _).mp
    rw [map_sub,hqj',sub_self]
  let E : (Fin 2 → F) ≃ₗ[ZMod 2] K.toSubmodule := LinearEquiv.ofInjective j' hji
  refine ⟨K,⟨hdisj,codisjoint_iff.mpr hsup⟩,E.symm,?_⟩
  intro g k
  apply E.injective
  apply Subtype.ext
  change j' (E.symm (K.toRepresentation g k)) = j' (natRep g (E.symm k))
  rw [←hje]
  have hE (x : K.toSubmodule) : j' (E.symm x) = x :=
    congrArg Subtype.val (E.apply_symm_apply x)
  rw [hE,hE]
  rfl

end Representation.SL2NaturalSelfExtension
