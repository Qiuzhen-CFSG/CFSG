module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSelection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicEndomorphisms
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicImage

public import Theory.Representation.Quotient

/-!
# Cubic containment on two natural SL₃ copies

The natural endomorphism field counts the actual simple constituents. An
element of order three fixes one because the field-unit order is divisible
by three. Restrict to its setwise stabilizer and transport the original
action to this constituent. CubicImage then proves containment, including
the nonsplit prime-to-three action kernel and the full SL₃ center.

The explicit doubled-module isomorphism is the multiplicity premise of
Aschbacher--Smith A.3.19, pp.54--55. CubicFull applies this result to the
literal full normalizer orbit; the preliminary source owner retains the
proof that this multiplicity premise holds there.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups MonoidAlgebra
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
section Coordinates
variable {H W E : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup E] [Module (ZMod 2) E]

/-- Turn actual binary product coordinates and their intertwining equations
into a group-algebra isomorphism, retaining the same acting group. -/
def doubleModuleEquiv (ρ : Representation (ZMod 2) H W)
    (μ : Representation (ZMod 2) H E)
    (e : W ≃ₗ[ZMod 2] E × E)
    (he : ∀ g v, e (ρ g v) = (μ g (e v).1, μ g (e v).2)) :
    ρ.asModule ≃ₗ[(ZMod 2)[H]] μ.asModule × μ.asModule := by
  let f : ρ.IntertwiningMap μ := {
    toLinearMap := (LinearMap.fst (ZMod 2) E E).comp e.toLinearMap
    isIntertwining' g := LinearMap.ext (fun v => congrArg Prod.fst (he g v)) }
  let q : ρ.IntertwiningMap μ := {
    toLinearMap := (LinearMap.snd (ZMod 2) E E).comp e.toLinearMap
    isIntertwining' g := LinearMap.ext (fun v => congrArg Prod.snd (he g v)) }
  let j := (IntertwiningMap.equivLinearMapAsModule ρ μ f).prod
    (IntertwiningMap.equivLinearMapAsModule ρ μ q)
  exact LinearEquiv.ofBijective j e.bijective
end Coordinates

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]

/-- Every cubic lies in the marked component when the original restriction
is two natural copies and the ambient three-rank is at most two. -/
theorem cubic_mem_of_double_natural (F : BinaryField)
    (L : Subgroup H) [L.Normal] (η : L →* SL(3,F.Carrier))
    (hη : Function.Surjective η) (hηker : Nat.Coprime 3 (Nat.card η.ker))
    (ρ : Representation (ZMod 2) H W)
    (e : Representation.asModule (ρ.comp L.subtype) ≃ₗ[(ZMod 2)[L]]
      Representation.asModule ((linearNatural F 3).comp η) ×
        Representation.asModule ((linearNatural F 3).comp η))
    (hd : 3 ∣ Nat.card F.Carrier - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  let μ : Representation (ZMod 2) L (Fin 3 → F.Carrier) := (linearNatural F 3).comp η
  let : IsIrreducible μ := (irreducible_comp_surjective_iff η hη _).mpr
    (ExtensionConsequences.linearNatural_irreducible F (by decide))
  let : Finite μ.asModule := Finite.of_equiv (Fin 3 → F.Carrier) μ.asModuleEquiv.symm.toEquiv
  have hcard : 3 ∣ Nat.card (Module.End (ZMod 2)[L] μ.asModule) - 1 := by
    have heq : μ = (Representation.SL3OddNaturalNormalizer.binaryNatural F.Carrier).comp η := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro v
      rfl
    rw [heq, natural_end_card η hη]
    exact hd
  have hP : IsPGroup 3 (zpowers x) :=
    (isPGroup_iff_orderOf_dvd_pow).mpr (fun y => by
      refine ⟨1, ?_⟩
      have h : orderOf y ∣ 3 := by
        have hy := orderOf_dvd_natCard y
        have hc : Nat.card (zpowers x) = orderOf x := Nat.card_zpowers x
        rw [hc] at hy
        exact hy.trans (orderOf_dvd_of_pow_eq_one hx)
      exact h)
  obtain ⟨U,_,⟨a⟩,hU⟩ := invariant_simple_of_double ρ L e hcard (zpowers x) hP
  let eU : U.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → F.Carrier) := a.restrictScalars (ZMod 2)
  have ha (g : L) (v : U.toSubmodule) :
      eU (U.toRepresentation g v) = (η g).val.mulVec (eU v) := by
    let v' : U.asSubmodule := ⟨v.val,v.property⟩
    have hh := a.map_smul (MonoidAlgebra.single g (1 : ZMod 2)) v'
    have he : ((MonoidAlgebra.single g (1 : ZMod 2)) • v' : U.asSubmodule) =
        U.toRepresentation g v' := by
      apply Subtype.ext
      simp only [SetLike.val_smul, Representation.single_smul, one_smul]
      rfl
    rw [he] at hh
    have hs := Representation.single_smul μ 1 g (a v')
    rw [one_smul] at hs
    rw [hs] at hh
    change a (U.toRepresentation g v') = μ g (a v')
    exact hh
  let H₀ := BinaryOffender.subspaceStabilizer ρ U.toSubmodule
  have hLH : L ≤ H₀ := BinaryOffender.le_subspaceStabilizer ρ U.toSubmodule
    (fun g hg v hv => U.apply_mem_toSubmodule ⟨g,hg⟩ hv)
  have hxH : x ∈ H₀ := by
    have hn : zpowers x ≤ H₀ := BinaryOffender.le_subspaceStabilizer ρ U.toSubmodule (by
      intro g hg v hv
      rw [← hU ⟨g,hg⟩]
      exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
    exact hn (mem_zpowers x)
  let L₀ := L.subgroupOf H₀
  let : L₀.Normal := inferInstance
  let q : L₀ ≃* L := subgroupOfEquivOfLe hLH
  let η₀ : L₀ →* SL(3,F.Carrier) := η.comp q.toMonoidHom
  have hker : Nat.Coprime 3 (Nat.card η₀.ker) := by
    have hk : η₀.ker = η.ker.comap q.toMonoidHom := rfl
    rw [hk, comap_equiv_eq_map_symm', card_map_of_injective q.symm.injective]
    exact hηker
  let τ : Representation (ZMod 2) H₀ (Fin 3 → F.Carrier) :=
    (eU.conjRingEquiv.toMonoidHom).comp (BinaryOffender.stabilizerRepresentation ρ U.toSubmodule)
  have hnat (g : L₀) (v : Fin 3 → F.Carrier) :
      τ (g : H₀) v = (η₀ g).val.mulVec v := by
    change eU (U.toRepresentation (q g) (eU.symm v)) = _
    rw [ha, eU.apply_symm_apply]
    rfl
  have hh := cubic_mem_of_natural_quotient L₀ η₀ (hη.comp q.surjective) hker τ hnat hd
    ((Theory.GroupTheory.primeRank_le_of_injective 3 H₀.subtype H₀.subtype_injective).trans hr)
    ⟨x,hxH⟩ (Subtype.ext hx)
  exact hh
/-- The same containment from concrete binary coordinates, without requiring
a caller to construct a group-algebra module structure. -/
theorem cubic_mem_of_double_coordinates (F : BinaryField)
    (L : Subgroup H) [L.Normal] (η : L →* SL(3,F.Carrier))
    (hη : Function.Surjective η) (hηker : Nat.Coprime 3 (Nat.card η.ker))
    (ρ : Representation (ZMod 2) H W)
    (e : W ≃ₗ[ZMod 2] (Fin 3 → F.Carrier) × (Fin 3 → F.Carrier))
    (he : ∀ (g : L) (v : W), e (ρ g v) =
      ((η g).val.mulVec (e v).1, (η g).val.mulVec (e v).2))
    (hd : 3 ∣ Nat.card F.Carrier - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  apply cubic_mem_of_double_natural F L η hη hηker ρ
    (doubleModuleEquiv (ρ.comp L.subtype) ((linearNatural F 3).comp η) e he) hd hr x hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
