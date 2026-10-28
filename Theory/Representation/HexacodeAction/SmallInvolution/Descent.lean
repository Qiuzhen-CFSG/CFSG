module
public import Theory.Representation.HexacodeAction.SmallInvolution
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Recognition of the small moving section through its actual residual

The even preimage contains the original two-residual, so full movement and
zero fixed space persist upon restriction. The constituent budget makes this
restriction irreducible. Only now is the two-group kernel killed and the
action descended to the concrete even hexacode cover. Its degree is four
with central kernel, or six with faithful action.

The resulting epimorphism has the original residual as domain and retains
pointwise compatibility with the original representation. Its surjectivity
uses perfectness of the full cubic cover; the center is never discarded in
the faithful case. This supplies the representation step of MS93 (3.8),
printed pp.878--879, for the exceptional faithful-radius application.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace Representation.Hexacode.SmallInvolution
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The sign quotient kills the original two-residual. -/
theorem residual_le_even (π : H →* HexAutomorphisms) :
    pResidual 2 H ≤ evenPreimage π :=
  (pResidual_le_iff_isPGroup_quotient 2 _).mpr (quotient_evenPreimage_isTwoGroup π)

/-- Restriction to the even preimage retains the unique noncentral constituent. -/
theorem even_restriction_irreducible
    (π : H →* HexAutomorphisms) (hE : hexSign.ker ≤ π.range)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W) [Nontrivial W]
    (hfull : subspaceCommutator ρ ⊤ (pResidual 2 H) = ⊤)
    (hfix : fixedSpace ρ (pResidual 2 H) = ⊥)
    (A : Subgroup H) (hAE : A.map π ≤ hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) (htA : t.val ∈ A.map π)
    (hcost : fixedCodim ρ A ≤ 2) : IsIrreducible (ρ.comp (evenPreimage π).subtype) := by
  let P := evenPreimage π
  let f := π.comp P.subtype
  have hEf : hexSign.ker ≤ f.range := by
    intro x hx
    obtain ⟨y,hy⟩ := hE hx
    exact ⟨⟨y,by change hexSign (π y) = 1; rw [hy]; exact hx⟩,hy⟩
  have hpf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (π.ker.comap P.subtype)
    exact hp.comap_subtype
  have hAP : A ≤ P := fun x hx => hAE (mem_map_of_mem π hx)
  have hmap : (A.subgroupOf P).map f = A.map π := by
    change (A.subgroupOf P).map (π.comp P.subtype) = A.map π
    rw [←map_map,map_subgroupOf_eq_of_le hAP]
  have hmov : subspaceCommutator (ρ.comp P.subtype) ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    apply top_unique
    apply hfull.symm.trans_le
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,residual_le_even π hg,v,hv,rfl⟩
  have hfixed : fixedSpace (ρ.comp P.subtype) ⊤ = ⊥ := by
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    apply le_bot_iff.mp
    rw [←hfix]
    exact fixedSpace_antitone ρ (residual_le_even π)
  exact projected_irreducible f hEf hpf (ρ.comp P.subtype) hmov hfixed
    (A.subgroupOf P) (hmap ▸ hAE) t ht (hmap ▸ htA)
    (by rwa [fixedCodim_subgroupOf ρ hAP])

/-- The actual residual surjects onto the cover and carries the descended simple action. -/
theorem exists_residual_model
    (π : H →* HexAutomorphisms) (hE : hexSign.ker ≤ π.range)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W) [Nontrivial W]
    (hfull : subspaceCommutator ρ ⊤ (pResidual 2 H) = ⊤)
    (hfix : fixedSpace ρ (pResidual 2 H) = ⊥)
    (A : Subgroup H) (hAE : A.map π ≤ hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) (htA : t.val ∈ A.map π)
    (hcost : fixedCodim ρ A ≤ 2) :
    ∃ q : pResidual 2 H →* HexEvenAutomorphisms, Function.Surjective q ∧
      ∃ σ : Representation (ZMod 2) HexEvenAutomorphisms W,
        IsIrreducible σ ∧ σ ≠ 1 ∧ (∀ g v, σ (q g) v = ρ g.val v) ∧
        ((center HexEvenAutomorphisms ≤ σ.ker ∧ Module.finrank (ZMod 2) W = 4) ∨
          (Function.Injective σ ∧ Module.finrank (ZMod 2) W = 6)) := by
  let P := evenPreimage π
  let qP : P →* HexEvenAutomorphisms := {
    toFun x := ⟨π x,x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' x y := Subtype.ext (map_mul π x.val y.val) }
  have hqP : Function.Surjective qP := by
    intro g
    obtain ⟨x,hx⟩ := hE g.property
    exact ⟨⟨x,by change hexSign (π x) = 1; rw [hx]; exact g.property⟩,Subtype.ext hx⟩
  have hqker : qP.ker = π.ker.comap P.subtype := by ext x; exact Subtype.ext_iff
  have hpq : IsPGroup 2 qP.ker := by rw [hqker]; exact hp.comap_subtype
  let τ := ρ.comp P.subtype
  let : IsIrreducible τ := even_restriction_irreducible π hE hp ρ hfull hfix A hAE t ht htA hcost
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent qP hqP hpq τ
  have hcomp : σ.comp qP = τ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp qP hqP hpq τ
  let : IsIrreducible σ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_irreducible qP hqP hpq τ
  let q : pResidual 2 H →* HexEvenAutomorphisms := {
    toFun g := ⟨π g,(residual_le_even π) g.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' x y := Subtype.ext (map_mul π x.val y.val) }
  have hperfect : pResidual 2 HexEvenAutomorphisms = ⊤ := by
    let := even_isPerfect
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN htwo
    let := hN
    by_contra hn
    let : Nontrivial (HexEvenAutomorphisms ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (HexEvenAutomorphisms ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let := htwo.isNilpotent
    exact Group.IsPerfect.not_isSolvable (HexEvenAutomorphisms ⧸ N) inferInstance
  have hq : Function.Surjective q := by
    intro z
    have hm : (pResidual 2 P).map qP = ⊤ :=
      (map_pResidual_of_surjective 2 qP hqP).trans hperfect
    obtain ⟨y,hy,hyz⟩ := (show z ∈ (pResidual 2 P).map qP from hm ▸ mem_top z)
    exact ⟨⟨y.val,map_pResidual_le 2 P.subtype (mem_map_of_mem P.subtype hy)⟩,hyz⟩
  have he (g : pResidual 2 H) (v : W) : σ (q g) v = ρ g.val v := by
    exact LinearMap.congr_fun (congrArg (fun η => η ⟨g.val,residual_le_even π g.property⟩) hcomp) v
  have hnσ : σ ≠ 1 := by
    intro hz
    have hh : subspaceCommutator ρ ⊤ (pResidual 2 H) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      rw [←he ⟨g,hg⟩ v,hz]
      exact sub_self v
    rw [hfull] at hh
    exact top_ne_bot (le_bot_iff.mp hh)
  have hAP : A ≤ P := fun x hx => hAE (mem_map_of_mem π hx)
  have htq : t ∈ (A.subgroupOf P).map qP := by
    obtain ⟨x,hx,hxt⟩ := htA
    exact ⟨⟨x,hAP hx⟩,hx,Subtype.ext hxt⟩
  have hle : fixedCodim σ (zpowers t) ≤ fixedCodim σ ((A.subgroupOf P).map qP) := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr htq))
    have h₁ := fixedCodim_add_finrank σ (zpowers t)
    have h₂ := fixedCodim_add_finrank σ ((A.subgroupOf P).map qP)
    omega
  have hc : fixedCodim σ ((A.subgroupOf P).map qP) = fixedCodim ρ A := by
    have hc' : fixedCodim σ ((A.subgroupOf P).map qP) = fixedCodim τ (A.subgroupOf P) := by
      rw [←hcomp]
      unfold fixedCodim
      rw [fixedSpace_comp_map]
    exact hc'.trans (fixedCodim_subgroupOf ρ hAP)
  refine ⟨q,hq,σ,inferInstance,hnσ,he,?_⟩
  exact simple_degree σ hnσ t ht (by omega)

end Representation.Hexacode.SmallInvolution
