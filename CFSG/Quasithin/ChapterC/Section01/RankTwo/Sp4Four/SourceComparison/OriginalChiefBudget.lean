module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ChiefQuotient
public import Theory.GroupTheory.PResidual.Restriction

/-!
# The symplectic chief budget inside an ambient extension

The actor lies over the simple residual image, while the original ambient
quotient may have outer automorphisms. Restrict to the full preimage of that
image, apply the symplectic chief budget to the literal radius and seed, then
map back. The embedded residual is unchanged; no inner-ambient hypothesis or
characteristic replacement is needed. The index subgroup need not be normal.

The original tensor radius application is GenerationTwoSymplecticRadiusChief.
Source: MS93 (5.2)(i), printed p.914, with the original maps of 9.3.10.
-/

public section
open Subgroup Theory.GroupTheory
open NoncentralChiefRefinement.SymmetricSixBudget
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
variable {H J F : Type*} [Group H] [Finite H] [Group J] [Finite J] [Field F] [Finite F]

/-- Restrict the chief budget to the full preimage of the residual image,
then return its conclusion to the original group. -/
theorem original_symplectic_residual_dichotomy_of_index
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (q : H →* J) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hcard : Nat.card ((pResidual 2 H).map q) = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hinner : A.map q ≤ (pResidual 2 H).map q)
    (hlarge : Nat.card F^2 ≤ q.ker.relIndex A)
    (P : Subgroup H) (hcomm : ⁅V ⊓ P,A⁆ ≤ Z) (hindex : P.relIndex V ≤ Nat.card F^3)
    (X : Subgroup H) [X.Normal] (hXV : X ≤ V) :
    ⁅X,pResidual 2 H⁆ ≤ Z ∨ ⁅V,pResidual 2 H⁆ ≤ X ⊔ Z := by
  let B := (pResidual 2 H).map q
  let N := B.comap q
  have hKN : q.ker ≤ N := fun x hx => by
    change q x ∈ B
    rw [show q x=1 from hx]
    exact B.one_mem
  have hRN : pResidual 2 H ≤ N := le_comap_map q _
  have hVN : V ≤ N := hV.trans hKN
  have hZN : Z ≤ N := hZV.trans hVN
  have hAN : A ≤ N := (map_le_iff_le_comap).mp hinner
  have hXN : X ≤ N := hXV.trans hVN
  let f : N →* B := (q.comp N.subtype).codRestrict B (fun x => x.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨x,hx⟩ := hq b.val
    exact ⟨⟨x,show q x ∈ B from hx ▸ b.property⟩,Subtype.ext hx⟩
  have hfker : f.ker = q.ker.subgroupOf N := by
    ext x
    exact Subtype.ext_iff
  have hfp : IsPGroup 2 f.ker := by
    rw [hfker]
    exact hp.comap_subtype
  have hres : (pResidual 2 N).map N.subtype = pResidual 2 H := by
    have hh := embedded_pResidual_eq_of_le_of_residual_le 2 (show N ≤ ⊤ from le_top)
      (show (pResidual 2 (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype ≤ N by
        change (pResidual 2 (⊤ : Subgroup H)).map Subgroup.topEquiv.toMonoidHom ≤ N
        rw [map_pResidual]
        exact hRN)
    change (pResidual 2 N).map N.subtype =
      (pResidual 2 (⊤ : Subgroup H)).map Subgroup.topEquiv.toMonoidHom at hh
    rwa [map_pResidual] at hh
  have hVm : (V.subgroupOf N).map N.subtype = V := map_subgroupOf_eq_of_le hVN
  have hZm : (Z.subgroupOf N).map N.subtype = Z := map_subgroupOf_eq_of_le hZN
  have hAm : (A.subgroupOf N).map N.subtype = A := map_subgroupOf_eq_of_le hAN
  have hXm : (X.subgroupOf N).map N.subtype = X := map_subgroupOf_eq_of_le hXN
  let := IsElementaryAbelian.subgroupOf (p := 2) hAN
  let : IsElementaryAbelian 2 ((A.subgroupOf N).map f) := IsElementaryAbelian.map f
  have hlarge' : Nat.card F^2 ≤ Nat.card ((A.subgroupOf N).map f) := by
    rw [←relIndex_ker,hfker,←relIndex_map_map_of_injective _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le hKN,hAm]
    exact hlarge
  have hindex' : (P.subgroupOf N).relIndex (V.subgroupOf N) ≤ Nat.card F^3 := by
    change (P.comap N.subtype).relIndex (V.subgroupOf N) ≤ _
    rw [relIndex_comap,hVm]
    exact hindex
  have hcomm' : ⁅V.subgroupOf N ⊓ P.subgroupOf N,A.subgroupOf N⁆ ≤ Z.subgroupOf N := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ N.subtype_injective,hVm,hAm,hZm]
    exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans hcomm
  have hd := NonbinarySymplectic.symplectic_residual_dichotomy_modulo hF hn hcard hsq
    f hf hfp (V.subgroupOf N) (Z.subgroupOf N) (comap_mono hZV)
    (by rw [hfker]; exact comap_mono hV) (A.subgroupOf N) hlarge'
    ((centralizerModulo_relIndex_le_of_commutator _ _ _ _ hcomm').trans hindex')
    (X.subgroupOf N) (comap_mono hXV)
  rcases hd with hd | hd
  · left
    have hm := map_mono (f := N.subtype) hd
    rwa [map_commutator,hXm,hres,hZm] at hm
  · right
    have hm := map_mono (f := N.subtype) hd
    rwa [map_commutator,hVm,hres,Subgroup.map_sup,hXm,hZm] at hm

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
