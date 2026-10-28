module
public import Theory.SpecificGroups.AlternatingSix.CubicLift.SymmetricExtension
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The selected cubic in the original two-core quotient

The image of the original normal component in G/O₂(G) is identified with
L/O₂(L). Its central quotient is the actual alternating image of the given
permutation action. Its center is odd because the ambient two-core quotient
has trivial two-core. The proved ordinary/triple-cover cubic lifting theorem
therefore supplies a genuine invariant cubic in this image, retaining all
original quotient maps and the natural-module movement certificate.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/

public section

open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
open Theory.SpecificGroups.AlternatingSix.CubicLift

variable {G : Type*} [Group G] [Finite G]
theorem exists_quotient_cubic (L R : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hpR : IsPGroup 2 R) (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    ∃ (c : Sym) (M : Subgroup (G ⧸ pCore 2 G)),
      M ≤ L.map (QuotientGroup.mk' (pCore 2 G)) ∧ Nat.card M=3 ∧
      R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)) ∧
      M.map (QuotientGroup.lift (pCore 2 G) q hQ)=zpowers c ∧
      orderOf c=3 ∧ c ∈ alternatingGroup (Fin 6) ∧ r*c*r⁻¹=c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c=⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym)=6 ∧
      ¬Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
        Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c) := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  let B := L.map π
  let : B.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hBq : B.map qb=alternatingGroup (Fin 6) := by
    rw [map_map]
    exact hLq
  let f : B →* alternatingGroup (Fin 6) := (qb.comp B.subtype).codRestrict _
    (fun x => hBq ▸ mem_map_of_mem qb x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y:Sym)∈B.map qb := by rw [hBq]; exact y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  let cover : Covering B (alternatingGroup (Fin 6)) := ⟨f,hf⟩
  have hk : f.ker=center B := cover.ker_eq_center_of_isSimple
  let e : B ⧸ center B ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ x : B, qb x=(GLS3.Chapter5.alternatingQuotientHom e x : Sym) := by
    intro x
    rfl
  have ho : Odd (Nat.card (center B)) :=
    GLS3.Chapter5.OddCentralCovers.component_center_odd (pCore_quotient_pCore_eq_bot (G := G) 2)
      B ⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩
  have hRq : (R.map π).map qb=zpowers r := by
    rw [map_map]
    exact hR
  exact exists_ambient_cubic B e ho qb he (R.map π) (hpR.map π) r hr hRq
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
