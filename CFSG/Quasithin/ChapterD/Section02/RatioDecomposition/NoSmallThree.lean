module
public import CFSG.Quasithin.ChapterD.Section02.JhatRestriction
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFixedSupplement

/-!
# The no-small-three reduction on the original Jhat action

The cyclic source theorem makes the three-core fixed space globally fixed
on Jhat. Its odd moved support therefore retains faithfulness, the cubic
minimum and the original starred actors. The three-core acts fully on that
support and lies in the Fitting subgroup, so D.2.16 supplies the finite family
of indecomposables. Every action and embedding is the literal restriction
of the original representation; no odd-kernel factorization is an input.

Source: Aschbacher--Smith D.2.26--29, printed pp.191--192, applied in 15.1.2,
first paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
open Theory.GroupTheory CyclicSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

namespace RatioDecomposition
/-- In the no-small-three case the proved fixed supplement supplies the literal
fully Fitting-moved factor datum. No odd-kernel factorization is assumed. -/
theorem noSmallThree_factorData (hf : Function.Injective ρ)
    (hratio : cubicRatio ρ ≤ 2)
    (H : Subgroup G) (hH : H = Jhat ρ)
    (h : CoreHypotheses (ρ.comp H.subtype))
    (hq : cubicRatio (ρ.comp H.subtype) = 2)
    (hfive : ∀ A ∈ QhatStar (ρ.comp H.subtype), ⁅pCore 5 H,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup H, X ≤ pCore 3 H → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp H.subtype) ⊤ X) ≠ 2) :
    let U := subspaceCommutator (ρ.comp H.subtype) ⊤ (pCore 3 H)
    ∃ d : FactorData ρ H U,
      subspaceCommutator d.representation ⊤ (fittingSubgroup H) = ⊤ ∧
        ∃ c : Decomposition d.representation, c.FittingFull := by
  let : H.Normal := by rw [hH]; exact Jhat_normal ρ
  let P := (pCore 3 H).map H.subtype
  let : P.Normal := inferInstanceAs ((pCore 3 H).map H.subtype).Normal
  have hPH : P ≤ H := map_subtype_le _
  have hPS : P.subgroupOf H = pCore 3 H := by
    exact (Subgroup.map_injective H.subtype_injective) (map_subgroupOf_eq_of_le hPH)
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := H)).map H.subtype |>.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  let U := subspaceCommutator ρ ⊤ P
  have hUeq : subspaceCommutator (ρ.comp H.subtype) ⊤ (pCore 3 H) = U :=
    subspaceCommutator_comp_map ρ H.subtype _ _
  have hsup : U ⊔ fixedSpace ρ H = ⊤ := by
    have hs := h.threeCore_fixed_supplement hq hfive hNo
    simpa only [hUeq,fixedSpace_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype] using hs
  have hs := oddMoved_stable ρ H P
  have hsupport : subspaceCommutator ρ ⊤ H = U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
        (show v ∈ U ⊔ fixedSpace ρ H from hsup ▸ Submodule.mem_top)
      have hwg : ρ g w = w := hw ⟨g,hg⟩
      have he : ρ g (u+w) - (u+w) = ρ g u-u := by rw [map_add,hwg]; abel
      rw [he]
      exact U.sub_mem ((hs hg u).mpr hu) hu
    · apply Submodule.span_mono
      rintro _ ⟨p,hp,v,hv,rfl⟩
      exact ⟨p,hPH hp,v,hv,rfl⟩
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hratio
  have hwit : ∃ A ∈ QhatStar ρ, A ≤ H := ⟨A,hA,hH.symm ▸ le_sSup hA⟩
  have ht := side_transport ρ hs hsup le_rfl hwit
  have hfull := oddMovedAction_full_of_le ρ H P hPH hodd (fittingSubgroup H)
    (hPS.symm ▸ pCore_le_fitting H 3)
  have hgen : Jhat (oddMovedAction ρ H P) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
    apply le_antisymm (map_subtype_le _)
    apply hH.le.trans
    apply sSup_le
    intro B hB
    have hBH : B ≤ H := hH.symm ▸ le_sSup hB
    have hB' : B.subgroupOf H ∈ QhatStar (oddMovedAction ρ H P) :=
      (ht.2 _).mpr (by rwa [map_subgroupOf_eq_of_le hBH])
    have hm := Subgroup.map_mono (le_sSup hB') (f := H.subtype)
    simpa only [Jhat,map_subgroupOf_eq_of_le hBH] using hm
  let d : FactorData ρ H U :=
    ⟨oddMovedAction ρ H P,fun _ _ => rfl,side_faithful ρ hf hs hsup le_rfl,hgen,
      by
        apply top_unique
        apply hfull.ge.trans
        apply Submodule.span_mono
        rintro _ ⟨g,hg,v,hv,rfl⟩
        exact ⟨g,Subgroup.mem_top g,v,hv,rfl⟩,
      hsupport,hsup,ht.1,ht.2⟩
  rw [hUeq]
  exact ⟨d,hfull,source_fitting_decomposition d.representation d.faithful d.generated hfull
    (ht.1 ▸ hratio)⟩
end RatioDecomposition
end CFSG.Quasithin.ChapterD
