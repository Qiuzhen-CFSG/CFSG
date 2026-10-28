module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSwap
public import Theory.GroupTheory.QuaternionResidualSwapEquivalence
/-!
# Marked comparison of the original ordinary point endpoint

The original source packet supplies two commuting SL₂(3) residual factors
and an involution exchanging them. A matching packet in a model point group
therefore constructs a whole-group equivalence by central-product gluing
and the involution complement. The two-core and its center are intrinsic;
the recovered module C_{O₂(H)}(v)⟨v⟩ and its normalizer retain the original
V₁, V and Borel markings.

This is the comparison step in Aschbacher--Smith 13.5.17, printed p.922.
The explicit packet in the literal unitary point group, and compatibility
with the plane endpoint on the common Borel, remain separate inputs to the
final marked amalgam recognition. No desired point equivalence is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u v
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)

include d hA312 hH hU hn

/-- The original ordinary point endpoint is recognized from a matching
swapped residual packet, retaining its original central line, module and Borel. -/
theorem normal_ordinary_point_comparison
    (hordinary : L ⊔ (T : Subgroup G) = L)
    {P : Type v} [Group P] [Finite P]
    (qP : QuaternionCentralProductData (pCore 2 P))
    (cP : QuaternionResidualCentralProduct (pCore 2 P) qP)
    (w : P) (hw : w^2=1)
    (hcP : (pResidual 2 P).IsComplement' (zpowers w))
    (hsP : cP.left.map (MulAut.conj w).toMonoidHom=cP.right) :
    ∃ v : H, (v : G)∈V ∧ ∃ e : H ≃* P, e v=w ∧
      (pCore 2 H).map e.toMonoidHom=pCore 2 P ∧
      (V₁.subgroupOf H).map e.toMonoidHom=(center (pCore 2 P)).map (pCore 2 P).subtype ∧
      (V.subgroupOf H).map e.toMonoidHom=
        (pCore 2 P ⊓ centralizer ({w} : Set P)) ⊔ zpowers w ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H).map e.toMonoidHom=
        normalizer (((pCore 2 P ⊓ centralizer ({w} : Set P)) ⊔ zpowers w : Subgroup P) : Set P) := by
  obtain ⟨v,hv,hv2,hcomp,q,hz,c,hs,_,hV⟩ :=
    normal_ordinary_point_swapped_decomposition d hA312 hH hU hn hordinary
  obtain ⟨e,he,_⟩ := c.exists_mulEquiv_of_swap cP v w hv2 hw hcomp hcP hs hsP
    (c.left_model.some.trans cP.left_model.some.symm)
  have hline : V₁.subgroupOf H=(center (pCore 2 H)).map (pCore 2 H).subtype := by
    rw [←hz,←map_map]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hVm : (V.subgroupOf H).map e.toMonoidHom=
      (pCore 2 P ⊓ centralizer ({w} : Set P)) ⊔ zpowers w := by
    rw [hV,map_fixed_core_join_zpowers,he]
  refine ⟨v,hv,e,he,pCore_map_iso 2 e,?_,hVm,?_⟩
  · rw [hline,map_center_two_core]
  · rw [normal_point_borel_intrinsic d hA312 hH hU hn,
      map_normalizer_eq_of_bijective _ e.bijective,hVm]
end CFSG.Quasithin.Chapter13.Section05.A5Source
