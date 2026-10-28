module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The original normalized right factor in a linear extension

An injective marking of the original right parabolic in Aut(PSL₃(F))
identifies its selected factor R with a native point or line local. The
native core calculation applies to the image of S, which only needs to
normalize that local. Transport through the same parabolic embedding gives
O₂(RS) = O₂(R). The genuine F.1.1 local-Sylow factorization, using the
proved right-Borel normalization, then gives S ≤ R.

Here S is literally O₂(N_G(L) ∩ H), and R is any prepared selected factor.
No ambient Sylow is passed through the parabolic map. This is the local
restriction step used by `Linear` to remove the original outer extension.

Source: Aschbacher–Smith F.1.12, printed p.264, and 5.2.6,
printed pp.650–651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalLinear
open Matrix.PSL3.LinearThree.OuterExtensions

variable {X : Type*} [Group X] [Finite X]
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (K U : Subgroup X) (hn : U ≤ normalizer (K : Set X))
  (f : X →* MulAut PSL(3,F)) (hf : Function.Injective f) (point : Bool)
  (hK : K.map f = (localFactor F point).map MulAut.conj)

omit [Finite X] [Finite F] [CharP F 2] in
include hn hK in
private theorem preserves_local (a : X) (ha : a ∈ U) :
    (localFactor F point).map (f a).toMonoidHom = localFactor F point := by
  apply Subgroup.map_injective (Matrix.PSL3.ExtensionBorel.inner_injective F)
  have he : (MulAut.conj (f a)).toMonoidHom.comp MulAut.conj =
      MulAut.conj.comp (f a).toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map, ← he, ← Subgroup.map_map, ← hK]
  have hh := mem_normalizer_iff_map_conj_eq.mp (hn ha)
  change K.map (MulAut.conj a).toMonoidHom = K at hh
  have he' : (MulAut.conj (f a)).toMonoidHom.comp f =
      f.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp
  rw [Subgroup.map_map, he', ← Subgroup.map_map, hh]

omit [Finite X] in
include hm hF hn hf hK in
/-- The marked linear extension has no extra two-core in the local join. -/
private theorem core_eq : (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply Subgroup.map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf, map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup, hK]
  apply AmbientLocalCores.local_join_core_in_aut F hm hF point (U.map f)
  rintro a ⟨x, hx, rfl⟩
  exact preserves_local F K U hn f point hK x hx

/-- The local quotient is transported through the same original embedding. -/
private def quotientEquiv : (K ⧸ pCore 2 K) ≃* PSL(2,F) :=
  let e : K ≃* localFactor F point :=
    ((K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hK)).trans
      ((localFactor F point).equivMapOfInjective MulAut.conj
        (Matrix.PSL3.ExtensionBorel.inner_injective F)).symm
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((localFactorQuotientEquiv F point).trans (Theory.PSL2.sl2QuotientEquiv F))

end OriginalLinear

section SourceRestriction
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (point : Bool)
  (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 →* MulAut PSL(3,F))
  (hf : Function.Injective f)
  (hR : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map f =
    (Matrix.PSL3.LinearThree.OuterExtensions.localFactor F point).map MulAut.conj)

omit [Finite G] in
include d hm hF hf hR in
/-- Recover the original local core equality from the marked extension,
without mapping the ambient Sylow through a parabolic map. -/
theorem Preparation.linear_extension_right_core :
    (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : (sourceS L H).subgroupOf P ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hRP]
    exact comap_mono d.S_normalizes_right
  have hc := OriginalLinear.core_eq F hm hF (R.subgroupOf P)
    ((sourceS L H).subgroupOf P) hn f hf point hR
  have hh := congrArg (Subgroup.map P.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hRP, map_subgroupOf_eq_of_le hSP] at hh
  exact hh

include d h hTH hm hF hf hR in
/-- Normalization of the ORIGINAL right Borel removes the linear outer
supplement: the same S is contained in the selected R. -/
theorem Preparation.sourceS_le_right_of_linear_extension : sourceS L H ≤ R := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let e : R ≃* R.subgroupOf P := (subgroupOfEquivOfLe hRP).symm
  let q : (R ⧸ pCore 2 R) ≃* PSL(2,F) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (OriginalLinear.quotientEquiv F (R.subgroupOf P) f hf point hR)
  have hs := (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1 F q
    d.right_borel_normalizes_sourceS
  change sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ (sourceS L H ⊓ R) at hs
  rw [d.linear_extension_right_core F hm hF point f hf hR] at hs
  exact hs.le.trans (sup_le (map_subtype_le _) inf_le_right)


end SourceRestriction

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
