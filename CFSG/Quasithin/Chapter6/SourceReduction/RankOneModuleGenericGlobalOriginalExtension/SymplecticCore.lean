module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalCoreKernel
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Original symplectic quotient and core transport

A two-element of the core of a local join acts trivially on the local core
quotient. Pulling its commutators back through faithful native conjugation
puts it in the kernel of the actual SL₂ quotient action. The proved native
point/plane kernel calculations make this automorphism inner in the local
factor, so adjoining the original normalizing S adds no two-core.

Transport through the literal right-parabolic embedding gives O₂(RS)=O₂(R).
The F.1.1 relative-Sylow factorization and normalized right Borel then give
S≤R. Separately, at the binary field the native local is solvable; its marked
copy would make the original full source endpoint solvable. Thus the field
restriction needed by the native kernel calculation follows before collapse.
Both nodes and every prepared selected R are retained, with no R=O²(H) or
S=T premise. `Symplectic` uses these results to restrict all three maps.

Source: Aschbacher--Smith F.1.12, p.264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalSymplectic
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable (F : Type) [Field F] [Finite F] [CharP F 2]

/-- The native determinant-one local in the supplied node. -/
@[expose] def localFactor (point : Bool) : Subgroup (Sp F) :=
  if point then pointLocal else planeLocal

/-- The full native parabolic in the supplied node. -/
@[expose] def parabolic (point : Bool) : Subgroup (Sp F) :=
  if point then pointParabolic else planeParabolic

omit [Finite F] in
private theorem inner_injective : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) :=
  Theory.GroupTheory.conj_injective_of_center_eq_bot EvenProjective.center_eq_bot

omit [Finite F] in
private theorem local_join_core (K : Subgroup (Sp F))
    (hdetect : ∀ (a : MulAut (Sp F)) (hK : K.map a.toMonoidHom = K),
      (∃ k : ℕ, a^(2^k)=1) →
      (∀ x : K, restrict a K hK x / x ∈ pCore 2 K) →
      ∃ k : K, a = MulAut.conj k.val)
    (U : Subgroup (MulAut (Sp F))) (hn : U ≤ normalizer (K.map MulAut.conj : Set _)) :
    (K.map MulAut.conj ⊔ U).pCoreIn 2 = (K.map MulAut.conj).pCoreIn 2 := by
  apply join_pCore_eq_of_quotient_action_detection 2 _ U hn
  intro a ha htwo hc
  have hnorm : a ∈ normalizer (K.map MulAut.conj : Set _) :=
    (sup_le (K.map MulAut.conj).le_normalizer hn) ha
  have hK : K.map a.toMonoidHom = K := by
    apply Subgroup.map_injective (inner_injective F)
    have he : MulAut.conj.comp a.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp MulAut.conj := by
      ext x y
      simp
    rw [map_map,he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hnorm
  have hdiff (x : K) : restrict a K hK x / x ∈ pCore 2 K := by
    have hh := hc ⟨MulAut.conj x.val,mem_map_of_mem MulAut.conj x.property⟩
    change ⁅a,MulAut.conj x.val⁆ ∈ (K.map MulAut.conj).pCoreIn 2 at hh
    rw [←map_pCoreIn_of_injective 2 _ _ (inner_injective F)] at hh
    have he : MulAut.conj (restrict a K hK x / x).val = ⁅a,MulAut.conj x.val⁆ := by
      apply MulEquiv.ext
      intro y
      change (a x.val / x.val) * y * (a x.val / x.val)⁻¹ =
        a (x.val * a.symm (x.val⁻¹ * y * x.val) * x.val⁻¹)
      simp only [div_eq_mul_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    rw [←he] at hh
    exact (mem_map_iff_mem K.subtype_injective).mp
      ((mem_map_iff_mem (inner_injective F)).mp hh)
  obtain ⟨k,hk⟩ := hdetect a hK htwo hdiff
  rw [hk]
  exact mem_map_of_mem MulAut.conj k.property

private theorem native_core_eq {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m)
    (point : Bool) (U : Subgroup (MulAut (Sp F)))
    (hn : U ≤ normalizer ((localFactor F point).map MulAut.conj : Set _)) :
    ((localFactor F point).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((localFactor F point).map MulAut.conj).pCoreIn 2 := by
  apply local_join_core F _ ?_ U hn
  intro a hK htwo hc
  cases point
  · obtain ⟨k,_,hk⟩ := plane_core_inner_of_quotient_trivial hF hm a hK htwo hc
    exact ⟨k,hk⟩
  · obtain ⟨k,_,hk⟩ := point_core_inner_of_quotient_trivial hF hm a hK htwo hc
    exact ⟨k,hk⟩

variable {X : Type*} [Group X] (K U : Subgroup X)
  (hn : U ≤ normalizer (K : Set X))
  (f : X →* MulAut (Sp F)) (hf : Function.Injective f) (point : Bool)
  (hK : K.map f = (localFactor F point).map MulAut.conj)

include hn hf hK in
private theorem core_eq {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) :
    (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply Subgroup.map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf,map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup,hK]
  apply native_core_eq F hm hF point (U.map f)
  rw [←hK]
  exact (map_mono hn).trans (le_normalizer_map f)

private def localEquiv : K ≃* localFactor F point :=
  ((K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hK)).trans
    ((localFactor F point).equivMapOfInjective MulAut.conj (inner_injective F)).symm

private def quotientEquiv {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) :
    (K ⧸ pCore 2 K) ≃* PSL(2,F) := by
  let e := localEquiv F K f hf point hK
  refine (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans ?_
  cases point
  · exact (planeLocalCoreQuotientEquiv hF hm).trans (Theory.PSL2.sl2QuotientEquiv F)
  · exact (pointLocalCoreQuotientEquiv hF hm).trans (Theory.PSL2.sl2QuotientEquiv F)
end OriginalSymplectic

section SourceRestriction
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 →* MulAut (Sp F))
  (hf : Function.Injective f)
  (hR : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map f =
    (OriginalSymplectic.localFactor F point).map MulAut.conj)

omit [Finite G] in
include d hm hF hf hR in
/-- Native quotient-action detection supplies the actual original core equality. -/
theorem Preparation.symplectic_extension_right_core :
    (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : (sourceS L H).subgroupOf P ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hRP]
    exact comap_mono d.S_normalizes_right
  have hc := OriginalSymplectic.core_eq F (R.subgroupOf P)
    ((sourceS L H).subgroupOf P) hn f hf point hR hm hF
  have hh := congrArg (Subgroup.map P.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hRP, map_subgroupOf_eq_of_le hSP] at hh
  exact hh

include d h hTH hm hF hf hR in
/-- The normalized right Borel puts the original S in the selected factor R. -/
theorem Preparation.sourceS_le_right_of_symplectic_extension : sourceS L H ≤ R := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let e : R ≃* R.subgroupOf P := (subgroupOfEquivOfLe hRP).symm
  let q : (R ⧸ pCore 2 R) ≃* PSL(2,F) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (OriginalSymplectic.quotientEquiv F (R.subgroupOf P) f hf point hR hm hF)
  have hs := (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1 F q
    d.right_borel_normalizes_sourceS
  change sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ (sourceS L H ⊓ R) at hs
  rw [d.symplectic_extension_right_core F hm hF point f hf hR] at hs
  exact hs.le.trans (sup_le (map_subtype_le _) inf_le_right)

include d h hTH hf hR in
/-- The binary native local cannot be the marked selected factor:
its solvability would make the actual full source parabolic solvable. -/
theorem Preparation.symplectic_extension_parameter (hp : Group.IsPerfect R)
    (hpos : 0 < m) (hcard : Nat.card F = 2^m) : 1 < m := by
  by_contra hgt
  have hm1 : m = 1 := by omega
  have hc : Nat.card F = 2 := by simpa only [hm1,pow_one] using hcard
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let e := (subgroupOfEquivOfLe hRP).symm.trans
    (OriginalSymplectic.localEquiv F (R.subgroupOf P) f hf point hR)
  let a : OriginalSymplectic.parabolic F point ≃* Binary.LocalProduct := by
    cases point
    · exact Binary.planeParabolicEquivProd hc
    · exact Binary.pointParabolicEquivProd hc
  have hKP : OriginalSymplectic.localFactor F point ≤
      OriginalSymplectic.parabolic F point := by
    cases point
    · exact planeLocal_le
    · exact pointLocal_le
  let j := a.toMonoidHom.comp ((inclusion hKP).comp e.toMonoidHom)
  have hj : Function.Injective j :=
    a.injective.comp ((inclusion_injective hKP).comp e.injective)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 2)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective hj
  exact d.parabolics_not_solvable h hp 1
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient 1).mpr (by
      change Group.IsSolvable (R ⧸ pCore 2 R)
      infer_instance))
end SourceRestriction
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
