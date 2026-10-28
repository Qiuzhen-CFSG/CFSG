module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.IrreducibleInner
public import Theory.Representation.CubicClifford.IndexTwoDisplacement
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.SourceComparison
public import Theory.SpecificGroups.BinaryLinear.SylowCentralClosure
public import CFSG.Quasithin.ChapterG.Section06.IrreducibleCentral
public import Theory.Representation.BinaryFullLinearRecognition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The full binary linear automorphism branch of partner-chief recognition

The inner index-two restriction is either irreducible or a pair of simple
conjugate constituents. The former case is recognized by the degree sieves
in IrreducibleInner. In the latter case choose the outer conjugator in the
marked Sylow subgroup. It commutes with the central involution, so the
rank-two displacement splits into two rank-one displacements. G.6.4 on
each faithful constituent gives its natural degree. The actual natural
coordinates and the outer exchange then give the full natural-plus-dual
action, including the graph automorphism.

This proves both action branches for Aut(L₄(2)) and Aut(L₅(2)) without
assuming irreducibility on the component, a module identification, or a
classification callback. The source consumer is LinearSource.

Source: Aschbacher–Smith 15.2.27(2), printed p.1119; G.6.4,
printed pp.345–346; Clifford theory, Isaacs, Theorem 6.5.
-/

public section
open Subgroup Representation Theory.GroupTheory
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
open CFSG CFSG.Quasithin
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

private instance (n : ℕ) : Finite (LinearGroup n) := Finite.of_injective
  (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem linear_card (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

theorem central_rank_one_dimension
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    {I W : Type*} [Group I] [Finite I] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (eI : I ≃* LinearGroup n)
    (ρ : Representation (ZMod 2) I W) [IsIrreducible ρ]
    (hsq : IsSQTK KnownSimple.IsKnownSimple I) (hf : Function.Injective ρ)
    (a : I) (ho : orderOf a = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 1)
    (S : Sylow 2 I) (haS : a ∈ S) (hc : ∀ s ∈ S, Commute a s) :
    Module.finrank (ZMod 2) W = n := by
  have hcore : pCore 2 I = ⊥ := by
    have hle := normal_p_subgroup_le_ker ρ (pCore 2 I) pCore_isPGroup
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hle
    exact bot_unique hle
  have hh := ChapterG.Section06.hypotheses_of_irreducible ρ (MonoidHom.id I)
    hsq Function.surjective_id hcore hf a
    (by simpa only [ho] using pow_orderOf_eq_one a)
    (by intro he; rw [he,orderOf_one] at ho; omega) (by omega)
  have hz : a ∈ (center S).map (S : Subgroup I).subtype := by
    refine ⟨⟨a,haS⟩,mem_center_iff.mpr (fun s => Subtype.ext (hc s s.property).eq.symm),rfl⟩
  have hm := ((ChapterG.Section06.lemma_G_6_4 hh hr).2 S hz).2
  have hcard : Nat.card I = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) :=
    (Nat.card_congr eI.toEquiv).trans (linear_card n)
  rcases hm with ⟨m,hlo,hhi,j,E,_,_⟩ | ⟨j,E,_,_⟩ | ⟨j,E,_,_⟩ | ⟨j,E,_,_⟩
  · have hc : Nat.card I = Nat.card (LinearGroup m) :=
      (Nat.card_congr Subgroup.topEquiv.symm.toEquiv).trans (Nat.card_congr j.toEquiv)
    rw [hcard,linear_card] at hc
    have he : m = n := by
      rcases hn with rfl | rfl <;> interval_cases m <;>
        norm_num [Fin.prod_univ_succ] at hc <;> omega
    have hd := (Submodule.topEquiv (R := ZMod 2) (M := W)).symm.trans E |>.finrank_eq
    simpa only [Module.finrank_pi,Fintype.card_fin,he] using hd
  all_goals
    have hc := (Nat.card_congr Subgroup.topEquiv.symm.toEquiv).trans (Nat.card_congr j.toEquiv)
    rw [hcard] at hc
    rcases hn with rfl | rfl <;>
      norm_num [Fin.prod_univ_succ,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hc


theorem linear_action_model {n : ℕ} (hn : n = 4 ∨ n = 5)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (MulAut (LinearGroup n)) W)
    [IsIrreducible ρ]
    (hsq : IsSQTK KnownSimple.IsKnownSimple (MulAut (LinearGroup n)))
    (hf : Function.Injective ρ)
    (hq : BinaryOffender.quadraticRatio ρ ≤ 2)
    (S : Sylow 2 (MulAut (LinearGroup n))) (a : MulAut (LinearGroup n))
    (haS : a ∈ S) (ho : orderOf a = 2)
    (hc : ∀ s ∈ S, Commute a s)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 2) :
    SmallDisplacementParabolics.ActionModel ρ := by
  let I := MulAut.innerSubgroup (LinearGroup n)
  by_cases hi : IsIrreducible (ρ.comp I.subtype)
  · exact irreducible_inner_model hn ρ hsq hf hq hi
  have hSI : ¬ (S : Subgroup (MulAut (LinearGroup n))) ≤ I := by
    intro hle
    apply S.not_dvd_index
    have hh := index_dvd_of_le hle
    change I.index ∣ _ at hh
    rwa [inner_index hn] at hh
  obtain ⟨t,htS,htI⟩ := SetLike.not_le_iff_exists.mp hSI
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨C,hC⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp I.subtype)
  let : IsIrreducible C.toRepresentation := hC
  obtain ⟨hd,⟨e⟩⟩ := (CubicClifford.Inertia.restriction_dichotomy ρ I
    (inner_index hn) t htI C hC).resolve_left hi
  let : IsSimpleGroup I := (innerEquiv (by omega : 0 < n)).symm.isSimpleGroup_congr.mpr
    (linear_simple (by omega : 3 ≤ n))
  have hfC := CubicClifford.Inertia.constituent_faithful ρ hf I
    (inner_index hn) t htI C hC
  have haI := central_sylow_automorphism_inner hn S a hc
  let aI : I := ⟨a,haI⟩
  have hrC := CubicClifford.Inertia.constituent_rank_one_of_rank_two ρ I C t aI
    (hc t htS).symm e hr
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal I
  have haP : aI ∈ P := by
    change aI ∈ (P : Subgroup I)
    rw [hP]
    exact haS
  have hoI : orderOf aI = 2 := (Subgroup.orderOf_coe aI).symm.trans ho
  have hcP : ∀ p ∈ P, Commute aI p := by
    intro p hp
    have hpS : (p : MulAut (LinearGroup n)) ∈ S := by
      change p ∈ (P : Subgroup I) at hp
      rw [hP] at hp
      exact hp
    exact Subtype.ext (hc p hpS).eq
  have hdim := central_rank_one_dimension hn (innerEquiv (by omega : 0 < n)).symm
    C.toRepresentation (hsq.subgroup I) hfC aI hoI hrC P haP hcP
  let j₀ := (innerEquiv (by omega : 0 < n)).symm.trans (slEquivLinear n).symm
  obtain ⟨j,f,hf'⟩ := BinaryFullLinearRecognition.exists_natural_equiv
    C.toRepresentation hfC j₀ hdim
  let U := C.toSubmodule
  let U' := U.map (ρ t⁻¹)
  have hdim' : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U := by
    exact (LinearEquiv.ofBijective (ρ t⁻¹) (Representation.apply_bijective ρ t⁻¹)).finrank_map_eq U
  have hsum : U ⊔ U' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have he := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at he
    change Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) U at he
    have hh := U.finrank_sup_add_finrank_inf_eq U'
    rw [hd.eq_bot,finrank_bot,add_zero,hdim'] at hh
    omega
  have hcompl : IsCompl U U' := ⟨hd,codisjoint_iff.mpr hsum⟩
  let β : LinearGroup n ≃* LinearGroup n :=
    (innerEquiv (by omega : 0 < n)).trans (j.trans (slEquivLinear n))
  let d := coordinateAction hn
  have hnat (g : LinearGroup n) (x : Space n) :
      ρ (MulAut.conj g) (f.symm x : W) = (f.symm (β g x) : W) := by
    let l : I := innerEquiv (by omega : 0 < n) g
    have hh := hf' l (f.symm x)
    have hh' : f (C.toRepresentation l (f.symm x)) = β g x := by
      rw [f.apply_symm_apply] at hh
      simpa only [β,MulEquiv.trans_apply,slEquivLinear_apply] using hh
    exact congrArg Subtype.val ((f.symm_apply_apply _).symm.trans (congrArg f.symm hh'))
  obtain ⟨_,E,_,_,hE⟩ := BinaryNaturalDual.ModelOrbits.MarkedComparison.exists_equiv_of_automorphismEquiv
    hn d ρ (MulEquiv.refl _) β hcompl f hnat
    ⟨t⁻¹,fun hh => htI (I.inv_mem hh),rfl⟩
  refine Or.inr (Or.inl ⟨n,hn,d,MulAut.congr β,⟨Representation.Equiv.mk E ?_⟩⟩)
  intro g
  apply LinearMap.ext
  intro w
  exact hE g w

end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
