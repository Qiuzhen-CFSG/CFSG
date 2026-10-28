module
public import CFSG.Quasithin.ChapterB.Section02.AlternatingFivePoint
public import Theory.Representation.BinaryPermutation.FiveSylowPoint
public import Theory.SpecificGroups.AlternatingSix.PairedCubicResidual
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.NoncentralChiefRefinement.ExhaustedTwoLayers
public import Theory.GroupTheory.NormalSectionTwoResidual
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.PCoreSurjective

/-!
# The core layer forced by an A₅ point chief budget

For a nonzero Sylow-fixed point of the actual deleted five-point module,
the point centralizer maps onto A₄ with its exact two-core kernel. Its
two-residual moves the module and the quotient Klein four. These separated
layers exhaust a budget of two noncentral binary chief factors, so the
middle core quotient is fixed. Normality of that section and simplicity
of A₅ promote the bound to the full two-perfect group. Its intrinsic
commutator layer is therefore the originally marked module.

No full-core marking or splitting is assumed. The original 13.4 consumer
constructs this budget from the five-dimensional augmentation short block.
Source: Aschbacher–Smith 13.4.10(1), printed p.908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.ChapterB.AlternatingFivePoint
variable {H : Type*} [Group H] [Finite H]
variable (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
  (q : H →* alternatingGroup (Fin 5))
  (hq : Function.Surjective q) (hk : q.ker = pCore 2 H)
  (e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
  (he : ∀ h u, (e (MulAut.conjNormal h u)).toAdd =
    BinaryPermutation.coreRepresentation (Fin 5) (q h).val (e u).toAdd)

private theorem four_twoResidual : pResidual 2 (alternatingGroup (Fin 4)) = ⊤ := by
  apply top_unique
  rw [← AlternatingSix.PairedCubicResidual.alternatingFour_primeToResidual]
  exact primeToResidual_three_le_twoResidual

include hq hk he in
/-- The two noncentral factors of the reciprocal point residual exhaust
its natural-module and quotient layers, identifying the full core commutator. -/
theorem core_commutator_of_point_chief_budget
    (hperfect : IsPPerfect 2 H) (hU : ⁅U,(⊤ : Subgroup H)⁆ = U)
    (w : U) (hw : w ≠ 1) (S : Sylow 2 H)
    (hSw : (S : Subgroup H) ≤ centralizer ({w.val} : Set H))
    (hcount : ∀ s : ChiefSeries (primeToResidual 3 (centralizer ({w.val} : Set H))),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅pCore 2 H,(⊤ : Subgroup H)⁆ = U := by
  let C := centralizer ({w.val} : Set H)
  have hQC : pCore 2 H ≤ C := by
    rw [←hk,kernel_centralizer U q e he]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx w.val w.property).symm
  have hUQ : U ≤ pCore 2 H := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hUC : U ≤ C := hUQ.trans hQC
  have hv : (e w).toAdd ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  let P := S.mapSurjective (f := q) hq
  have hs : BinaryPermutation.FiveGeometry.form (e w).toAdd = 0 := by
    apply BinaryPermutation.FiveSylowSingular.fixed_singular P
    rintro a ⟨x,hx,rfl⟩
    change BinaryPermutation.coreRepresentation (Fin 5) (q x).val (e w).toAdd = (e w).toAdd
    rw [←he]
    apply congrArg (fun v : U => (e v).toAdd)
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hSw hx))
  obtain ⟨a⟩ := BinaryPermutation.FiveSylowPoint.stabilizer_equiv (e w).toAdd hv hs
  obtain ⟨f₀,hf₀,hk₀⟩ := point_centralizer_projection U q hq e he w
  let f : C →* alternatingGroup (Fin 4) := a.toMonoidHom.comp f₀
  have hf : Function.Surjective f := a.surjective.comp hf₀
  have hfk : f.ker = (pCore 2 H).subgroupOf C := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,hk₀,hk]
  have hp : IsPGroup 2 f.ker := by rw [hfk]; exact pCore_isPGroup.comap_subtype
  have hr : (pResidual 2 C).map f = ⊤ :=
    (map_pResidual_of_surjective 2 f hf).trans four_twoResidual
  have h23 := (point_centralizer_cubic U q hq hk e he w hw).2
  have hres : pResidual 2 C = primeToResidual 3 C := twoResidual_eq_primeToResidual_three h23
  have hc : ∀ s : ChiefSeries (pResidual 2 C),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2 := by
    rw [hres]
    exact hcount
  let W : NormalNode C := ⟨U.subgroupOf C,inferInstanceAs (U.subgroupOf C).Normal⟩
  let Q : NormalNode C := ⟨(pCore 2 H).subgroupOf C,inferInstanceAs ((pCore 2 H).subgroupOf C).Normal⟩
  let R : NormalNode C := ⟨pCore 2 C,inferInstanceAs (pCore 2 C).Normal⟩
  have hWQ : W ≤ Q := comap_mono hUQ
  have hQR : Q ≤ R := by
    change (pCore 2 H).subgroupOf C ≤ pCore 2 C
    exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  have hW : ⁅W.val,pResidual 2 C⁆ ≠ ⊥ := by
    intro hz
    have hfix := commutator_eq_bot_iff_le_centralizer.mp hz
    have hle : pResidual 2 C ≤ f.ker := by
      rw [hfk,←hk,kernel_centralizer U q e he]
      intro x hx u hu
      have hh := hfix (show (⟨u,hUC hu⟩ : C) ∈ W.val from hu) x hx
      exact (congrArg (fun y : C => y.val) hh).symm
    have hh := (Subgroup.map_eq_bot_iff _).mpr hle
    rw [hr] at hh
    exact top_ne_bot hh
  have hupper : ¬ ⁅R.val,pResidual 2 C⁆ ≤ Q.val := by
    intro hh
    have heq : (⁅R.val,pResidual 2 C⁆).map f = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (hh.trans hfk.ge)
    have hcore : (pCore 2 C).map f = pCore 2 (alternatingGroup (Fin 4)) := by
      rw [← f.comap_pCore_of_ker_isPGroup hf hp,map_comap_eq_self]
      rw [f.range_eq_top_of_surjective hf]
      exact le_top
    change (⁅pCore 2 C,pResidual 2 C⁆).map f = ⊥ at heq
    rw [map_commutator,hcore,hr] at heq
    have hcen : pCore 2 (alternatingGroup (Fin 4)) ≤ center (alternatingGroup (Fin 4)) := by
      simpa only [coe_top,centralizer_univ] using (commutator_eq_bot_iff_le_centralizer.mp heq)
    rw [alternatingGroup.center_eq_bot (by simp)] at hcen
    have he := congrArg (fun B : Subgroup (alternatingGroup (Fin 4)) => Nat.card B) (le_bot_iff.mp hcen)
    rw [AlternatingFourPair.twoCore_eq_kleinFour,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp)] at he
    norm_num at he
  have hbound := residual_commutator_le_of_two_used_layers W Q R hWQ hQR
    pCore_isPGroup hW hupper hc
  let J := (pResidual 2 C).map C.subtype
  have hcomm : ⁅pCore 2 H,J⁆ ≤ U := by
    have hh := map_mono (f := C.subtype) hbound
    simpa only [Q,W,map_commutator,map_subgroupOf_eq_of_le hQC,
      map_subgroupOf_eq_of_le hUC] using hh
  have hj : ¬ J ≤ q.ker := by
    intro hh
    have hjf : pResidual 2 C ≤ f.ker := by
      rw [hfk,←hk]
      intro x hx
      exact hh (mem_map_of_mem C.subtype hx)
    have hb := (Subgroup.map_eq_bot_iff _).mpr hjf
    rw [hr] at hb
    exact top_ne_bot hb
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hb := commutator_pResidual_le_of_simple_kernel_escape 2 q hq
    (by rw [hk]; exact pCore_isPGroup) (pCore 2 H) U J hj hcomm
  rw [(pResidual_eq_top_iff 2 H).mpr hperfect] at hb
  exact le_antisymm hb (hU.symm.le.trans (commutator_mono hUQ le_rfl))

end CFSG.Quasithin.ChapterB.AlternatingFivePoint
