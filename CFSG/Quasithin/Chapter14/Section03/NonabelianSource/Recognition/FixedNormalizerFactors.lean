module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterPoint
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.BlockElementary
public import Theory.Representation.BinaryConjugationSection.FixedNormalizerFactors

/-!
# Elementary factors normalized by the original local two-core

An element of the local two-core acts trivially on the central quotient
of the quaternion closure. This automorphism is inner, so the two-core
is the product of the closure and its centralizing supplement. Each
natural-plane preimage is an orbit span of an involutory seed lift. The
supplement centralizes the lift and normalizes the seed and parabolic,
therefore it normalizes both factors.

Source: Aschbacher--Smith 14.3.18(4), printed p.996. The final application
retains the literal section and avoids an unnecessary whole-section
commutator assumption.
-/

@[expose] public section
noncomputable section
open Subgroup InvertedCubicTensor
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Invisible action on the extraspecial central quotient is inner; removing
that inner automorphism gives the actual centralizing supplement. -/
theorem core_eq_U_sup_centralizer (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F) (hZ : F.ZU=F.Vi 1)
    (dU : QuaternionCentralProductData F.U) :
    F.H.pCoreIn 2 = F.U ⊔ (F.H.pCoreIn 2 ⊓ centralizer (F.U:Set G)) := by
  have hUQ : F.U≤F.H.pCoreIn 2 := le_pCoreIn_of_normalizes d.two F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)
  apply le_antisymm ?_ (sup_le hUQ inf_le_left)
  intro q hq
  let qh : F.H := ⟨q,pCoreIn_le 2 F.H hq⟩
  have hqker : qh∈F.terminalHatAction.ker := by
    rw [terminal_kernel_of_center_point F d hZ]
    obtain ⟨a,ha,he⟩ := hq
    exact (show a=qh from Subtype.ext he) ▸ ha
  have hqa : quotientAut (center F.U) (F.uAction qh)=1 := hqker
  obtain ⟨u,hu⟩ := (dU.quotientAut_eq_one_iff_inner (F.uAction qh)).mp hqa
  let uh : F.H := ⟨u,F.U_le_H u.property⟩
  have hua : F.uAction uh=MulAut.conj u := by ext x; rfl
  have hc : F.uAction (uh⁻¹*qh)=1 := by
    rw [map_mul,map_inv,hua,hu,inv_mul_cancel]
  have hcu : (u:G)⁻¹*q∈centralizer (F.U:Set G) := by
    intro x hx
    have he := congrArg (fun a : MulAut F.U => (a ⟨x,hx⟩:G)) hc
    change ((u:G)⁻¹*q)*x*((u:G)⁻¹*q)⁻¹=x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hdc : (u:G)⁻¹*q∈F.H.pCoreIn 2⊓centralizer (F.U:Set G) :=
    ⟨(F.H.pCoreIn 2).mul_mem ((F.H.pCoreIn 2).inv_mem (hUQ u.property)) hq,hcu⟩
  have hres := (F.U⊔(F.H.pCoreIn 2⊓centralizer (F.U:Set G))).mul_mem
    ((show F.U≤F.U⊔(F.H.pCoreIn 2⊓centralizer (F.U:Set G)) from le_sup_left) u.property)
    ((show F.H.pCoreIn 2⊓centralizer (F.U:Set G)≤
      F.U⊔(F.H.pCoreIn 2⊓centralizer (F.U:Set G)) from le_sup_right) hdc)
  simpa only [mul_inv_cancel_left] using hres

/-- The local two-core normalizes the actual factors through its
centralizing supplement; no whole-section commutator premise is needed. -/
theorem block_elementary_factors_of_center_point
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    (dU : QuaternionCentralProductData F.U) (dg : ClosureGeometry F)
    (hZ : F.ZU=F.Vi 1) (L : Subgroup G) (g : G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hIG : F.I₂ L≤F.Gi 2) (hIN : ((F.I₂ L).subgroupOf (F.Gi 2)).Normal)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S₃ W)
    (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
      (F.E g) (σ.comp (F.binaryCoreProjection L e)))
    (hE : F.E g=V)
    (hcore : F.I₂ L⊓centralizer (F.Vi 2:Set G)=(F.I₂ L).pCoreIn 2)
    (hW : F.W≤(F.I₂ L).pCoreIn 2)
    (hmark : d.imageSpace F.W=InvertedCubicTensor.multiplicitySpace σ)
    (hfree : ∀w,σ InvertedCubicTensor.cubic w=w→w=0)
    (hdim : Module.finrank (ZMod 2) (InvertedCubicTensor.multiplicitySpace σ)=2)
    (hgen : closure {x:F.W|x^2=1}=⊤) :
    ∃ A B : Subgroup G,
      A≤(F.I₂ L).pCoreIn 2 ∧ B≤(F.I₂ L).pCoreIn 2 ∧ V≤A ∧ V≤B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A=16 ∧ Nat.card B=16 ∧ A⊓B=V ∧ A⊔B=(F.I₂ L).pCoreIn 2 ∧
      Nat.card ((F.I₂ L).pCoreIn 2)=64 ∧
      F.I₂ L⊔F.H.pCoreIn 2≤normalizer (A:Set G) ∧
      F.I₂ L⊔F.H.pCoreIn 2≤normalizer (B:Set G) := by
  let N : Subgroup G:=F.H.pCoreIn 2⊓centralizer (F.U:Set G)
  have hQT : F.H.pCoreIn 2≤(T:Subgroup G) := by
    have hTH : (T:Subgroup G)≤F.H := F.invariant 1
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change F.H.pCoreIn 2≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hNV : N≤normalizer (F.E g:Set G) := by
    rw [hE,←F.last]
    exact (inf_le_left.trans hQT).trans (F.invariant 2)
  have hNI : N≤normalizer (F.I₂ L:Set G) :=
    ((inf_le_left.trans hQT).trans (F.invariant 2)).trans
      ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hNC : N≤centralizer (F.W:Set G) :=
    inf_le_right.trans (centralizer_le (show F.W≤F.U from inf_le_left))
  have hc : Nat.card (F.E g)=4 := by
    rw [hE]
    simpa only [F.last,show (2:ℕ)^2=4 by decide] using F.card 2 le_rfl
  have hcentral : F.E g≤centralizer (((F.I₂ L).pCoreIn 2):Set G) := by
    intro v hv r hr
    exact ((hcore.ge hr).2 v (F.last.symm ▸ (hE ▸ hv))).symm
  have hsquare : ∀v∈F.E g,v^2=1 := fun v hv=>
    elemPow_eq_one_of_isElementaryAbelian (p:=2) v (hE ▸ hv)
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN⟩ :=
    d.exists_elementary_factors_of_fixed_normalizer σ (F.binaryCoreProjection L e) F.W hW hmark
      (by
        intro s
        obtain ⟨i,hi⟩:=QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L)) (e.symm s)
        exact ⟨i,by rw [F.binaryCoreProjection_apply,hi,e.apply_symm_apply]⟩)
      hfree hdim hgen hc hcentral hsquare N hNV hNI hNC
  have hQeq := core_eq_U_sup_centralizer F dg hZ dU
  have hineq : F.I₂ L⊔F.H.pCoreIn 2≤F.I₂ L⊔N := by
    rw [hQeq]
    exact sup_le le_sup_left
      (sup_le ((le_conjugateSpanBy F.U (F.P L)).trans le_sup_left) le_sup_right)
  rw [hE] at hVA hVB hi
  exact ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,
    hineq.trans hAN,hineq.trans hBN⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
