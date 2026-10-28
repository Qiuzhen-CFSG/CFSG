module

public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Coordinates
public import Theory.GroupTheory.PResidual.CubicGeneration

/-!
# Recovering the ordinary component from its point action

Let Y be two-perfect with prime divisors two and three, and suppose it fixes
a nonzero point of the original natural A₆ module. The point stabilizer has
three-part of order three. The genuine theta identity places every cubic
element of the action kernel in L, where the ordinary quotient identifies
the kernel with the two-core. Thus the kernel is three-free, nine does not
divide |Y|, and cubic generation gives Y≤L.

The theta identity, normalization of V, and the {2,3} assertion remain the
actual earlier source inputs 12.2.6/8 and 13.3.8(2). No component-placement
or module-classification conclusion is used as an input.
Source: Aschbacher–Smith 13.3.9, printed p.887, ordinary A₆ branch.
-/

public section
open Subgroup
open BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Chapter13.Section08.TransvectionQuotients.FiveSeed
open Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

private theorem point_nine_not_dvd (P:Submodule (ZMod 2) NaturalGeometry.V)
    (hP:Module.finrank (ZMod 2) P=1) (A:Subgroup S)
    (hA:A≤subspaceStabilizer (naturalRepresentation (Fin 6)) P) : ¬9∣Nat.card A := by
  let J:=subspaceStabilizer (naturalRepresentation (Fin 6)) P
  let T:Sylow 2 J:=Classical.choice inferInstance
  have hi:(T:Subgroup J).index=3 := by
    have hJ:(⊤:Subgroup S)⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P=J := inf_of_le_right le_top
    have hh:=point_sylow_index_three (⊤:Subgroup S) (by simp) P hP
    rw [hJ] at hh
    exact hh T
  obtain ⟨n,hn⟩:=T.isPGroup'.exists_card_eq
  have hc:Nat.card J=2^n*3 := by rw [←(T:Subgroup J).card_mul_index,hn,hi]
  intro hd
  have hd':9∣2^n*3 := hc ▸ hd.trans (card_dvd_of_le hA)
  have hcop:Nat.Coprime 9 (2^n):=(by decide:Nat.Coprime 9 2).pow_right n
  exact (by decide:¬9∣3) (hcop.dvd_mul_left.mp hd')

/-- The ordinary quotient and the genuine cubic theta identity place Y in L.
The {2,3} assertion is the preceding ambient source lemma13.3.8(2). -/
theorem le_component_of_theta_natural_point {G:Type*} [Group G] [Finite G]
    (M L V Y:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (htheta:closure {x:G|x∈M ∧ orderOf x=3}=L)
    (hY:Y≤M⊓normalizer (V:Set G)) (hp:IsPPerfect 2 Y)
    (h23:IsPiGroup twoThreePrimes Y)
    (w:Additive V) (hw:w≠0) (hc:Y≤centralizer ({(w.toMul:G)}:Set G)) : Y≤L := by
  let P:=M⊓normalizer (V:Set G)
  obtain ⟨f,hfL,hact,hker⟩:=natural_extension P L V hLP hPL inf_le_right α hα e he
  let a:Y→*S:=f.comp (inclusion hY)
  let line:=Submodule.span (ZMod 2) {e w}
  have hew:e w≠0 := by
    intro hh
    exact hw (e.injective (hh.trans e.map_zero.symm))
  have hline:Module.finrank (ZMod 2) line=1:=finrank_span_singleton hew
  have hstab:a.range≤subspaceStabilizer (naturalRepresentation (Fin 6)) line := by
    apply le_subspaceStabilizer
    rintro _ ⟨y,rfl⟩ v hv
    obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp hv
    have hfix:conjugationRepresentation P V inf_le_right (inclusion hY y) w=w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (y:G)*(w.toMul:G)*(y:G)⁻¹=(w.toMul:G)
      have hh:=mem_centralizer_singleton_iff.mp (hc y.property)
      rw [hh,mul_inv_cancel_right]
    have hf:naturalRepresentation (Fin 6) (a y) (e w)=e w := by
      change naturalRepresentation (Fin 6) (f (inclusion hY y)) (e w)=e w
      rw [←hact,hfix]
    simpa only [map_smul,hf] using Submodule.smul_mem line c
      (Submodule.mem_span_singleton_self (e w))
  have h9im:¬9∣Nat.card a.range := point_nine_not_dvd line hline a.range hstab
  have h3ker:¬3∣Nat.card a.ker := by
    intro hd
    obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' 3 hd
    have hxG:orderOf (x.val.val:G)=3 := by
      rw [Y.orderOf_coe,a.ker.orderOf_coe]
      exact hx
    have hxL:(x.val.val:G)∈L := htheta ▸ subset_closure ⟨(hY x.val.property).1,hxG⟩
    let l:L:=⟨x.val.val,hxL⟩
    have hlker:l∈α.ker := by
      apply Subtype.ext
      have hh:=hfL l
      have hpEq:inclusion hLP l=inclusion hY x.val := Subtype.ext rfl
      rw [hpEq] at hh
      exact hh.symm.trans x.property
    rw [action_kernel_eq_core L α hα eL] at hlker
    have hcop:Nat.Coprime (orderOf (⟨l,hlker⟩:pCore 2 L)) 3 :=
      (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime (by decide) _
    have ho:orderOf (⟨l,hlker⟩:pCore 2 L)=3 := by
      rw [←(pCore 2 L).orderOf_coe,←L.orderOf_coe]
      exact hxG
    rw [ho] at hcop
    exact (by decide:¬Nat.Coprime 3 3) hcop
  have h9:¬9∣Nat.card Y := by
    intro hd
    have hh:=a.ker.card_mul_index
    rw [index_ker] at hh
    have hcop:Nat.Coprime 9 (Nat.card a.ker) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3ker).pow_left 2
    exact h9im (hcop.dvd_mul_left.mp (hh.symm ▸ hd))
  have hgen:=Subgroup.cubic_closure_eq_top_of_twoPerfect h23 hp h9
  have hm:=congrArg (Subgroup.map Y.subtype) hgen
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [←hm,←htheta]
  apply Subgroup.closure_mono
  rintro x ⟨y,hy,rfl⟩
  exact ⟨(hY y.property).1,(Y.orderOf_coe y).trans hy⟩
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
