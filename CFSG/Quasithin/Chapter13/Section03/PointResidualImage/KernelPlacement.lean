module
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Coordinates
public import Theory.GroupTheory.PResidual.CubicGeneration
/-!
# Component placement from theta and a two-group point-action kernel

A subgroup fixing a nonzero natural A₆ vector acts through a point stabilizer
whose Sylow two-subgroup has index three. If its actual action kernel is a
two-group, its order divides 2^n·3. Two-perfectness and the existing cubic
generation theorem place it inside the original cubic theta subgroup of M.
This works for the covered component without assuming its action kernel is
O₂(L); that mistaken ordinary-only identification is avoided.

Source: Aschbacher--Smith13.3.9, p.887, following12.2.6/8 and13.3.7.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
theorem le_component_of_theta_point_two_kernel {G:Type*} [Group G] [Finite G]
    (M L V Y:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (htheta:closure {x:G|x∈M ∧ orderOf x=3}=L)
    (hY:Y≤M⊓normalizer (V:Set G)) (hp:IsPPerfect 2 Y)
    (hk:IsPGroup 2 (Y ⊓ centralizer (V:Set G) : Subgroup G))
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
  have hka : IsPGroup 2 a.ker := by
    let j : a.ker →* (Y ⊓ centralizer (V:Set G) : Subgroup G) :=
      (Y.subtype.comp a.ker.subtype).codRestrict _ (fun x => by
        refine ⟨x.val.property,?_⟩
        have hx : inclusion hY x.val ∈ f.ker := x.property
        rw [hker] at hx
        exact hx)
    apply hk.of_injective j
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (Y ⊓ centralizer (V:Set G) : Subgroup G) => z.val) hh
  let P₁ := subspaceStabilizer (naturalRepresentation (Fin 6)) line
  let S₁ : Sylow 2 P₁ := Classical.choice inferInstance
  have hi : (S₁ : Subgroup P₁).index = 3 := by
    have hh := point_sylow_index_three (⊤:Subgroup S) (by simp) line hline
    rw [top_inf_eq] at hh
    exact hh S₁
  obtain ⟨m,hm⟩ := S₁.isPGroup'.exists_card_eq
  obtain ⟨n,hn⟩ := hka.exists_card_eq
  have hP : Nat.card P₁ = 2^m*3 := by rw [←(S₁:Subgroup P₁).card_mul_index,hm,hi]
  have hd : Nat.card Y ∣ 2^(n+m)*3 := by
    have him : Nat.card a.range ∣ 2^m*3 := hP ▸ card_dvd_of_le hstab
    have hh := a.ker.card_mul_index
    rw [index_ker,hn] at hh
    rw [←hh,pow_add,mul_assoc]
    exact Nat.mul_dvd_mul_left _ him
  have h23 : IsPiGroup twoThreePrimes Y := by
    rw [IsPiGroup_iff]
    intro p hp
    change p.val = 2 ∨ p.val = 3
    have hp' : p.val ∣ 2^(n+m)*3 := hp.trans hd
    rcases p.property.dvd_mul.mp hp' with hp' | hp'
    · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hp')).resolve_left p.property.ne_one)
    · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hp').resolve_left p.property.ne_one)
  have h9 : ¬9 ∣ Nat.card Y := by
    intro h9
    have hh : 9 ∣ 2^(n+m)*3 := h9.trans hd
    have hcop : Nat.Coprime 9 (2^(n+m)) := (by decide : Nat.Coprime 9 2).pow_right _
    exact (by decide : ¬9∣3) (hcop.dvd_mul_left.mp hh)
  have hgen := Subgroup.cubic_closure_eq_top_of_twoPerfect h23 hp h9
  have hm := congrArg (Subgroup.map Y.subtype) hgen
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [←hm,←htheta]
  apply Subgroup.closure_mono
  rintro x ⟨y,hy,rfl⟩
  exact ⟨(hY y.property).1,(Y.orderOf_coe y).trans hy⟩
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
