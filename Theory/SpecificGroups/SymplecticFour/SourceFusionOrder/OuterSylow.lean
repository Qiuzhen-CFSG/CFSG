module
public import Theory.SpecificGroups.SymplecticFour.NormalSylowActors
public import Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension

/-!
# Outer involutions in symplectic flag extensions

The inner part of a two-subgroup centralizing an outer diagram-preserving
involution embeds in its actual fixed group. Field descent bounds its order
by q². This retains the original automorphism and the whole two-subgroup.

If a flag overgroup contains the full inner Borel and a noninner element
of two-power order, its inner-field decomposition has its inner factor in
that Borel. Removing this factor puts the field automorphism in the same
overgroup; its half-order power is an actual field involution. No splitting
of an arbitrary Sylow extension is assumed, and q=4 is included.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, printed pp.289,293–294
of `refs/quasithin.pdf`. The Chapter 6 consumer transports these results
through the original common normalizer; ambient Sylow placement is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The inner two-part centralizing an outer diagram-preserving involution has order at most q². -/
theorem inner_outer_centralizer_card {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : PreservesDiagram a)
    (hi : a ∉ MulAut.innerSubgroup (Sp F))
    (V : Subgroup (MulAut (Sp F))) (hp : IsPGroup 2 V)
    (hVi : V ≤ MulAut.innerSubgroup (Sp F))
    (hVc : V ≤ centralizer ({a} : Set (MulAut (Sp F)))) :
    Nat.card V ≤ Nat.card F^2 := by
  let e : Sp F ≃* MulAut.innerSubgroup (Sp F) := MonoidHom.ofInjective inner_injective
  let k : V →* Sp F := e.symm.toMonoidHom.comp (inclusion hVi)
  have hk (x : V) : MulAut.conj (k x) = x.val :=
    congrArg Subtype.val (e.apply_symm_apply (inclusion hVi x))
  let f : V →* a.fixedSubgroup := k.codRestrict _ (fun x => by
    rw [MulAut.mem_fixedSubgroup]
    apply inner_injective
    have heq : a * MulAut.conj (k x) * a⁻¹ = MulAut.conj (a (k x)) := by
      ext y
      simp
    rw [←heq,hk]
    have hh := mem_centralizer_singleton_iff.mp (hVc x.property)
    rw [←hh,mul_assoc,mul_inv_cancel,mul_one])
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    have hh' := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) hh
    exact (hk x).symm.trans (hh'.trans (hk y))
  have hb := NormalSylowActors.outer_fixed_two_subgroup_card (by omega) hF a hao ha hi f.range
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hb
  simpa only [hF,←pow_mul,Nat.mul_comm n 2] using hb
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A flag overgroup containing the inner Borel contains the field involution of each nontrivial two-power field part. -/
theorem flag_overgroup_field_involution {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (V : Subgroup (MulAut (Sp F)))
    (hB : (borel (F := F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ V)
    (a : MulAut (Sp F)) (haV : a ∈ V) (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) (hp : ∃ k : ℕ, orderOf a = 2^k) :
    ∃ τ : F ≃+* F, orderOf τ=2 ∧ fieldAutomorphism τ ∈ V := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  obtain ⟨g,σ,he⟩ := SemilinearClassification.inner_field_of_preservesDiagram a
    (SourceNormalizerExtension.flag_preservesDiagram ⟨a,ha⟩)
  have hgflag : MulAut.conj g ∈ SourceNormalizerExtension.flagAutomorphisms F := by
    have hfield : fieldAutomorphism σ ∈ SourceNormalizerExtension.flagAutomorphisms F :=
      ⟨field_map_pointParabolic σ,field_map_planeParabolic σ⟩
    have hh := (SourceNormalizerExtension.flagAutomorphisms F).mul_mem ha
      ((SourceNormalizerExtension.flagAutomorphisms F).inv_mem hfield)
    rwa [he,mul_inv_cancel_right] at hh
  have hgB : g ∈ borel := (SourceNormalizerExtension.inner_flag_iff hF hn g).mp hgflag
  have hσV : fieldAutomorphism σ ∈ V := by
    have hh := V.mul_mem (V.inv_mem (hB (mem_map_of_mem _ hgB))) haV
    rwa [he,inv_mul_cancel_left] at hh
  have hσne : σ ≠ 1 := by
    intro hh
    apply hi
    rw [he,hh]
    change MulAut.conj g * fieldAutomorphismHom 1 ∈ _
    rw [map_one,mul_one]
    exact ⟨g,rfl⟩
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) := QuotientGroup.mk' _
  have hπ : π a = outerFieldHom σ := by
    rw [he,map_mul]
    have hg : π (MulAut.conj g)=1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [hg,one_mul]
    rfl
  have hσp : ∃ k, orderOf σ=2^k := by
    obtain ⟨k,hk⟩ := hp
    have hd : orderOf σ ∣ 2^k := by
      rw [←orderOf_injective (outerFieldHom (F := F)) outerFieldHom_injective,←hπ,←hk]
      exact orderOf_map_dvd π a
    obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
    exact ⟨j,hj⟩
  have hd : 2 ∣ orderOf σ := by
    obtain ⟨k,hk⟩ := hσp
    have hkpos : 0<k := by
      by_contra hh
      have hk0 : k=0 := by omega
      rw [hk0,pow_zero,orderOf_eq_one_iff] at hk
      exact hσne hk
    rw [hk]
    exact dvd_pow_self 2 (by omega : k≠0)
  refine ⟨σ^(orderOf σ/2),orderOf_pow_orderOf_div (orderOf_pos σ).ne' hd,?_⟩
  change fieldAutomorphismHom (σ^(orderOf σ/2)) ∈ V
  rw [map_pow]
  exact V.pow_mem hσV _
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
