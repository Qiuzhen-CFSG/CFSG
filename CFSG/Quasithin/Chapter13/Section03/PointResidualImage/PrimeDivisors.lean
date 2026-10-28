module

public import Theory.GroupTheory.PResidual.PrimeSetPerfect
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.OrdinaryRecovery

/-!
# Prime divisors in the original ordinary point-action branch

The six-letter point stabilizer is a {2,3}-group. Hence the {2,3}-residual
of Y acts trivially on the natural module. Since the original ordinary
L-quotient has kernel O₂(L), its commutator with L lies in O₂(L). Relative
normality in H, characteristic two of H, and the original core-free join
now kill that residual. The final theorem combines this source calculation
with the genuine theta identity to obtain Y≤L.

This is the ordinary point-centralizing case of Aschbacher–Smith13.3.8(2)
and the recovery step of13.3.9, printed pp.886–887. No maximality,
component placement, or separate13.3.8 callback is assumed.
-/

public section
open Subgroup
open scoped commutatorElement
open BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Chapter13.Section08.TransvectionQuotients.FiveSeed
open Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

private theorem point_isTwoThree (P:Submodule (ZMod 2) NaturalGeometry.V)
    (hP:Module.finrank (ZMod 2) P=1) :
    IsPiGroup twoThreePrimes (subspaceStabilizer (naturalRepresentation (Fin 6)) P) := by
  let J:=subspaceStabilizer (naturalRepresentation (Fin 6)) P
  let T:Sylow 2 J:=Classical.choice inferInstance
  have hi:(T:Subgroup J).index=3 := by
    have hJ:(⊤:Subgroup S)⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P=J := inf_of_le_right le_top
    have hh:=point_sylow_index_three (⊤:Subgroup S) (by simp) P hP
    rw [hJ] at hh
    exact hh T
  obtain ⟨n,hn⟩:=T.isPGroup'.exists_card_eq
  have hc:Nat.card J=2^n*3 := by rw [←(T:Subgroup J).card_mul_index,hn,hi]
  rw [IsPiGroup_iff]
  intro p hd
  change p.val=2 ∨ p.val=3
  change p.val∣Nat.card J at hd
  rw [hc] at hd
  rcases p.property.dvd_mul.mp hd with hd|hd
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hd)).resolve_left p.property.ne_one)
  · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left p.property.ne_one)

/-- The ordinary point-action case of13.3.8(2), using the literal two-core-free
join and characteristic two of H instead of an unproved maximality premise. -/
theorem twoThree_of_natural_point {G:Type*} [Group G] [Finite G]
    (M L V H Y:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (hY:Y≤M⊓normalizer (V:Set G)) (hYH:Y≤H) (hnY:H≤normalizer (Y:Set G))
    (hQH:L.pCoreIn 2≤H) (hcore:pCore 2 (L⊔H:Subgroup G)=⊥)
    (hchar:centralizer (pCore 2 H:Set H)≤pCore 2 H)
    (w:Additive V) (hw:w≠0) (hc:Y≤centralizer ({(w.toMul:G)}:Set G)) :
    IsPiGroup twoThreePrimes Y := by
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
  have hpi:IsPiGroup twoThreePrimes a.range :=
    (point_isTwoThree line hline).of_injective (inclusion hstab) (inclusion_injective hstab)
  have hres:piResidual twoThreePrimes Y≤a.ker :=
    piResidual_le_ker_of_range twoThreePrimes a hpi
  let N:=(piResidual twoThreePrimes Y).map Y.subtype
  have hNP:N≤P:=(map_subtype_le _).trans hY
  have hNL:N≤normalizer (L:Set G):=hNP.trans hPL
  have hcl:⁅L,N⁆≤L := le_normalizer_iff_commutator_le_left.mp hNL
  have hfN (n:G) (hn:n∈N):f ⟨n,hNP hn⟩=1 := by
    obtain ⟨y,hy,rfl⟩:=hn
    exact hres hy
  apply twoThree_of_residual_commutator L H Y (L.pCoreIn 2) hYH hnY hQH
    (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ?_ hcore hchar
  apply commutator_le.mpr
  intro l hl n hn
  let x:L:=⟨⁅l,n⁆,hcl (commutator_mem_commutator hl hn)⟩
  have hfX:f (inclusion hLP x)=1 := by
    have hcoord:inclusion hLP x=⁅(⟨l,hLP hl⟩:P),(⟨n,hNP hn⟩:P)⁆ := Subtype.ext rfl
    rw [hcoord,map_commutatorElement,hfN n hn]
    simp
  have hxα:x∈α.ker := by
    apply Subtype.ext
    exact (hfL x).symm.trans hfX
  rw [action_kernel_eq_core L α hα eL] at hxα
  exact mem_map_of_mem L.subtype hxα
/-- Original ordinary source placement, with13.3.8's {2,3} assertion discharged
from the genuine generated-core and characteristic-two hypotheses. -/
theorem le_component_of_theta_and_core_free_join {G:Type*} [Group G] [Finite G]
    (M L V H Y:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (htheta:closure {x:G|x∈M ∧ orderOf x=3}=L) (hp:IsPPerfect 2 Y)
    (hY:Y≤M⊓normalizer (V:Set G)) (hYH:Y≤H) (hnY:H≤normalizer (Y:Set G))
    (hQH:L.pCoreIn 2≤H) (hcore:pCore 2 (L⊔H:Subgroup G)=⊥)
    (hchar:centralizer (pCore 2 H:Set H)≤pCore 2 H)
    (w:Additive V) (hw:w≠0) (hc:Y≤centralizer ({(w.toMul:G)}:Set G)) :
    Y≤L := by
  have h23:=twoThree_of_natural_point M L V H Y hLP hPL α hα eL e he
    hY hYH hnY hQH hcore hchar w hw hc
  exact le_component_of_theta_natural_point M L V Y hLP hPL α hα eL e he
    htheta hY hp h23 w hw hc
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
