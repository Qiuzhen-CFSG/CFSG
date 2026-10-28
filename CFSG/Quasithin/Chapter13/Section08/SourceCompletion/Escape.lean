module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalPair

/-!
# Choosing an original member of Hz

The universal 12.2.13 theorem applies to the unchanged chosen Irr⁺ module.
The actual global exclusions eliminate all its model alternatives. Natural
A₆ transitivity transports the escaping centralizer to the original flag
line, so G₁ is not contained in M. The order-two normal line places G₁ in
the genuine local family, proving G₁ ∈ Hz and hence Hz is nonempty.

The literal Hypothesis1223 input is the earlier 13.3.2(4) consequence; its
source proof uses 13.1.7 and 13.1.2(5). It is not replaced by an escape or
local-family assumption. Source: 12.2.13, 13.3.2(4), and the opening of
13.8 on printed p.946.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁:Subgroup G}

namespace NaturalSetup
variable (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem exists_escaping_vector (h1223:Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier:Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ∃v∈V,v≠1 ∧ ¬centralizer ({v}:Set G)≤M := by
  rw [d.local_normalizer]
  rcases earlier G T L V h1223 d.chosen with
    hv | ⟨n,hn,_,he⟩ | ⟨_,he⟩ | ⟨_,he⟩
  · exact hv
  · exact (d.counterexample.no_linear (n+1) (by rcases hn with rfl|rfl <;> omega) he).elim
  · exact (d.counterexample.no_alternating_nine he).elim
  · exact (d.counterexample.no_sporadic .m24 (by simp) he).elim

theorem vector_centralizer_escape (h1223:Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier:Theorem12213 KnownSimple.IsKnownSimple.{u}) {x:G} (hx:x∈V) (hx1:x≠1) :
    ¬centralizer ({x}:Set G)≤M := by
  obtain ⟨v,hv,hv1,hescape⟩:=d.exists_escaping_vector h1223 earlier
  obtain ⟨l,hl,he⟩:=Section07.natural_nonzero_transitive d hx hv hx1 hv1
  intro hc
  apply hescape
  intro y hy
  have hyc : l⁻¹*y*l∈centralizer ({x}:Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hyv:=mem_centralizer_singleton_iff.mp hy
    rw [←he] at hyv
    have hh:=congrArg (fun a:G=>l⁻¹*a*l) hyv
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh
  have hlM:l∈M:=d.local_normalizer ▸ L.le_normalizer hl
  have hyM:=M.mul_mem (M.mul_mem hlM (hc hyc)) (M.inv_mem hlM)
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hyM

theorem first_normalizer_escape (h1223:Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier:Theorem12213 KnownSimple.IsKnownSimple.{u}) : ¬G₁≤M := by
  obtain ⟨z,hz,_⟩:=(Nat.card_eq_two_iff' (1:V₁)).mp d.line_card
  have hz1:(z:G)≠1:=fun he=>hz (Subtype.ext he)
  have hp:V₁=zpowers (z:G) := by
    let : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
    have he:=zpowers_eq_top_of_prime_card d.line_card hz
    have hm:=congrArg (map V₁.subtype) he
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using hm.symm
  intro hGM
  apply d.vector_centralizer_escape h1223 earlier
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) z.property) hz1
  apply le_trans _ hGM
  rw [d.first_normalizer]
  have hh:=normalizer_zpowers_eq_centralizer_of_order_two (z:G)
    (show orderOf (z:G)=2 from (Nat.card_zpowers (z:G)).symm.trans ((congrArg (fun A:Subgroup G=>Nat.card A) hp).symm.trans d.line_card))
  exact hh.symm.le.trans (congrArg (fun A:Subgroup G=>normalizer (A:Set G)) hp).symm.le

theorem first_mem_Hz (h1223:Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier:Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    G₁∈Source.Hz (sourceOne L T V₁) (T:Subgroup G) G₁ M := by
  have hline:V₁≤G₁:=d.first_normalizer ▸ V₁.le_normalizer
  let : IsElementaryAbelian 2 V:=d.chosen.elementary
  let : IsElementaryAbelian 2 V₁:=IsElementaryAbelian.of_le
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  have hcore:V₁≤G₁.pCoreIn 2:=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V₁) hline
      (d.first_normalizer ▸ le_rfl)
  have hne:G₁.pCoreIn 2≠⊥ := by
    intro he
    have hz:V₁=⊥:=bot_unique (he ▸ hcore)
    have hc:=d.line_card
    rw [hz] at hc
    simp at hc
  have hLG:sourceOne L T V₁≤G₁:=by
    rw [d.first_normalizer]
    exact (ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.one_le _ _ _).trans inf_le_right
  exact ⟨⟨hne,sup_le hLG (d.first_normalizer ▸ d.line_stable)⟩,le_rfl,
    d.first_normalizer_escape h1223 earlier⟩

/-- Source opening with a genuine chosen local subgroup and critical pair.
The two uniform inputs are the earlier 13.5.7 applicability and 13.7.8 span. -/
theorem source_critical_pair
    (h1223:Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (earlier:Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:∀H∈Source.Hz (sourceOne L T V₁) (T:Subgroup G) G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ∃H∈Source.Hz (sourceOne L T V₁) (T:Subgroup G) G₁ M,
      ∃c:CriticalGeometry.CriticalPair L (T:Subgroup G) H V,
        3≤c.path.length ∧ Odd c.path.length := by
  have hH:=d.first_mem_Hz h1223 earlier
  exact ⟨G₁,hH,d.exists_criticalPair hspan (hF9 G₁ hH)⟩
end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
