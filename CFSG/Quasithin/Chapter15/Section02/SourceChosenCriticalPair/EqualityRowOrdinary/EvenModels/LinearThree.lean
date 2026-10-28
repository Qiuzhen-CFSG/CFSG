module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.LinearThree
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.LinearThree

/-!
# Direct LinearThree ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.LinearThree. The original residual input and literal
marked Sylow supply its geometric hypotheses without a partner residual identity.
The deliberate private import keeps those existing model lemmas internal.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
variable (hcard : Nat.card (centralInvolutions T) = 2)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include r hcard

/-- The ordinary nonbinary PSL₃ central quotient is impossible, retaining all central two-covers. -/
theorem not_linear_three_quotient_component
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (c.component ⧸ pCore 2 c.component) 3 (2^n))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hai := marked_component_twoCentral r hcard c hI.1 hP hz hzne a ha hi
  obtain ⟨t,ht,_,hact⟩ := quotient_twoCentral_of_inner c e a hai
  obtain ⟨_,ho,Q,hQ⟩ := hai
  have hQfix : (Q : Subgroup c.component) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hQ ⟨x,hx⟩)
  let q : c.component →* PSL(3,F) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hk : q.ker = pCore 2 c.component := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let C := centralizer ({t} : Set PSL(3,F))
  have hqC (x : a.fixedSubgroup) : q x ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := hact x
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let f : a.fixedSubgroup →* C := (q.comp a.fixedSubgroup.subtype).codRestrict C hqC
  have hfker : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 c.component).comap a.fixedSubgroup.subtype := by
      ext x
      change (⟨q x,hqC x⟩ : C)=1 ↔ _
      rw [Subtype.ext_iff]
      change q x=1 ↔ _
      exact show x.val ∈ q.ker ↔ x.val ∈ pCore 2 c.component from hk ▸ Iff.rfl
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ a.fixedSubgroup.subtype_injective
  have hnorm := Sylow.normal_of_pGroup_kernel_of_core_index f hfker
    (linear_three_involution_core_odd hn hF t ht).not_two_dvd_nat (Q.subtype hQfix)
  have hnfix : a.fixedSubgroup ≤ normalizer (Q : Set c.component) :=
    (normal_subgroupOf_iff_le_normalizer hQfix).mp hnorm
  have hfix := marked_component_borel_fixed r hcard c hI hP hz hzne a ha
    ⟨hi,ho,Q,hQ⟩ Q hQfix hnfix
  let : IsQuasisimple c.component := c.isComponent.2
  let eZ := (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  have ha1 := Matrix.PSL3.OrdinaryBorel.cover_normalizer_fixer (by omega : 1<n) hF eZ Q a hfix
  rw [ha1,orderOf_one] at ho
  omega

/-- The simple nonbinary PSL₃ rows are excluded on the same marked component. -/
theorem not_even_linear_three_component
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL c.component 3 (2^n))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  let := hs
  let : IsQuasisimple c.component := c.isComponent.2
  have hc : pCore 2 c.component = ⊥ := c.center_eq.symm.trans center_eq_bot_of_simple_perfect
  let e : (c.component ⧸ pCore 2 c.component) ≃* c.component :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact not_linear_three_quotient_component r hcard c hI hP hz hzne a ha hn (hm.of_mulEquiv e) hi
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
