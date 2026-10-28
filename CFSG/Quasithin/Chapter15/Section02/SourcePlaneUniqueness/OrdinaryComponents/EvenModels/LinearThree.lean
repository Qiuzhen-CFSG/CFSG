module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Borel
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank
public import Theory.SpecificGroups.PSL3.CentralCoverBorelGeometry
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.GroupTheory.SylowNormalKernel

/-!
# Exclusion of nonbinary PSL₃ and its central two-covers

The marked involution descends to an inner projective involution. Its
centralizer has normal Sylow two-subgroup. Pull this back to the actual
fixed subgroup through its two-group kernel; no surjectivity of the
fixed-subgroup map is assumed. The maximal-intersection argument forces
pointwise fixation of the component Borel, contradicting the concrete
central-cover Borel fixer theorem. This also covers the permitted
PSL₃(4) central two-covers.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels

private theorem linear_three_involution_core_odd
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2^n) (t : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (ht : orderOf t=2) :
    Odd (pCore 2 (centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)))).index := by
  let e := Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv F hn hF t
    (by intro he; simp [he] at ht) (ht ▸ pow_orderOf_eq_one t)
  have hidx : (pCore 2 (centralizer ({t} : Set PSL(3,F)))).index =
      (pCore 2 (Matrix.PSL3.EvenInnerCentralizers.centralizer F)).index := by
    calc
      _ = ((pCore 2 (centralizer ({t} : Set PSL(3,F)))).map e.toMonoidHom).index :=
        (index_map_equiv _ e).symm
      _ = _ := congrArg Subgroup.index (pCore_map_iso 2 e)
  rw [hidx,
    Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants.twoCore_eq_unipotent F hF (by omega),
    (Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants.torus_complement F hF (by omega)).index_eq_card]
  exact (Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants.units_odd F hF (by omega)).of_dvd_nat
    (card_range_dvd (Matrix.PSL3.EvenInnerCentralizers.torus F))

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- The ordinary nonbinary PSL₃ central quotient is impossible, retaining all central two-covers. -/
theorem not_linear_three_quotient_component
    (hI : MinimalPlaneEscape Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (c.component ⧸ pCore 2 c.component) 3 (2^n))
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hai := marked_component_twoCentral d c hI.1 hP hz hzne a ha hi
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
  have hfix := marked_component_borel_fixed d c hI hz hzne a ha
    ⟨hi,ho,Q,hQ⟩ Q hQfix hnfix
  let : IsQuasisimple c.component := c.isComponent.2
  let eZ := (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  have ha1 := Matrix.PSL3.OrdinaryBorel.cover_normalizer_fixer (by omega : 1<n) hF eZ Q a hfix
  rw [ha1,orderOf_one] at ho
  omega

/-- The simple nonbinary PSL₃ rows are excluded on the same marked component. -/
theorem not_even_linear_three_component
    (hI : MinimalPlaneEscape Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
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
  exact not_linear_three_quotient_component d c hI hP hz hzne a ha hn (hm.of_mulEquiv e) hi
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
