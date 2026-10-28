module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedOmegaContainment
public import Theory.GroupTheory.IrreducibleResidualSaturation
public import Theory.GroupTheory.OmegaCoreSandwich

/-!
# The paired irreducible-section argument identifies the local two-core

The original local hypotheses place E in the preimage F of the omega-center
of the quotient two-core. Its conjugate escapes A because E has larger
order than A ∩ Aᵃ. Irreducibility of C/A for B = I ∩ Mc therefore puts
[C,K] in F. The ordinary and modulo centralizer bounds then identify
O₂(Mc) with that commutator subgroup.

This assembles steps (k)--(n) using the actual quotient by Ω₁Z(O₂(Mc)).
The geometric premises are supplied by the paired block modules: the
Thompson/radical comparison supplies Q₁ ≤ C and S normal in T, the paired
Borel action supplies the two irreducible sections and their center bound,
and the point-core geometry supplies the commutator and centralizer identities.
The acting group on C/A is I ∩ Mc = Kz TI, with TI = T ∩ I.

Source: Aschbacher--Smith, proof of 14.6.9(k)--(n), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] omegaCore_normal

/-- The paired irreducible sections and their ordinary and modulo centralizers
identify the actual local two-core. -/
theorem source_omegaCore_eq_of_paired_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (S B A C K E N Z₀ : Subgroup H)
    (hST : S ≤ (T.subtype hH.2 : Subgroup H))
    (hSnormal : (S.subgroupOf (T.subtype hH.2 : Subgroup H)).Normal)
    (hCS : C ≤ S) (hQC : pCore 2 H ≤ C) (hEA : E ≤ A)
    (hZ₀Z : Z₀ ≤ omegaOneCenterAmbient (pCore 2 H))
    [(Z₀.subgroupOf S).Normal]
    (hBE : B ≤ normalizer (E : Set H))
    (hirrE : IsIrreducibleSection B Z₀ E)
    (hcenter : ((center (S ⧸ Z₀.subgroupOf S)).comap
      (QuotientGroup.mk' (Z₀.subgroupOf S))).map S.subtype ≤ E)
    (hBA : B ≤ normalizer (A : Set H))
    (hBC : B ≤ normalizer (C : Set H))
    (hirrC : IsIrreducibleSection B A C)
    (hsmall : ⁅A,K⁆ ≤ E) (hcomm : ⁅C,K⁆ = N)
    (a : H)
    (hcard : Nat.card (A ⊓ A.map (MulAut.conj a).toMonoidHom : Subgroup H) < Nat.card E)
    (hcent : C ⊓ centralizer (N : Set H) ≤ Z₀)
    (hmod : ∀ c ∈ C, (∀ n ∈ N, ⁅n,c⁆ ∈ Z₀) → c ∈ N) :
    pCore 2 H = N := by
  let Q := pCore 2 H
  let Z := omegaOneCenterAmbient Q
  let q := QuotientGroup.mk' Z
  let F := (omegaOneCenterAmbient (pCore 2 (H ⧸ Z))).comap q
  have hZQ : Z ≤ Q := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hEF : E ≤ F := source_omegaCore_quotient_contains_irreducible_section
    hG T hempty hH hHZ S B E Z₀ hST hSnormal (hEA.trans (hirrC.1.trans hCS))
    (hZQ.trans (hQC.trans hCS)) hZ₀Z hBE hirrE hcenter
  obtain ⟨_,himage,_⟩ := source_omegaCore_quotient_characteristicTwo hG T hempty hH hHZ
  have hFQ : F ≤ Q := by
    change (omegaOneCenterAmbient (pCore 2 (H ⧸ Z))).comap q ≤ Q
    rw [himage]
    exact (omega_center_preimage_le_and_commutator_le Q Z hZQ).1
  have hFmap : F.map (MulAut.conj a).toMonoidHom = F :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top a))
  have hNF : N ≤ F := by
    rw [←hcomm]
    exact commutator_le_normal_of_irreducible_conjugate B A C K E F hBA hBC hirrC
      (hsmall.trans hEF) hEA hEF a
      ((map_mono hEF).trans (hFmap.le.trans (hFQ.trans hQC))) hcard
  apply eq_of_omega_center_preimage_centralizer_bounds Q C N Z₀ hQC _ hcent hmod
  change N ≤ (omegaOneCenterAmbient (Q.map q)).comap q
  change N ≤ (omegaOneCenterAmbient (pCore 2 (H ⧸ Z))).comap q at hNF
  rw [himage] at hNF
  exact hNF
end CFSG.Quasithin.Chapter14.Section06
