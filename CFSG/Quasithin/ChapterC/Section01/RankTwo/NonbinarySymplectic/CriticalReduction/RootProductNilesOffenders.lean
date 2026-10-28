module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesPair
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalLower
public import Glauberman.MaximumAbelianReplacement
public import Glauberman.PushingUpQuadraticOffender
public import Glauberman.MaximumAbelianKernelIntersection

/-!
# Sharp original-degree offenders for the same Niles group

The actual identity O₂(F₀)=F₀ intersect Q-alpha makes every outside actor
move the full U-alpha by index at least q. Since that entire layer lies in
Ω₁Z(O₂(F₀)), the same lower bound holds on the literal core omega. Maximal
abelian order gives the reverse bound q. Every outside maximum abelian
subgroup therefore supplements the core and has a maximum replacement
inside it, preserving the complete maximum abelian family. The original
characteristic-normal exclusion supplies an actual quadratic offender.

Source: Niles (1979), Lemma 2.9 through assertion (4), and Lemma 7.4,
printed pp.33,60–61, applied to F₀ in MS93 (5.1), printed p.913. The
invariant-kernel maximum-intersection selection of Lemma 7.5 follows for
the same group and every original Sylow automorphism. The subsequent
pushing-up structure and commutator conclusion remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The unchanged original F₀ has sharp maximum-abelian replacement and an
actual quadratic offender at every original nonbinary degree. -/
theorem Input.replacement_root_product_F0_niles_offenders
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t) ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ ∧
          NoCharacteristicNormal (P : Subgroup C) ∧
          (pCore 2 C).map C.subtype = C ⊓ Q d.radical a ∧
          U d.radical a ≤ C ∧
          (U d.radical a).subgroupOf C ≤ omegaCenterIn (pCore 2 C) ∧
          Nonempty ((P ⧸ (pCore 2 C).subgroupOf (P : Subgroup C)) ≃* Multiplicative E.Carrier) ∧
          (pCore 2 C).relIndex (P : Subgroup C) = Nat.card F ∧
          (∀ A : Subgroup C, ¬ A ≤ pCore 2 C →
            Nat.card F ≤ (centralizer (A : Set C)).relIndex (omegaCenterIn (pCore 2 C))) ∧
          (∀ A : Subgroup C, A ∈ thompsonAbelianSubgroups (P : Subgroup C) →
            ¬ A ≤ pCore 2 C →
            A ⊔ pCore 2 C = (P : Subgroup C) ∧
            (A ⊓ pCore 2 C) ⊔ omegaCenterIn (pCore 2 C) ∈ thompsonAbelianSubgroups (P : Subgroup C) ∧
            (A ⊓ pCore 2 C) ⊔ omegaCenterIn (pCore 2 C) ∈ thompsonAbelianSubgroups (pCore 2 C) ∧
            Nat.card ((A ⊓ pCore 2 C) ⊔ omegaCenterIn (pCore 2 C) : Subgroup C) = Nat.card A ∧
            (A ⊓ omegaCenterIn (pCore 2 C)).relIndex (omegaCenterIn (pCore 2 C)) = Nat.card F ∧
            thompsonAbelianSubgroups (pCore 2 C) ⊆ thompsonAbelianSubgroups (P : Subgroup C)) ∧
          (∃ A : Subgroup C, A ∈ thompsonAbelianSubgroups (P : Subgroup C) ∧
            ¬ A ≤ pCore 2 C ∧ ⁅⁅omegaCenterIn (pCore 2 C),A⁆,A⁆ = ⊥ ∧
            (centralizer (A : Set C)).relIndex (omegaCenterIn (pCore 2 C)) = Nat.card F) ∧
          (∀ α : MulAut P,
            omegaCenterIn (pCore 2 C) ≤
              (NilesRankOneKernel.invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype →
            ∃ A : Subgroup C, A ∈ thompsonAbelianSubgroups (P : Subgroup C) ∧
              ¬ A ≤ pCore 2 C ∧
              A ⊓ pCore 2 C = A ⊓
                (NilesRankOneKernel.invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype) ∧
          ∃ x : C, x ∈ pResidual 2 C ∧
            (P : Subgroup C) ⊔ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = ⊤ ∧
            (P : Subgroup C) ⊓ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = pCore 2 C := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hpair⟩ :=
    h.replacement_root_product_F0_niles_pair d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hCa := hCI.trans hI
  have hq : 4 ≤ Nat.card F := by
    rw [h.field_card]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h.nonbinary
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion hCa) (inclusion_injective hCa)
  let Ω := omegaCenterIn (pCore 2 C)
  have hlower (A : Subgroup C) (hout : ¬ A ≤ pCore 2 C) :
      Nat.card F ≤ (centralizer (A : Set C)).relIndex Ω := by
    have hAQ : ¬ A.map C.subtype ≤ Q d.radical a := by
      intro hh
      apply hout
      apply (map_le_map_iff_of_injective C.subtype_injective).mp
      rw [hcore]
      exact le_inf (map_subtype_le _) hh
    have hlow := h.replacement_natural_fixed_index_lower d geometry hb ha
      (A.map C.subtype) ((map_subtype_le _).trans hCa) hAQ
    have htransport := Subgroup.SmallMover.centralizer_index_map C.subtype C.subtype_injective
      ((U d.radical a).subgroupOf C) A
    rw [map_subgroupOf_eq_of_le hUC] at htransport
    rw [htransport] at hlow
    exact hlow.trans ((centralizer (A : Set C)).relIndex_le_of_le_right hUomega
      index_ne_zero_of_finite)
  have hQS : pCore 2 C ≤ (P : Subgroup C) := pCore_isPGroup.le_sylow_of_normal P
  have hΩQ : Ω ≤ pCore 2 C := fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hΩc : Ω ≤ centralizer (pCore 2 C : Set C) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hsharp (A : Subgroup C) (hA : A ∈ thompsonAbelianSubgroups (P : Subgroup C))
      (hout : ¬ A ≤ pCore 2 C) :=
    Glauberman.maximum_abelian_replacement_of_fixedIndex hA hQS hΩQ
      (inferInstance : IsMulCommutative Ω) hΩc (by rw [normalizer_eq_top]; exact le_top)
      (by rw [hidx,inf_relIndex_left]; exact hlower A hout)
  have hSne : (P : Subgroup C) ≠ ⊥ := by
    intro he
    rw [he,relIndex_bot_right] at hidx
    omega
  obtain ⟨A,hA,hout,hquad,hupper⟩ := Glauberman.pushingUp_quadratic_offender P hSne hno
  have hi : (centralizer (A : Set C)).relIndex Ω = Nat.card F := by
    apply le_antisymm ?_ (hlower A hout)
    rw [inf_relIndex_left] at hupper
    exact hupper.trans (((pCore 2 C).relIndex_le_of_le_right hA.1
      index_ne_zero_of_finite).trans_eq hidx)
  refine ⟨E,hE,I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hlower,?_,⟨A,hA,hout,hquad,hi⟩,?_,hpair⟩
  · intro B hB hout
    obtain ⟨hgen,hS,hQ,hcard,hfixed,hfamily⟩ := hsharp B hB hout
    rw [hidx] at hfixed
    exact ⟨hgen,hS,hQ,hcard,hfixed,hfamily⟩
  · intro α hVN
    let N := NilesRankOneKernel.invariantNormalKernel (P : Subgroup C) α
    have hNQ : N.map (P : Subgroup C).subtype ≤ pCore 2 C :=
      le_sSup ⟨inferInstance,P.isPGroup'.of_injective
        (inclusion (map_subtype_le N)) (inclusion_injective _)⟩
    have hfamily := (hsharp A hA hout).2.2.2.2.2
    apply Glauberman.exists_maximum_abelian_kernel_intersection (P : Subgroup C) α
      (pCore 2 C) Ω hQS hfamily ⟨A,hA,hout⟩ _ hNQ hVN
    intro B hB hout
    obtain ⟨_,hrep,_,_,hfix,_⟩ := hsharp B hB hout
    refine ⟨hrep,?_⟩
    intro hΩB
    rw [inf_eq_right.mpr hΩB,relIndex_self,hidx] at hfix
    omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
