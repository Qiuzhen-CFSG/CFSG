module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesOmega
public import Theory.SpecificGroups.SL2.InvariantKernelOrbit
public import Theory.GroupTheory.RankOneInvariantKernelQuotient

/-!
# The original-degree central-chief Niles quotient

The original F0 and Baumann Sylow satisfy the cyclic-orbit formula of
Niles 7.6 using their actual selected maximum abelian subgroup. The
intersection argument of 7.2 therefore gives an automorphism-invariant
normal kernel with only central ambient chief factors. Its quotient has
characteristic two, a unique maximal Sylow overgroup, and an induced
Sylow automorphism fixing no nontrivial ambient-normal subgroup. The
original two-residual centralizes the kernel, and the quotient by the
new two-core is explicitly SL2 over the unchanged original field.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 7.3-7.6 and
Theorem 7.2, printed pp.60-62, applied to F0 in MS93 (5.1), printed p.913.
This completes the Main Hypothesis reduction for this F0; its structure,
source commutator conclusion and distance exclusion remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit NilesRankOneKernel
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_root_product_F0_niles_quotient
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
          (∀ α : MulAut P,
            (omegaCenterIn (pCore 2 C)).subgroupOf (P : Subgroup C) ≤
              invariantNormalKernel (P : Subgroup C) α →
            invariantNormalKernel (P : Subgroup C) α =
              ⨅ m : ℤ, ((pCore 2 C).subgroupOf (P : Subgroup C)).map ((α ^ m).toMonoidHom)) ∧
          ∃ α : MulAut P,
            let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
            let q := QuotientGroup.mk' N
            ∃ s : NoncentralChiefRefinement.SeriesOn N, (∀ i, s.Central i) ∧
              N ≤ pCore 2 C ∧
              pResidual 2 C ≤ centralizer (N : Set C) ∧
              Nonempty (((C ⧸ N) ⧸ pCore 2 (C ⧸ N)) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
              Nonempty (((C ⧸ N) ⧸ (pCore 2 C).map q) ≃* (C ⧸ pCore 2 C)) ∧
              generalizedFitting (C ⧸ N) = pCore 2 (C ⧸ N) ∧
              Order.HasUniqueMaximalOver ((P : Subgroup C).map q) ⊤ ∧
              ∃ β : MulAut ((P : Subgroup C).map q),
                NoInvariantNormal ((P : Subgroup C).map q) β := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,⟨e⟩,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hCV,x,hx,hpair,hinter,hselect⟩ :=
    h.replacement_root_product_F0_niles_omega d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (hCI.trans hI)) (inclusion_injective _)
  have hEc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hEn : 3 < Nat.card E.Carrier := by
    rw [hEc,←h.field_card]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n from h.nonbinary)
    rw [←h.field_card] at hh
    norm_num at hh
    omega
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) E.Carrier) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E.Carrier)).isSimpleGroup
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  have hnot : ¬ IsPGroup 2 (C ⧸ pCore 2 C) := by
    intro hp
    have hsl := hp.of_surjective e.toMonoidHom e.surjective
    have hh : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) E.Carrier)) ≤ pCore 2 _ :=
      le_sSup ⟨inferInstance,hsl.to_subgroup _⟩
    rw [Matrix.SL2.twoCore_eq_bot] at hh
    exact top_ne_bot (le_bot_iff.mp hh)
  have hformula : ∀ α : MulAut P,
      (omegaCenterIn (pCore 2 C)).subgroupOf (P : Subgroup C) ≤
        invariantNormalKernel (P : Subgroup C) α →
      invariantNormalKernel (P : Subgroup C) α =
        ⨅ m : ℤ, ((pCore 2 C).subgroupOf (P : Subgroup C)).map ((α ^ m).toMonoidHom) := by
    intro α hv
    have hVS : omegaCenterIn (pCore 2 C) ≤ (P : Subgroup C) :=
      fun _ hz => pCore_isPGroup.le_sylow_of_normal P (((mem_omegaCenterIn_iff _ _).mp hz).1)
    have hVN : omegaCenterIn (pCore 2 C) ≤
        (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype := by
      have hh := map_mono (f := (P : Subgroup C).subtype) hv
      rwa [map_subgroupOf_eq_of_le hVS] at hh
    obtain ⟨_,_,_,_,A,_,_,_,_,_,hL,hup⟩ := hselect α hVN
    apply sl2_invariantKernel_orbit P α e (show 1 < n from h.nonbinary) hEc hVN hCV
      (A ⊔ A.map (MulAut.conj x).toMonoidHom) hL
    simpa only [hEc,←h.field_card] using hup
  obtain ⟨α,s,hcentral,hNQ,he,hfitQ,huniqueQ,β,hβ⟩ :=
    exists_main_quotient_of_orbit_formula P hunique (pCore 2 C) hnot hfit hno hformula
  let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
  let q := QuotientGroup.mk' N
  have hNtwo : IsPGroup 2 N := pCore_isPGroup.to_le hNQ
  have hqker : IsPGroup 2 q.ker := by
    exact hNtwo.of_equiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N).symm)
  let ecore := q.pCoreQuotientEquiv (QuotientGroup.mk'_surjective N) hqker
  exact ⟨E,hE,I,hI,C,hCI,hCn,hgen,⟨e⟩,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hformula,α,s,hcentral,hNQ,
    residual_le_centralizer_of_central_chief_series N hNtwo s hcentral,
    ⟨ecore.symm.trans e⟩,he,hfitQ,huniqueQ,β,hβ⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
