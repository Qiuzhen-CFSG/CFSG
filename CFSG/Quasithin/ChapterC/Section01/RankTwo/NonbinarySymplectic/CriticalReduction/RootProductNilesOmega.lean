module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesOffenders
public import Theory.GroupTheory.RankOneInvariantKernelOmega
public import Glauberman.MaximumAbelianKernelOmega

/-!
# The larger omega layer for the original Niles group

For the same F0, original Baumann Sylow and residual conjugator, every
invariant normal kernel containing the core omega has C_S(Omega1 Z(N))=N.
The maximum abelian subgroup selected in Niles 7.5 has fixed index exactly
q on this larger omega. Its chosen residual conjugate generates a supplement
to the literal two-core and has combined fixed index at most q squared.
Every original field parameter, envelope and fixed central attachment is retained.

Source: Niles (1979), Lemma 7.6, printed pp.61-62, applied in MS93 (5.1),
printed p.913. The orbit identity and pushing-up structure still require
matching movement bounds and the subsequent source argument.
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

theorem Input.replacement_root_product_F0_niles_omega
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
          centralizer (omegaCenterIn (pCore 2 C) : Set C) = pCore 2 C ∧
          ∃ x : C, x ∈ pResidual 2 C ∧
            (P : Subgroup C) ⊔ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = ⊤ ∧
            (P : Subgroup C) ⊓ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = pCore 2 C ∧
            ∀ α : MulAut P,
              omegaCenterIn (pCore 2 C) ≤
                (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype →
              let N := (invariantNormalKernel (P : Subgroup C) α).map (P : Subgroup C).subtype
              let W := omegaCenterIn N
              N ≤ pCore 2 C ∧ omegaCenterIn (pCore 2 C) ≤ W ∧ W.Normal ∧
                (P : Subgroup C) ⊓ centralizer (W : Set C) = N ∧
                ∃ A : Subgroup C, A ∈ thompsonAbelianSubgroups (P : Subgroup C) ∧
                  ¬ A ≤ pCore 2 C ∧ A ⊓ pCore 2 C = A ⊓ N ∧
                  A ⊔ pCore 2 C = (P : Subgroup C) ∧
                  (centralizer (A : Set C)).relIndex W = Nat.card F ∧
                  (A ⊔ A.map (MulAut.conj x).toMonoidHom) ⊔ pCore 2 C = ⊤ ∧
                  (centralizer ((A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup C) : Set C)).relIndex W ≤
                    Nat.card F ^ 2 := by
  obtain ⟨E,hE,I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hlower,hsharp,hoff,hselect,x,hx,hpair,hinter⟩ :=
    h.replacement_root_product_F0_niles_offenders d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion (hCI.trans hI)) (inclusion_injective _)
  have hq : 1 < Nat.card F := by rw [h.field_card]; exact Nat.one_lt_pow h.nonbinary.ne_zero (by decide)
  have hCV : centralizer (omegaCenterIn (pCore 2 C) : Set C) ≤ pCore 2 C := by
    by_contra hn
    have hi := hlower _ hn
    have hone : (centralizer (centralizer (omegaCenterIn (pCore 2 C) : Set C) : Set C)).relIndex
        (omegaCenterIn (pCore 2 C)) = 1 :=
      relIndex_eq_one.mpr (le_centralizer_iff.mp le_rfl)
    rw [hone] at hi
    omega
  have hCVeq : centralizer (omegaCenterIn (pCore 2 C) : Set C) = pCore 2 C :=
    le_antisymm hCV (le_centralizer_iff.mp (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1))
  refine ⟨E,hE,I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,hequiv,hidx,hCVeq,x,hx,hpair,hinter,?_⟩
  intro α hVN
  obtain ⟨hNQ,hVW,hWn,hCW⟩ := invariantKernel_omega_properties P α hVN hCV
  obtain ⟨A,hA,hout,hAN⟩ := hselect α hVN
  have hAQ := (hsharp A hA hout).1
  have hi := Glauberman.maximum_abelian_kernel_omega_index P _ hNQ hVW
    (Nat.card F) hidx hlower A hA hout hAN
  let _ := hWn
  have hp := Glauberman.selected_pair_fixed_index_bound (P : Subgroup C) (pCore 2 C)
    _ A hAQ x hpair (Nat.card F) hi
  exact ⟨hNQ,hVW,hWn,hCW,A,hA,hout,hAN,hAQ,hi,hp⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
