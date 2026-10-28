module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentSix
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentSmallQuotient
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedFreeRows
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The fixed-free ordinary A₆ moved module

For the selected ordinary A₆ component, the already proved small-quotient
minimality identifies its actual moved omega-orbit with [R₂(KT),K]. The
seven earlier module alternatives, specialized at the original G,T, then
leave only the natural six-letter quotient action: the other actors have
different orders. Vanishing fixed space makes the literal central-module
projection an isomorphism. The resulting marking retains K → K/O₂(K) and
also supplies the central-core marking used by the central-seed theorem.
Orbit splitting now proves |Ω₁Z(T)|=4 and Ω₁Z(T)≤V on this branch.

Theorem1222ModulesAt retains its genuine producer qt-d-1222-modules, with
its multiple-overgroup guard supplied when specializing the source theorem.
The universal Structural1222 premise is retained and is not inferred from
a pointwise input. Earlier structural and 13.3.2 discharge remains with
qt-d-1341-fixed-core-source. The selected covering and linear-three rows,
comparison, commutator and graph assembly stay with
qt-d-1341-nonsolvable-source. Universal nonsolvability at both original
escaping weights remains required; this is not the final contradiction.

Source: Aschbacher–Smith 12.2.2(3), 13.3.2(3), and 13.4.10(4–5),
printed pp.795,885,907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource ChapterB.QuasisimpleSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

private theorem linear_card_ne_six {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) :
    Nat.card SL(n,ZMod 2) ≠ 360 := by
  have hc : Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
      Matrix.card_GL_field]
    simp
  rw [hc]
  rcases hn with rfl | rfl | rfl <;> norm_num [Fin.prod_univ_succ]

/-- The earlier seven-case theorem identifies the literal ordinary fixed-free
chosen action, including its quotient projection. -/
theorem ordinary_six_natural_coordinates
    (DK : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : U ⊓ centralizer (K : Set G) = ⊥)
    (hm : ModuleAlternatives1222 DK) :
    ∃ q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      ∃ e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
        ∀ (k : K) (v : U),
          (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
            BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
              (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hc : Nat.card (K ⧸ pCore 2 K) = 360 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num
  let := DK.actionCentralizer_normal
  have hfaith : Nat.card (K ⧸ (centralizer (U : Set G)).subgroupOf K) = 360 :=
    (Nat.card_congr (DK.coreToFaithfulEquiv hs).toEquiv).symm.trans hc
  have haction : Nonempty (ActionEquiv DK.quotientAction
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))) := by
    cases hm with
    | linear n hn a =>
      exact (linear_card_ne_six hn ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
    | linearThreeExtension a _ _ =>
      exact (linear_card_ne_six (Or.inl rfl) ((Nat.card_congr a.toEquiv).symm.trans hc)).elim
    | linearFiveExterior a _ _ =>
      exact (linear_card_ne_six (Or.inr (Or.inr rfl)) ((Nat.card_congr a.toEquiv).symm.trans hc)).elim
    | alternating n hn hn' a =>
      have he : n = 6 := by
        have hh := (Nat.card_congr a.groupEquiv.toEquiv).symm.trans hfaith
        change Nat.card (alternatingGroup (Fin n)) = 360 at hh
        interval_cases n <;> first
        | rfl
        | norm_num only [nat_card_alternatingGroup, Nat.card_fin, Nat.factorial] at hh
      subst n
      refine ⟨⟨(DK.coreToFaithfulEquiv hs).trans a.groupEquiv,
        (RecognitionSource.fixedFreeQuotientEquiv DK hfixed).trans a.linearEquiv,?_⟩⟩
      intro k v
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) k
      exact a.intertwines (QuotientGroup.mk' ((centralizer (U : Set G)).subgroupOf K) x)
        (RecognitionSource.fixedFreeQuotientEquiv DK hfixed v)
    | alternatingSevenFour a _ =>
      have hh := (Nat.card_congr a.toEquiv).symm.trans hfaith
      rw [nat_card_alternatingGroup,Nat.card_fin] at hh
      norm_num at hh
    | g2 a =>
      have hh := (Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc
      rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
      omega
    | tripleSix a _ _ _ =>
      have hh := (Nat.card_congr a.toEquiv).symm.trans hc
      rw [Atlas.Codes.hexEven_card] at hh
      omega
  obtain ⟨a⟩ := haction
  obtain ⟨q,e,he⟩ := DK.conjugationModel_of_quotientAction a
  refine ⟨q,e,?_⟩
  intro k v
  have hh : e.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)) =
      U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v := Subtype.ext (he k v)
  simpa only [e.apply_symm_apply,toAdd_ofAdd] using
    (congrArg (fun w : U => (e w).toAdd) hh).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Construct the whole moved-module marking and the full central seed from
the same-G,T earlier classification and the original component geometry. -/
theorem ordinary_six_component_marking
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) = ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      ∃ q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
        ∃ e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
          (∀ (k : K) (v : U),
            (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
              BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
                (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) ∧
          U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
            (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
          Nonempty (ComponentModuleAt DK z.val) ∧
          omegaOneCenterAmbient (T : Subgroup G) =
            V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
          Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hcard : Nat.card (K ⧸ pCore 2 K) = 360 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨⟨DK⟩,hUR⟩ := component_chosen_of_small_quotient h₀ h structural m hzT hz1
    hKz h1332 hHN hKM hfK (Or.inr (Or.inl hcard))
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨q,e,he⟩ := ordinary_six_natural_coordinates DK eK hfixed (modules K _ hK12 DK)
  let ec : (K ⧸ centralCore K) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.quotientMulEquivOfEq (Solvable.centralCore_eq_twoCore_of_ordinary eK)
  have mark : ComponentModuleAt DK z.val := .naturalSix (ec.trans q) e (fun k v => he k v)
  exact ⟨DK,q,e,he,hUR,⟨mark⟩,full_seed_of_component_split h structural m z
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK mark hKz hKM
    (component_seed_split h₀ hzT hz1 hKz (h1332 K hfK).1)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
