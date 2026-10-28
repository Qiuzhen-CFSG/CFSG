module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSmallAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalSix

/-!
# The fixed-free ordinary component at the original G,T

Small quotient minimality constructs the chosen module on the actual moved
omega orbit. The earlier seven-row module theorem then identifies it with
the natural A6 module. Its Sylow fixed-point bound and the exact fixed line
in the full omega center give order four and containment in the original V.
The quotient and action maps are the literal K/O2(K) maps.

This is the guarded specialization of Nonsolvable/ComponentNaturalSix;
ComponentNaturalResidualAt uses it to identify the original quotient and
both reciprocal residuals. The selected ordinary row and earlier module
classification remain explicit. Source: Aschbacher--Smith 13.4.10(4--5),
printed pp.907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Construct the whole moved-module marking and the full central seed from
the same-G,T earlier classification and the original component geometry. -/
theorem ordinary_six_component_marking_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  obtain ⟨⟨DK⟩,hUR⟩ := component_chosen_of_small_quotient_at h₀ h structural m hzT hz1
    hKz h1332 hHN hKM hfK (Or.inr (Or.inl hcard))
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨q,e,he⟩ := ordinary_six_natural_coordinates DK eK hfixed (modules K _ hK12 DK)
  let ec : (K ⧸ centralCore K) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.quotientMulEquivOfEq (Solvable.centralCore_eq_twoCore_of_ordinary eK)
  have mark : ComponentModuleAt DK z.val := .naturalSix (ec.trans q) e (fun k v => he k v)
  exact ⟨DK,q,e,he,hUR,⟨mark⟩,full_seed_of_component_split_at h structural m z
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK mark hKz hKM
    (component_seed_split h₀ hzT hz1 hKz (h1332 K hfK).1)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
