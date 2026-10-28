module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CentralSeedParabolics
public import Theory.GroupTheory.ReducedNormal.ComponentSeedSplitting

/-!
# The source component orbit and its splitting

For K contained in the original involution centralizer and normalized by T,
the involution gives KT a nontrivial two-core. Ambient characteristic two
then applies to KT. The Sylow-fixed seed theorem proves
V_H = [V_H,K] C_Z(K) for the literal V_H = ⟨Z^K⟩ and Z = Ω₁Z(T).

The component marking now gives the full order-four seed and the outside
parabolic's relative centralizer identities without a splitting premise.
ComponentSelection constructs K from the earlier source inputs; excluding
the A₅, covered-A₆ and doubled-natural rows remains with
qt-d-1341-nonsolvable-source. The earlier structural/index inputs retain
final discharge with qt-d-1341-fixed-core-source. This is not completion of
13.4.10 or the nonsolvable branch.

Source: Aschbacher–Smith B.2.14 and 13.4.10, printed pp.78,907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V K : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
/-- The central involution gives the actual KT a nontrivial two-core. -/
theorem component_sylow_mem_HOver {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G)) :
    K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
  let H := K ⊔ (T : Subgroup G)
  have hzH : z ∈ H := mem_sup_right ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).1
  have hHz : H ≤ centralizer ({z} : Set G) :=
    sup_le hKz (Solvable.original_sylow_le_centralizer hzT)
  have hcyc : zpowers z ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime
          ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1]
        decide))
      (zpowers_le.mpr hzH)
      (by
        rw [← centralizer_closure, ← zpowers_eq_closure] at hHz
        exact hHz.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨?_,fun _ ht => mem_sup_right ht⟩
  intro he
  exact hz1 (mem_bot.mp (he ▸ hcyc (mem_zpowers z)))

/-- Characteristic two of KT proves the source orbit splitting. -/
theorem component_seed_split
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ⊔
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  exact omegaCenter_component_span_split T K hTK
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h₀.qtke.evenCharacteristic T) (component_sylow_mem_HOver hzT hz1 hKz)))

/-- Passing from the component orbit to its moved subgroup preserves the
literal action kernel inside KT. The fixed factor is already central in KT. -/
theorem component_seed_action_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    (K ⊔ (T : Subgroup G)) ⊓
        centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K : Set G) =
      (K ⊔ (T : Subgroup G)) ⊓
        centralizer ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  have hmove : ⁅W,K⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hmove))
  intro x hx
  refine ⟨hx.1,?_⟩
  have hfix : Z ⊓ centralizer (K : Set G) ≤ centralizer ((K ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact le_centralizer_iff.mp (fun y hy =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hy.1).2.2)
  have hw : W ≤ centralizer ({x} : Set G) := by
    change conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K ≤ _
    rw [component_seed_split h₀ hzT hz1 hKz hTK]
    apply sup_le
    · exact fun y hy => mem_centralizer_singleton_iff.mpr (hx.2 y hy)
    · exact fun y hy => mem_centralizer_singleton_iff.mpr (hfix hy x hx.1).symm
  exact fun y hy => mem_centralizer_singleton_iff.mp (hw hy)

/-- The three source module rows yield the full central seed, with no
independent splitting or full-seed containment premise. -/
theorem full_seed_of_component_moved_module
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (marking : ComponentModuleAt DK z.val) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  exact full_seed_of_component_split h structural m z hz1 hzT hindex DK marking hKz hKM
    (component_seed_split h₀ hzT (fun he => hz1 (Subtype.ext he)) hKz
      DK.sylow_normalizes_component)
/-- The full-seed parabolic application with the splitting derived from
characteristic two, retaining the actual moved module and quotient maps. -/
theorem exists_parabolic_full_seed_of_component_moved_module
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) (marking : ComponentModuleAt DK z.val)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (A B : Subgroup G) (hTA : (T : Subgroup G) < A)
    (hAC : A < centralizer ({z.val} : Set G))
    (hgen : A ⊔ B = normalizer (L : Set G))
    (model : Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* Equiv.Perm (Fin 6))) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T P ∧
      P ⋖ centralizer ({z.val} : Set G) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val ∧
      (omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex
          (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        Q ≤ centralizer ({z.val} : Set G) → Q = P) ∧
      ∀ X : Subgroup G, X ∈ Chapter1.H G → P ≤ X → B ≤ X →
        let C := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
          centralizer ((pResidual 2 P).map P.subtype : Set G) : Subgroup G) : Set G)
        (((pResidual 2 P).map P.subtype).subgroupOf C).Normal ∧
          (primeToResidual 3 C).map C.subtype = (pResidual 2 P).map P.subtype := by
  exact exists_parabolic_full_seed_of_component_split h₀ h structural m z hz1 hzT hindex
    DK marking hKz hKM
    (component_seed_split h₀ hzT (fun he => hz1 (Subtype.ext he)) hKz
      DK.sylow_normalizes_component) hNT A B hTA hAC hgen model

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
