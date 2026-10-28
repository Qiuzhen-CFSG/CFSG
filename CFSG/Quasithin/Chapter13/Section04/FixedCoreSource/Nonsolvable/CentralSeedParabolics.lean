module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CentralSeed
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AmalgamCentralizers

/-!
# Applying the full central seed to the original parabolic

Construct the unique outside parabolic in each recognized centralizer
quotient. The component-module calculation supplies full Ω₁Z(T) containment,
so the fixed-line index and relative residual identities now hold on that
full seed. This discharges the outside-parabolic clauses of 13.4.7(b–c)
from the model and split inputs, including normality inside the actual
relative centralizer and the literal prime-to-three residual map.

The component classification and split, centralizer quotient recognition,
inside generating pair, chief-factor count, and the remaining pair-amalgam
application are still obligations of qt-d-1341-nonsolvable-source. This is
a conditional construction, not completion of 13.4.10 or 13.4.12.
Earlier local inputs retain discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.10(8) and 13.4.12, pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V K U : Subgroup G} {D : ChosenModule T L V}

/-- Construct the outside parabolic and its full-seed applicability clauses,
deriving seed containment from the component module and its actual orbit span. -/


theorem exists_parabolic_full_seed_of_component_split
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (DK : ChosenModule T K U) (marking : ComponentModuleAt DK z.val)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
      U ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)))
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
  have hseed := full_seed_of_component_split h structural m z hz1 hzT hindex
    DK marking hKz hKM hsplit
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V :=
    hseed.1 ▸ inf_le_left
  obtain ⟨P,hP,hmin,hPC,_,_,_,_,hfix,hidx,hu,hmax,hquot,_⟩ :=
    small_quotient_centralizer_parabolic h₀ h structural m z hz1 hzT
      (fun hh => hKM (hKz.trans hh)) hNT A hTA hAC
      (hgen ▸ le_sup_left) model
  rw [← hseed.1] at hfix hidx
  refine ⟨P,hP,hmin,hmax,hquot,hfix,hidx,hu,?_⟩
  intro X hX hPX hBX
  exact escaping_cubic_residual_in_overgroup h structural m z hz1 hzT hZV hNT
    A B P hAC.le hgen hP hPC model X hX hPX hBX

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
