module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Components
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer

/-!
# Escape and fixed-line movement of the actual amalgam component

The constructed faithful-local component is maximal and normal in the
join. Component uniqueness identifies its normalizer as the unique maximal
two-local subgroup over CT. If either it lay in M=N_G(L), or L normalized
it, the two uniqueness statements would put the whole join in M. Thus an
escaping join forces both noncontainments. Since C_G(C_V(L))=M, the
component moves the original fixed line as well.

The existential theorem constructs the same component, its normalizer
geometry and fixed-line movement from nonsolvability. Earlier Chapter 12
structure and Source1332OneTwo remain explicit genuine source inputs.
No component, normalizer uniqueness or escape conclusion is assumed.
The component catalogue and the remaining 13.4.7 alternatives are still
required for source assembly.
Source: Aschbacher–Smith 13.4.5(1–2) and 13.4.7, printed pp.898–900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Local uniqueness places the actual component outside M and forces it
to move the original fixed line. -/
theorem original_pair_component_normalizers {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let C := K.map X.subtype
    IsMaximalTwoLocal (normalizer (C : Set G)) ∧
      (∀ Y : Subgroup G, IsMaximalTwoLocal Y → C ⊔ (T : Subgroup G) ≤ Y →
        Y = normalizer (C : Set G)) ∧
      ¬ C ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (C : Set G) ∧
      ⁅V ⊓ centralizer (L : Set G),C⁆ ≠ ⊥ := by
  let X := A ⊔ B
  let C := K.map X.subtype
  obtain ⟨hn,hf,hstar,hTC,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hrestrict : C.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  have hXC : X ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp (hrestrict.symm ▸ hn)
  have hu := h.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hc := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
    (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H)) h₀.qtke T hstar
  have horb : componentOrbit C (T : Subgroup G) = C :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer C _ C le_rfl hTC)
      (le_componentOrbit C _)
  have hmax : IsMaximalTwoLocal (normalizer (C : Set G)) := horb ▸ hc.normalizer_maximal
  have huniq : ∀ Y : Subgroup G, IsMaximalTwoLocal Y → C ⊔ (T : Subgroup G) ≤ Y →
      Y = normalizer (C : Set G) := by
    intro Y hY hCY
    have hh := hc.normalizer_unique Y hY hCY
    change Y = normalizer (componentOrbit C (T : Subgroup G) : Set G) at hh
    rwa [horb] at hh
  have hLN : ¬ L ≤ normalizer (C : Set G) := by
    intro hLN
    exact hout (hXC.trans_eq (hu.2 _ hmax (sup_le hLN hTC)))
  have hCM : ¬ C ≤ normalizer (L : Set G) := by
    intro hCM
    exact hout (hXC.trans_eq (huniq _ hu.1 (sup_le hCM D.sylow_normalizes_component)).symm)
  refine ⟨hmax,huniq,hCM,hLN,?_⟩
  intro hh
  have hz := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  exact hCM (hz.trans_eq (fixed_centralizer_eq_normalizer h structural D m))

/-- The nonsolvable branch constructs its escaping faithful component and
its nontrivial action on the original fixed line. -/
theorem exists_original_pair_escaping_component {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    ∃ C : Subgroup G,
      C ∈ Chapter1.cComponentsIn X ∧
      C ∈ MainForward.faithfulLocalComponents T ∧ C ∈ Chapter1.LStar G T ∧
      X ≤ normalizer (C : Set G) ∧ (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      IsMaximalTwoLocal (normalizer (C : Set G)) ∧
      (∀ Y : Subgroup G, IsMaximalTwoLocal Y → C ⊔ (T : Subgroup G) ≤ Y →
        Y = normalizer (C : Set G)) ∧
      ¬ C ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (C : Set G) ∧
      ⁅V ⊓ centralizer (L : Set G),C⁆ ≠ ⊥ := by
  let X := A ⊔ B
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  obtain ⟨hn,hf,hstar,hTC,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨hmax,huniq,hCM,hLN,hmove⟩ := original_pair_component_normalizers
    h₀ h structural D m h1332 hTA hTB eA eB hne hindexA hindexB hout K hK
  have hrestrict : (K.map X.subtype).subgroupOf X = K :=
    comap_map_eq_self_of_injective X.subtype_injective K
  have hc : ((K.map X.subtype).subgroupOf X).IsCComponent := hrestrict.symm ▸ hK
  have hn' : ((K.map X.subtype).subgroupOf X).Normal := hrestrict.symm ▸ hn
  exact ⟨K.map X.subtype,⟨map_subtype_le _,hc⟩,hf,hstar,
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hn',hTC,
    hmax,huniq,hCM,hLN,hmove⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
