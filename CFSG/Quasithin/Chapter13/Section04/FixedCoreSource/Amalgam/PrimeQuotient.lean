module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Components
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ModelQuotients
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The actual component in the prime-to-three amalgam quotient

The earlier 13.3.2 models show that a selected component loses exactly its
two-core under X → X/O₃′(X). The resulting isomorphism retains the value
on every representative. Thus its image is an ordinary, normal component.
The solvable O₃′ core also shows that a nonsolvable join has a nonsolvable
quotient, excluding the collapsed S₃ row of F.6.11. The quotient therefore
retains both vertices and the original common Sylow image.

F.6.10 then places one local residual in this same component and gives
the supplement by the opposite vertex. All component, normality, overlap
and quotient data are constructed from the original pair. The further
model exclusions, Thompson normality and overgroup formula are still
needed for 13.4.7. Source1332OneTwo remains an earlier-source premise.
Source: Aschbacher–Smith 13.4.7, printed p.900; F.6.10–11, pp.306–307.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Section03.Noncentrality.SupercriticalSource
variable {X : Type*} [Group X] [Finite X] {A B : Subgroup X}

/-- A nonsolvable Goldschmidt triple remains nonsolvable modulo its three-prime core. -/
private theorem prime_quotient_not_solvable (hg : ChapterF.IsGoldschmidtTriple A B)
    (hn : ¬ Group.IsSolvable X) : ¬ Group.IsSolvable (X ⧸ pPrimeCore 3 X) := by
  intro hs
  exact hn ((Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 X)).mpr
    ⟨hg.primeToThreeCore_solvable,hs⟩)

/-- Nonsolvability rules out the collapsed S₃ quotient in F.6.11. -/
private theorem prime_quotient_preserves_pair (hg : ChapterF.IsGoldschmidtTriple A B)
    (hn : ¬ Group.IsSolvable X) :
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    A.map q ⊓ B.map q = (A ⊓ B).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  rcases hg.primeToThreeCore_dichotomy with hp | hc
  · exact ⟨hp.1,hp.2.1⟩
  obtain ⟨e⟩ := hc.2.2.1
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  exact (prime_quotient_not_solvable hg hn
    (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim

variable {G : Type*} [Group G] [Finite G]

private theorem internal_component_model (Y : Subgroup G) (K : Subgroup Y)
    (hK : K.IsCComponent) (hm : MidSizeModel ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype))) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧ pPrimeCore 3 (K ⧸ pCore 2 K) = ⊥ := by
  let C := K.map Y.subtype
  let e := K.equivMapOfInjective Y.subtype Y.subtype_injective
  let eq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) e (pCore_map_iso 2 e)
  let := hK.perfect
  let : Group.IsPerfect C := Group.IsPerfect.map Y.subtype
  let : Group.IsPerfect (C ⧸ pCore 2 C) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (C ⧸ pCore 2 C) := midSize_quasisimple hm
  refine ⟨IsQuasisimple.of_mulEquiv eq.symm,?_⟩
  apply map_injective (f := eq.toMonoidHom) eq.injective
  rw [pPrimeCore_map_iso,midSize_primeToThreeCore_eq_bot hm,Subgroup.map_bot]

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The actual selected component survives faithfully modulo the three-prime core. -/
theorem original_pair_component_prime_image
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let Y := A ⊔ B
    let q := QuotientGroup.mk' (pPrimeCore 3 Y)
    (q.subgroupMap K).ker = pCore 2 K ∧
      IsComponent (Y ⧸ pPrimeCore 3 Y) (K.map q) ∧ (K.map q).Normal ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* K.map q,
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k := by
  let Y := A ⊔ B
  let q := QuotientGroup.mk' (pPrimeCore 3 Y)
  obtain ⟨hn,hf,_,_,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨hq,hcore⟩ := internal_component_model Y K hK (h1332 _ hf).2
  let : IsQuasisimple (K ⧸ pCore 2 K) := hq
  have hk : (q.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact CComponentExceptionalQuotient.core_comap K hK.subnormal hcore
  let e : (K ⧸ pCore 2 K) ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
        (q.subgroupMap_surjective K))
  let : IsQuasisimple (K.map q) := IsQuasisimple.of_mulEquiv e
  refine ⟨hk,⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),inferInstance⟩,
    hn.map q (QuotientGroup.mk'_surjective _),e,?_⟩
  intro k
  rfl



/-- F.6.10 on the literal quotient: the actual component contains one local
residual and supplements the other vertex. -/
theorem original_pair_prime_component_supplement
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let Y := A ⊔ B
    let q := QuotientGroup.mk' (pPrimeCore 3 Y)
    let Ap := (A.subgroupOf Y).map q
    let Bp := (B.subgroupOf Y).map q
    let Kp := K.map q
    ¬ Group.IsSolvable (Y ⧸ pPrimeCore 3 Y) ∧
      Ap ⊓ Bp = ((T : Subgroup G).subgroupOf Y).map q ∧
      ChapterF.IsGoldschmidtTriple Ap Bp ∧
      IsComponent (Y ⧸ pPrimeCore 3 Y) Kp ∧ Kp.Normal ∧
      (((pResidual 2 Ap).map Ap.subtype ≤ Kp ∧ Kp ⊔ Bp = ⊤) ∨
        ((pResidual 2 Bp).map Bp.subtype ≤ Kp ∧ Kp ⊔ Ap = ⊤)) := by
  let Y := A ⊔ B
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have hns : ¬ Group.IsSolvable Y := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  obtain ⟨hp,ht⟩ := prime_quotient_preserves_pair hg hns
  have hAB : A.subgroupOf Y ⊓ B.subgroupOf Y = (T : Subgroup G).subgroupOf Y := by
    change A.comap Y.subtype ⊓ B.comap Y.subtype = _
    rw [←comap_inf]
    exact congrArg (fun U : Subgroup G => U.subgroupOf Y)
      (intersection_eq_sylow hTA hTB eA eB hne)
  rw [hAB] at hp
  obtain ⟨_,hc,hn,_⟩ := original_pair_component_prime_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  let := hn
  exact ⟨prime_quotient_not_solvable hg hns,hp,ht,hc,hn,
    ChapterF.SourceAssembly.normal_component_contains_residual ht
      hg.primeToThreeCore_quotient_twoCore_eq_bot hc⟩



end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
