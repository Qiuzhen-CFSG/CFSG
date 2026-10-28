module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.ActionPrimeComparison
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Nonsolvable
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableCharacteristic

/-!
# Applying F.6.18 to the original SQTK amalgam

The involution centralizer makes the actual group Ke SQTK. Apply the
complete source classification to Ke/O₃′(Ke). The original action quotient
Ke/C_Ke(Ue) has trivial two-core and two-group kernels on both vertices;
F.6.8 and F.6.11 therefore identify their local images in the two quotients.
In particular the characteristic-two S₃ actor survives in the source quotient.
Distinct cores and this actor exclude rows (1)--(2), so that quotient is
nonsolvable. The action kernel is solvable, which proves nonsolvability of
the actual action quotient as well.

All source alternatives, including both additional rank-one branches, remain
in the conclusion with the original local labels. No equality of the whole
action and prime-to-three quotients is assumed. The faithful-component sieve,
PSL₃(2) module calculation and final centerlessness remain to be proved.
Source: Aschbacher--Smith 14.3.31, printed p.1003, and F.6.8, F.6.11,
F.6.18, printed pp.305--310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- The full source classification applies to the same Ke, and its original
orbit-action quotient is nonsolvable. -/
theorem source_solvable_source_classification_with_actor
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let p := QuotientGroup.mk' (pPrimeCore 3 E)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map p
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map p
      let C := (K.subgroupOf E).map p
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      IsSQTK KnownSimple.IsKnownSimple E ∧
      Group.IsSolvable (amalgamKernel F L K) ∧
      Nonempty ((K.subgroupOf E).map q ≃* C) ∧
      ChapterF.IsGoldschmidtTriple A B ∧
      generalizedFitting C = pCore 2 C ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ Nonempty ((A ⊓ B : Subgroup (E ⧸ pPrimeCore 3 E)) ≃* Multiplicative (ZMod 2)) ∧
      (∃ S : Sylow 2 (E ⧸ pPrimeCore 3 E), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S)) ∧
      ¬ Group.IsSolvable (E ⧸ pPrimeCore 3 E) ∧
      ¬ Group.IsSolvable (AmalgamQuotient F L K) := by
  obtain ⟨g,l,e,_,_,hl,he,heI,heT,_,hKH,hKN,hKC,hK,hKT,hout,hE,hr,hcore,_,hneq⟩ :=
    source_solvable_shifted_quotients d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let A₀ := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B₀ := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
  let C₀ := K.subgroupOf E
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let p := QuotientGroup.mk' (pPrimeCore 3 E)
  have hg := source_solvable_ambient_goldschmidt d earlier hq chosen structural alternatives F hne K hKH hKT
  have ha := source_amalgam_actor_kernel d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT
  have hb : IsPGroup 2 (q.subgroupMap B₀).ker := by
    have ht := (source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH).2.1
    rwa [source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne] at ht
  have hneq₀ : B₀.pCoreIn 2 ≠ A₀.pCoreIn 2 := by
    intro heq
    apply hneq
    have hh := congrArg (map E.subtype) heq
    rwa [pCoreIn_subgroupOf 2 _ E le_sup_right,pCoreIn_subgroupOf 2 _ E le_sup_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show F.I₂ L ⊔ (T : Subgroup G) ≤ E from le_sup_right)),
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show K ⊔ (T : Subgroup G) ≤ E from le_sup_left))] at hh
  let j : C₀.map q ≃* C₀.map p := hg.action_prime_local_equiv q
    (QuotientGroup.mk'_surjective _) hcore ha hb C₀ (comap_mono le_sup_left)
  obtain ⟨_,hf,hm⟩ := source_amalgam_actor_structure d earlier hq chosen structural alternatives F hne
    K hKH hKN hKC hK
  have hfit : generalizedFitting (C₀.map p) = pCore 2 (C₀.map p) := by
    have hmap := congrArg (fun N : Subgroup (C₀.map q) => N.map j.toMonoidHom) hf
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hmap
  have hmodel : Nonempty (((C₀.map p) ⧸ pCore 2 (C₀.map p)) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans hm.some⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple E := by
    have hc := (d.qtke.involution_centralizer_sqtk he).subgroup (E.subgroupOf (centralizer ({e} : Set G)))
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hE)).mp hc
  have hsolv : Group.IsSolvable (amalgamKernel F L K) := by
    have hs := hg.action_kernel_solvable q ha hb
    rwa [QuotientGroup.ker_mk'] at hs
  have hgold := hg.quotient_primeToThreeCore_of_distinct_cores (Ne.symm hneq₀)
  have h1 := hg.primeToThreeCore_intersection_not_cyclic_two (Ne.symm hneq₀)
  have h2 : ¬ (Nonempty ((E ⧸ pPrimeCore 3 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (E ⧸ pPrimeCore 3 E), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((E ⧸ pPrimeCore 3 E) ⧸ N) ≃* FSource.E4)) := by
    rintro (hp | ⟨N,hN,_,hc,_,⟨eN⟩⟩)
    · exact SymmetricThreeTwoCore.characteristic_two_not_symmetric_three_product _ hfit hmodel.some hp
    · let := hN
      have hN3 : IsPGroup 3 N := IsPGroup.of_card (n := 3) hc
      have hQ2 : IsPGroup 2 (_ ⧸ N) := by
        apply (IsPGroup.of_card (n := 2) (G := FSource.E4) ?_).of_equiv eN.symm
        simp [FSource.E4,FSource.C]
      exact SymmetricThreeTwoCore.characteristic_two_not_three_by_two _ hfit hmodel.some N hN3 hQ2
  let cover : ThreePrimeSQTKQuotient KnownSimple.IsKnownSimple (E ⧸ pPrimeCore 3 E) :=
    { Cover := E, sqtk := hsq, equiv := MulEquiv.refl _ }
  obtain ⟨S,hS,hrows⟩ := FSource.sourceClassification_knownSimple_complete _ _ _ hgold cover
  have hS1 : ¬ Nonempty (S ≃* FSource.C 2) := by
    rintro ⟨jS⟩
    exact h1 ⟨(MulEquiv.subgroupCongr hS).trans jS⟩
  have hnsolv : ¬ Group.IsSolvable (E ⧸ pPrimeCore 3 E) :=
    hrows.elim (fun h => FSource.source_alternative_nonsolvable h hS1 h2)
      (fun h => FSource.source_alternative_nonsolvable h hS1 h2)
  refine ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,hsq,hsolv,⟨j⟩,hgold,hfit,hmodel,h1,⟨S,hS,hrows⟩,hnsolv,?_⟩
  intro hs
  let : Group.IsSolvable (amalgamKernel F L K) := hsolv
  let : Group.IsSolvable E := (Group.isSolvable_iff_subgroup_quotient (amalgamKernel F L K)).mpr ⟨hsolv,hs⟩
  exact hnsolv inferInstance

/-- The source classification with the original public conclusion. -/
theorem source_solvable_source_classification
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let p := QuotientGroup.mk' (pPrimeCore 3 E)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map p
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map p
      let C := (K.subgroupOf E).map p
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      IsSQTK KnownSimple.IsKnownSimple E ∧
      Group.IsSolvable (amalgamKernel F L K) ∧
      Nonempty ((K.subgroupOf E).map q ≃* C) ∧
      ChapterF.IsGoldschmidtTriple A B ∧
      generalizedFitting C = pCore 2 C ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ Nonempty ((A ⊓ B : Subgroup (E ⧸ pPrimeCore 3 E)) ≃* Multiplicative (ZMod 2)) ∧
      (∃ S : Sylow 2 (E ⧸ pPrimeCore 3 E), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S)) ∧
      ¬ Group.IsSolvable (E ⧸ pPrimeCore 3 E) ∧
      ¬ Group.IsSolvable (AmalgamQuotient F L K) := by
  obtain ⟨l,e,hl,he,heI,heT,_,_,_,_,_,_,hrest⟩ :=
    source_solvable_source_classification_with_actor d earlier hq chosen structural alternatives F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,hrest⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
