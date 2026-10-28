module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionControl
public import Theory.SpecificGroups.Alternating.EightComponent
public import Theory.SpecificGroups.Alternating.EightSylowResidual
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.GroupTheory.PResidual.TwoKernelComparison

/-!
# The ambient residual identity in the A₈ branch

The source normalizer is strongly quasithin and contains L as a relatively
normal C-component. The literal A₈ quotient gives three-prime index there.
Since the full omega-centralizer is contained in that normalizer, intersecting
with L preserves its embedded prime-to-three residual.

The image of C_L(Ω₁Z(T)) in L/O₂(L) contains a full Sylow two-subgroup.
Its two-group kernel lifts the proved intrinsic comparison of O² and O^{3′}
to C_L(Ω₁Z(T)). Combining this with the restriction gives the exact ambient
residual identity without an additional model premise.

The conditional comparison interfaces are retained for existing consumers.
The chosen V is never identified with the omega-generated module. The
separate Thompson identity remains explicit in the normalizer application.
Source: Aschbacher–Smith 3.3.21(e), printed p.596; the application in
12.2.16, pp.799–800 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual A₈ component has three-prime index in its own normalizer. -/
theorem alternatingEight_normalizer_index_coprime_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)) :
    Nat.Coprime 3 (L.subgroupOf (normalizer (L : Set G))).index := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans e
  have hA := h.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hr := h.simpleQTKE.twoLocal_sqtk (maximal_unique h D).1.1
  exact alternatingGroup.EightComponent.index_coprime_three A hA eA (hr.stronglyQuasithin 3 Nat.prime_three (by decide))

/-- Restriction to C_L(Z) preserves the ambient image of O^{3′}. -/
theorem omega_cubic_residual_eq_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype =
    (primeToResidual 3 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G)).map
      (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype := by
  let N := normalizer (L : Set G)
  let C := centralizer (omegaCenterIn (T : Subgroup G) : Set G)
  have hCN : C ≤ N := omega_centralizer_le h D hne
  have he := congrArg (fun U : Subgroup N => U.map N.subtype)
    (embedded_primeToResidual_inf_eq_of_normal 3 (L.subgroupOf N) (C.subgroupOf N)
      (primeToResidual_le _ (alternatingEight_normalizer_index_coprime_three h D e)))
  rw [map_embedded_primeToResidual_of_hom, map_embedded_primeToResidual_of_hom,
    map_inf _ _ _ N.subtype_injective,
    map_subgroupOf_eq_of_le L.le_normalizer, map_subgroupOf_eq_of_le hCN] at he
  exact he.symm


private theorem local_sylow (D : ChosenModule T L V) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let S : Sylow 2 H := T.subtype le_sup_right
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro l ⟨r, hr, rfl⟩
  rw [hR] at hr
  exact hr

/-- The intrinsic Sylow-overgroup comparison lifts to the literal C_L(Z). -/
theorem omega_local_residuals_eq_of_alternatingEight_sylow_residuals
    (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8))
    (model : ∀ (S : Sylow 2 (alternatingGroup (Fin 8)))
      (H : Subgroup (alternatingGroup (Fin 8))), (S : Subgroup _) ≤ H →
        pResidual 2 H = primeToResidual 3 H) :
    pResidual 2 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) =
      primeToResidual 3 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) := by
  let C := centralizer (omegaCenterIn (T : Subgroup G) : Set G)
  let B := (L ⊓ C).subgroupOf L
  let q : L →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := local_sylow D
  have hPB : (P : Subgroup L) ≤ B := by
    intro l hl
    refine ⟨l.property, ?_⟩
    intro z hz
    exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 l (hP l hl)).symm
  have hs : (P.mapSurjective hq : Subgroup (alternatingGroup (Fin 8))) ≤ B.map q :=
    map_mono hPB
  have hkq : IsPGroup 2 q.ker := by
    have he : q.ker = pCore 2 L := by
      ext l
      change e (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff l
    rw [he]
    exact pCore_isPGroup
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    have he : (q.subgroupMap B).ker = q.ker.subgroupOf B := by
      ext b
      exact Subtype.ext_iff
    rw [he]
    exact hkq.comap_subtype
  have hB := Subgroup.twoResidual_eq_primeToResidual_three_of_two_kernel (q.subgroupMap B)
    (q.subgroupMap_surjective B) hk (model (P.mapSurjective hq) (B.map q) hs)
  let b : B ≃* (L ⊓ C : Subgroup G) := subgroupOfEquivOfLe inf_le_left
  have hh := congrArg (fun U : Subgroup B => U.map b.toMonoidHom) hB
  rw [map_pResidual_of_surjective 2 b.toMonoidHom b.surjective, map_primeToResidual b] at hh
  exact hh


/-- The literal ambient residual identity from an intrinsic Sylow-overgroup
comparison. The unconditional specialization below supplies that comparison. -/
theorem omega_residual_eq_of_alternatingEight_sylow_residuals
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8))
    (model : ∀ (S : Sylow 2 (alternatingGroup (Fin 8)))
      (H : Subgroup (alternatingGroup (Fin 8))), (S : Subgroup _) ≤ H →
        pResidual 2 H = primeToResidual 3 H) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L := by
  rw [omega_cubic_residual_eq_local h D hne e, ← omega_local_residuals_eq_of_alternatingEight_sylow_residuals D e model]
  rfl

/-- The two residuals of the literal C_L(Ω₁Z(T)) agree in the A₈ branch. -/
theorem omega_local_residuals_eq_of_alternatingEight
    (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)) :
    pResidual 2 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) =
      primeToResidual 3 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) :=
  omega_local_residuals_eq_of_alternatingEight_sylow_residuals D e
    AlternatingEight.sylow_overgroup_residuals

/-- The displayed residual identity in 3.3.21(e), under the actual Chapter 12
A₈ branch hypotheses: the ambient O^{3′}(C_G(Z)) is the embedded O²(C_L(Z)). -/
theorem omega_residual_eq_of_alternatingEight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L := by
  rw [omega_cubic_residual_eq_local h D hne e,
    ← omega_local_residuals_eq_of_alternatingEight D e]
  rfl

/-- Applying the intrinsic residual calculation supplies the first clause
of the parent's original OmegaResidualIdentities contract. The independent
Thompson identity is retained as its other clause. -/
theorem sylow_normalizer_le_of_alternatingEight_sylow_residuals
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8))
    (model : ∀ (S : Sylow 2 (alternatingGroup (Fin 8)))
      (H : Subgroup (alternatingGroup (Fin 8))), (S : Subgroup _) ≤ H →
        pResidual 2 H = primeToResidual 3 H)
    (hJ : Stellmacher.elementaryAbelianMaxJ (omegaResidualCore T L) =
      Stellmacher.elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_omegaResidual_thompson h D
    (omega_residual_eq_of_alternatingEight_sylow_residuals h D hne e model) hJ

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
