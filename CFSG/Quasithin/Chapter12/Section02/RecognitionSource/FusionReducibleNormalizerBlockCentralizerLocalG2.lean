module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerContracts
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionControl
public import Theory.AtlasPort.LinearGroups.G2.BinaryLocalResidual
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# Local invariance in the original G₂(2) block row

The nonzero original fixed subgroup puts C_G(Ω₁Z(T)) inside N_G(L).
The genuine G₂(2)′ quotient, its elementary nine, and its outer group of
order at most two force L to have three-prime index there. Restriction
therefore preserves the ambient prime-to-three residual. The intrinsic
Sylow-overgroup theorem, lifted through the literal two-group kernel,
identifies it with O²(C_L(Ω₁Z(T))). Thus the full Sylow normalizer
preserves this subgroup and the two-core of its join with T.

No chosen module is identified with the omega-generated module. The
shared local-invariance contract is discharged in this row; its terminal
centralizer application and the linear-three row remain with the owner
qt-d-12216-normalizer-block-centralizer.
Source: Aschbacher–Smith A.3.18 and 3.3.25(2), printed pp.51–52 and 599.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual G₂(2)′ component has three-prime index in its own normalizer. -/
theorem g2Two_normalizer_index_coprime_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nat.Coprime 3 (L.subgroupOf (normalizer (L : Set G))).index := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let eA : (A ⧸ pCore 2 A) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans e
  have hA := h.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hr := h.simpleQTKE.twoLocal_sqtk (maximal_unique h D).1.1
  exact Atlas.G2.BinaryLocalResidual.index_coprime_three A hA eA (hr.stronglyQuasithin 3 Nat.prime_three (by decide))

/-- Restriction to C_L(Z) preserves the ambient image of O^{3′}. -/
theorem g2Two_omega_cubic_residual_eq_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype =
    (primeToResidual 3 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G)).map
      (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype := by
  let N := normalizer (L : Set G)
  let C := centralizer (omegaCenterIn (T : Subgroup G) : Set G)
  have hCN : C ≤ N := omega_centralizer_le h D hne
  have he := congrArg (fun U : Subgroup N => U.map N.subtype)
    (embedded_primeToResidual_inf_eq_of_normal 3 (L.subgroupOf N) (C.subgroupOf N)
      (primeToResidual_le _ (g2Two_normalizer_index_coprime_three h D e)))
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
theorem omega_local_residuals_eq_of_g2Two
    (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    pResidual 2 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) =
      primeToResidual 3 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G) := by
  let C := centralizer (omegaCenterIn (T : Subgroup G) : Set G)
  let B := (L ⊓ C).subgroupOf L
  let q : L →* commutator (Atlas.G2.Model (ZMod 2)) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := local_sylow D
  have hPB : (P : Subgroup L) ≤ B := by
    intro l hl
    refine ⟨l.property, ?_⟩
    intro z hz
    exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 l (hP l hl)).symm
  have hs : (P.mapSurjective hq : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) ≤ B.map q :=
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
    (q.subgroupMap_surjective B) hk (Atlas.G2.BinaryLocalResidual.sylow_overgroup_residuals (P.mapSurjective hq) (B.map q) hs)
  let b : B ≃* (L ⊓ C : Subgroup G) := subgroupOfEquivOfLe inf_le_left
  have hh := congrArg (fun U : Subgroup B => U.map b.toMonoidHom) hB
  rw [map_pResidual_of_surjective 2 b.toMonoidHom b.surjective, map_primeToResidual b] at hh
  exact hh


/-- The ambient cubic residual is the original block local residual in the G₂(2)′ row. -/
theorem blockLocalResidual_eq_ambient_of_g2Two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsG2TwoBlock L) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = blockLocalResidual T L := by
  obtain ⟨e⟩ := hb.quotient_iso
  rw [g2Two_omega_cubic_residual_eq_local h D hne e,
    ← omega_local_residuals_eq_of_g2Two D e]
  rfl

/-- Source 3.3.25(2) for the G₂ row, from the original nonzero fixed subgroup. -/
theorem blockLocalInvariance_of_g2Two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsG2TwoBlock L) :
    BlockLocalInvariance T L := by
  have he := blockLocalResidual_eq_ambient_of_g2Two h D hne hb
  refine ⟨fun _ => ⟨sylow_normalizer_normalizes_omegaLocalResidual he,
    sylow_normalizer_normalizes_omegaResidualCore he⟩, ?_⟩
  intro hl
  have ha := hb.module_card
  have hc := hl.module_card
  norm_num at ha hc
  omega

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
