module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalGeneration

/-!
# Constructing the original plane and all amalgam applicability clauses

The full normalizer action on the marked augmentation core maps the original
Sylow subgroup to a Sylow of a permutation group between A₆ and S₆.
The concrete six-letter Sylow flag supplies an invariant plane. Pulling it
back through the literal natural quotient and core coordinates proves
normalization of the original plane preimage in G.

The source application now constructs its own plane, its generating pair,
and the normalizer supplement. It also supplies V≤J(R₁) by the independent
ordinary point-radical calculation. The retained earlier 13.2–13.3 and
13.4.2–3 inputs then give all the hypotheses (a–c) of 13.4.7 and exclude
its product case, for the actual IT and L₂T. No invariant plane, parabolic
marking, generating pair, supplement or Thompson containment is assumed.

The general 13.4.7 alternatives and exclusions (3–4) are still required
from qt-d-1341-fixed-core-source; their solvable case selection remains with
qt-d-1341-solvable-source. This does not assert that the generated H₀ is
local before that theorem proves it. The genuine universal Structural1222
premise remains universal.
Source: Aschbacher–Smith 13.4.7,13.4.9, pp.899,906; Notation 13.2.1, p.877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource BinaryPermutation
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_preimage_of_permutation
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hn : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : normalizer (L : Set G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (x : normalizer (L : Set G)) (hx : q x ∈ flagStabilizer W) :
    x.val ∈ normalizer (m.naturalPreimage W : Set G) := by
  have he (v : V) :
      coreToNatural (Fin 6) (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        naturalRepresentation (Fin 6) (q x) (coreToNatural (Fin 6) (m.coordinate v).toAdd) := by
    rw [hq,coreToNatural_equivariant]
  apply mem_normalizer_iff.mpr
  intro a
  by_cases ha : a ∈ V
  · let v : V := ⟨a,ha⟩
    have hh := hx (coreToNatural (Fin 6) (m.coordinate v).toAdd)
    rw [←he,←m.mem_naturalPreimage,←m.mem_naturalPreimage] at hh
    exact hh.symm
  · have ha' : x.val * a * x.val⁻¹ ∉ V :=
      fun hh => ha (((mem_normalizer_iff.mp (hn x.property)) a).mpr hh)
    exact iff_of_false (fun hh => ha (m.naturalPreimage_le W hh))
      (fun hh => ha' (m.naturalPreimage_le W hh))

/-- Construct the source plane from the actual normalizer action and the
original Sylow subgroup, without an assumed invariant subspace. -/
theorem exists_original_invariant_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    ∃ W : Submodule (ZMod 2) (natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) := by
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,hqL,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  have hA : alternatingGroup (Fin 6) ≤ q.range := by
    intro a ha
    obtain ⟨v,hv⟩ := m.quotient.surjective ⟨a,ha⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) v
    exact ⟨inclusion L.le_normalizer l,(hqL l).trans (congrArg Subtype.val hv)⟩
  let S := T.subtype D.sylow_normalizes_component
  let Q := S.mapSurjective q.rangeRestrict_surjective
  obtain ⟨g,hg⟩ := sylow_flag_exists q.range hA Q
  let W := move g.val canonicalPlane
  refine ⟨W,(move_finrank _ _).trans
    canonicalPlane_finrank,?_⟩
  intro t ht
  let x : normalizer (L : Set G) := ⟨t,D.sylow_normalizes_component ht⟩
  have hx : q x ∈ (Q : Subgroup q.range).map q.range.subtype :=
    ⟨q.rangeRestrict x,⟨x,ht,rfl⟩,rfl⟩
  apply normalizes_preimage_of_permutation D m hn q hq W x
  exact (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.mem_stabilizer_iff_map W _).mpr
    (hg _ hx).2

/-- Construct the original pair and verify every applicability clause of
13.4.7, together with the residual commutator exclusion of case (i). -/
theorem exists_original_R1_amalgam_inputs
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let P := I ⊔ (T : Subgroup G)
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let L₂ := (pResidual 2 B).map B.subtype
      let H₀ := P ⊔ B
      let K₁ := (pResidual 2 P).map P.subtype
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let C₁ := H₀ ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := H₀ ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
      P ∈ Chapter1.HOver G (T : Set G) ∧ B ∈ Chapter1.HOver G (T : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
        B = L₂ ⊔ (T : Subgroup G) ∧
        IsCoatom (B.subgroupOf (L ⊔ (T : Subgroup G))) ∧
        (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
          s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
        (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
        (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧ P ≠ B ∧
        normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
        ¬ ⁅K₁,L₂⁆ ≤ K₁.pCoreIn 2 ∧
        (H₀ ∈ Chapter1.H G →
          H₀ ⊓ normalizer (L : Set G) = B ∧ H₀ ⊓ H = P ∧
          C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
          (primeToResidual 3 C₁).map C₁.subtype = K₁) := by
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  obtain ⟨W,hW,hT⟩ := exists_original_invariant_plane h structural D m
  have hg := (original_R1_inside_generation h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT).2
  exact ⟨W,hW,hT,original_R1_amalgam_conditions_of_plane h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hg
    (normalizer_component_centralizer_supplement h structural D m z)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
