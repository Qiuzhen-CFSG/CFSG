module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlaneExistence
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalGeneratedAmalgam

/-!
# Selecting the original linear amalgam from the earlier source proposition

The residual of the full plane normalizer equals the embedded residual of
N_L(V₂). Thus the second member of the constructed pair is literally the
L₂ of Notation 13.2.1. The earlier 13.4.7(3--4) exclusions apply to this
residual, and (4) supplies the commutator premise of the overgroup formula (2).
The checked original-pair construction verifies (a--c); its residual
commutator exclusion eliminates (1i), selecting the linear case.

`PlaneAmalgamSource1347` states the precise restricted consequence of
13.4.7(1--4) used here, for every applicable pair with this original second
parabolic. It is an explicit earlier-source hypothesis, not a proof of
13.4.7. Only the clauses consumed below are retained; no claim is made to
encode the complete module alternatives. In particular, the excluded rows
are not replaced by arbitrary group-family tags. `LinearAmalgamConclusion`
retains the actual component, local-family memberships, quotient and
relative Thompson normality, together with the literal overgroup formula.

The producer of this earlier input is qt-d-1341-fixed-core-source, which
absorbed qt-d-1341-local-amalgam-source. It also owns discharge of the
earlier Chapter 12 and 13.3 inputs. OriginalSource applies the selected
case to ambient recognition. Fusion control on V is retained as the earlier
13.2.2(5) input used in 13.4.2; ambient involution fusion is proved below.
Source: Aschbacher--Smith 13.4.7 and 13.4.9, printed pp.899--906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full second parabolic has the literal residual of the inner
plane normalizer from Notation 13.2.1. -/
theorem original_second_flag_residual_eq_inner
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
    (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype := by
  dsimp only
  rw [second_flag_normalizer_eq D _ hT]
  exact second_parabolic_full_residual _ (m.sylow_normalizes_inner_plane W hT)

/-- The part of the linear case needed below, retaining the actual component,
local families, quotient and relative Thompson normality. This is a conclusion
predicate, not an assertion that such a component exists. Its body is exposed
so consumers can use the actual component and relative subgroup data. -/
@[expose] def LinearAmalgamConclusion (T : Sylow 2 G) (X : Subgroup G) : Prop :=
  (∃ K : Subgroup G,
    K ∈ Chapter1.cComponentsIn X ∧
    K ∈ MainForward.faithfulLocalComponents T ∧ K ∈ Chapter1.LStar G T ∧
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
    X = K ⊔ (T : Subgroup G) ∧
    Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)) ∧
  X ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
  (∀ Y : Subgroup G, Y ∈ Chapter1.HOver G (X : Set G) →
    (Y : Set G) = (X : Set G) *
      (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) : Subgroup G))

/-- The precise earlier-source input used by the solvable branch: the
consequence of 13.4.7(1--4) for an arbitrary applicable pair whose second
residual is the original L₂. Clauses (3--4) exclude (iii--iv); in (ii),
clause (4) supplies K₂=[K₂,J₁(T)], allowing the overgroup formula of (2).

Only the commutator bound of (i) and the component/normalizer/overgroup
conclusions of (ii) are retained. This is a restricted consequence of the
source proposition, not a definition of the full proposition or a proof of it.
Its construction belongs to qt-d-1341-fixed-core-source. The body is exposed
so that owner can construct precisely this proposition across module boundaries. -/
@[expose] def PlaneAmalgamSource1347 (D : ChosenModule T L V) (m : CoreMarking D) : Prop :=
  ∀ (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6))),
    Module.finrank (ZMod 2) W = 2 →
    (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) →
    ∀ P : Subgroup G,
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      P ∈ Chapter1.HOver G (T : Set G) →
      B ∈ Chapter1.HOver G (T : Set G) →
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) →
      P ≠ B → K₂ = (pResidual 2 J).map J.subtype →
      ((∀ s : NoncentralChiefRefinement.ChiefSeries K₁,
          s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount) ∨
        (∀ s : NoncentralChiefRefinement.ChiefSeries K₂,
          s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount)) →
      (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 →
      (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 →
      (X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂)) →
      X ∈ Chapter1.HOver G (T : Set G) ∧
        (⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 ∨ LinearAmalgamConclusion T X)

/-- Apply the earlier source alternatives to the constructed original pair.
All applicability premises, the identity K₂=L₂, and the exclusion of the
product alternative are proved here or by the original local construction. -/
theorem exists_original_R1_linear_amalgam
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
      (normalizer (L : Set G)).subtype = L)
    (h1347 : PlaneAmalgamSource1347 D m) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      X ∈ Chapter1.HOver G (T : Set G) ∧ LinearAmalgamConclusion T X := by
  obtain ⟨W,hW,hT,hP,hB,hqP,hqB,_,_,hchief,hiP,hiB,hne,_,hexclude,hcentral⟩ :=
    exists_original_R1_amalgam_inputs h₀ h structural D m hcase z hz hzL
      hout hfusion h1339 hsolv hindex h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  have hc := h1347 W hW hT P hP hB hqP hqB hne
    (original_second_flag_residual_eq_inner D m W hT)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB
    (fun hx => by
      obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral hx.1
      exact ⟨h₁,h₂,Or.inl hr⟩)
  exact ⟨W,hW,hT,hc.1,hc.2.resolve_left hexclude⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
