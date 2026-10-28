module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SourceAmalgam

/-!
# The original solvable pair has its local action quotient

Apply the nontrivial-core argument to the constructed invariant plane and
original pair IT,L₂T. Locality discharges the antecedent in its checked
fixed-subgroup centralizer calculation. This gives the two literal
intersections, relative normality and the prime-to-three residual identity.

The same pair's omega-center span is reduced. Its full action kernel lies
in the first vertex, since the full kernel centralizes that vertex's fixed
line. The local kernel theorem therefore proves C_X(V₀)=O₂(X). Finally F.6.6
identifies O²(X) with the join of the two original residuals, and F.6.5(1)
constructs the Goldschmidt triple in the literal quotient X/O₂(X).

All premises retained here are the earlier-source premises of the checked
original pair. No part of `PlaneAmalgamSource1347` is assumed. The four
structural alternatives, their exclusions and the linear overgroup formula
remain necessary before this can supply that proposition and recognition.
Source: Aschbacher–Smith, 13.4.7, printed pp.899–900, applied to the original
13.4.9 pair on p.906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original pair is local and outside M, with its actual reduced module,
full action kernel, residual generation and quotient amalgam constructed. -/
theorem exists_original_R1_local_action
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
      let X := P ⊔ B
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      let V₀ := conjugateSpanBy Z X
      X ∈ Chapter1.HOver G (T : Set G) ∧
      ¬ X ≤ normalizer (L : Set G) ∧
      P ⊓ B = (T : Subgroup G) ∧
      X ⊓ normalizer (L : Set G) = B ∧ X ⊓ H = P ∧
      C₁ = P ∧ C₂ = B ∧
      (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∧
      (pResidual 2 X).map X.subtype = K₁ ⊔ K₂ ∧
      IsPReduced 2 (V₀.subgroupOf X) ∧
      X ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 ∧
      ChapterF.IsGoldschmidtTriple
        ((P.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
        ((B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  obtain ⟨W,hW,hT,hP,hB,hqP,hqB,_,_,_,hiP,hiB,hne,_,_,hcentral⟩ :=
    exists_original_R1_amalgam_inputs h₀ h structural D m hcase z hz hzL
      hout hfusion h1339 hsolv hindex h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V₀ := conjugateSpanBy Z X
  have hlocal := original_pair_local D m hP.2 hB.2 hqP.some hqB.some hne hiP hiB
  obtain ⟨hXM,hXH,hC₁,hC₂,hn₁,hn₂,hr⟩ := hcentral hlocal.1
  obtain ⟨hred,hkernelP,_,_⟩ := original_pair_action_kernel
    h₀ D m hP.2 hB.2 hqP.some hqB.some hne hiP hiB
  change P ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 at hkernelP
  have hkerle : X ⊓ centralizer (V₀ : Set G) ≤ P := by
    apply le_trans ?_ hC₁.le
    exact inf_le_inf_left X (centralizer_le (inf_le_left.trans (le_conjugateSpanBy Z X)))
  have hkernel : X ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 := by
    apply le_antisymm
    · rw [←hkernelP]
      exact le_inf hkerle inf_le_right
    · exact le_inf (X.pCoreIn_le 2) (hkernelP.symm.le.trans inf_le_right)
  have hg := pair_goldschmidt hP.2 hB.2 hqP.some hqB.some hne
  have hres := congrArg (Subgroup.map X.subtype) hg.twoResidual_eq_sup
  rw [Subgroup.map_sup, map_embedded_pResidual, map_embedded_pResidual,
    map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right] at hres
  have hinter : P ⊓ B = (T : Subgroup G) :=
    intersection_eq_sylow hP.2 hB.2 hqP.some hqB.some hne
  have hnotM : ¬ X ≤ normalizer (L : Set G) := by
    intro hx
    have hXB : X = B := (inf_eq_left.mpr hx).symm.trans hXM
    have hPB : P ≤ B := le_sup_left.trans hXB.le
    have hPT : P = (T : Subgroup G) := (inf_eq_left.mpr hPB).symm.trans hinter
    have hi : (T : Subgroup G).relIndex P = 3 :=
      SymmetricThreeTwoCore.sylow_index_three hqP.some (T.subtype hP.2)
    rw [←hPT,relIndex_self] at hi
    omega
  exact ⟨W,hW,hT,hlocal,hnotM,hinter,
    hXM,hXH,hC₁,hC₂,hn₁,hn₂,hr,hres,hred,hkernel,hg.quotient_twoCore⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
