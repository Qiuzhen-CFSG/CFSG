module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.OriginalLocalAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines
public import Theory.GroupTheory.Commutator.ResidualImage
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original pair reaches the noncommuting action branch

Apply the fixed-line and residual-kernel arguments to the invariant plane
and literal pair IT,L₂T constructed by the solvable branch. Its relative
centralizer equalities prove escape from M and the two normalizer bounds.
The full seed is V∩Ω₁Z(T), of order four, and splits into the two residual
fixed lines. The full action kernel is O₂(X) and has order prime to three;
the two-residual of X is its prime-to-three residual.

Finally, if the two residual images in X/O₂(X) commuted, normalization
would lift across the two-group kernel and give [K₁,K₂]≤O₂(K₁). This
contradicts the checked original-pair exclusion. Thus this is the literal
noncommuting branch on p.900, without assuming PlaneAmalgamSource1347.
The remaining structural alternatives, their exclusions and the overgroup
supplement still have to be proved before applying OriginalSource.

Source: Aschbacher–Smith 13.4.7, pp.899–900, and the pair in 13.4.9, p.906.
Earlier Chapter 12/13.3 and 13.4.2–3 premises retain their original contracts.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem commutator_bound_of_quotient (X A B : Subgroup G)
    (hAX : A ≤ X) (hBX : B ≤ X) (hp : IsPPerfect 2 A)
    (hn : X.pCoreIn 2 ≤ normalizer (A : Set G))
    (hc : ⁅(A.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)),
      (B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))⁆ = ⊥) :
    ⁅A,B⁆ ≤ A.pCoreIn 2 := by
  let e := (subgroupOfEquivOfLe hAX).symm
  have hp' : IsPPerfect 2 (A.subgroupOf X) := hp.of_surjective e.toMonoidHom e.surjective
  have hn' : pCore 2 X ≤ normalizer (A.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hAX]
    intro x hx
    exact hn (mem_map_of_mem X.subtype hx)
  have hc' := commutator_le_pCoreIn_of_commuting_images
    (QuotientGroup.mk' (pCore 2 X)) (A.subgroupOf X) (B.subgroupOf X) hp'
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by simpa only [QuotientGroup.ker_mk'] using hn') hc
  have hm := map_mono (f := X.subtype) hc'
  rwa [map_commutator,map_subgroupOf_eq_of_le hAX,map_subgroupOf_eq_of_le hBX,
    pCoreIn_subgroupOf 2 A X hAX,map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans hAX)] at hm

/-- The original plane pair has two fixed lines and noncommuting residual action images. -/
theorem exists_original_R1_fixed_action
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
      let F₁ := Z ⊓ centralizer (K₁ : Set G)
      let F₂ := Z ⊓ centralizer (K₂ : Set G)
      let V₀ := conjugateSpanBy Z X
      X ∈ Chapter1.HOver G (T : Set G) ∧
      Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
      Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) ∧
      Nat.card F₁ = 2 ∧ Nat.card F₂ = 2 ∧ F₁ ⊓ F₂ = ⊥ ∧ F₁ ⊔ F₂ = Z ∧
      X ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 ∧
      Nat.Coprime 3 (Nat.card (X ⊓ centralizer (V₀ : Set G) : Subgroup G)) ∧
      X.pCoreIn 2 ≤ normalizer (K₁ : Set G) ⊓ normalizer (K₂ : Set G) ∧
      (pResidual 2 X).map X.subtype = (primeToResidual 3 X).map X.subtype ∧
      ⁅(K₁.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)),
        (K₂.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))⁆ ≠ ⊥ := by
  obtain ⟨W,hW,hT,hP,hB,hqP,hqB,_,_,_,hiP,hiB,hne,_,hexclude,hcentral⟩ :=
    exists_original_R1_amalgam_inputs h₀ h structural D m hcase z hz hzL
      hout hfusion h1339 hsolv hindex h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let K₁ := (pResidual 2 P).map P.subtype
  let K₂ := (pResidual 2 B).map B.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V₀ := conjugateSpanBy Z X
  have hK₁X : K₁ ≤ X := (map_subtype_le _).trans le_sup_left
  have hK₂X : K₂ ≤ X := (map_subtype_le _).trans le_sup_right
  have hlocal := original_pair_local D m hP.2 hB.2 hqP.some hqB.some hne hiP hiB
  obtain ⟨hXM,_,hC₁,_,hn₁,hn₂,hr⟩ := hcentral hlocal.1
  have hnotM : ¬ X ≤ normalizer (L : Set G) := by
    intro hx
    have hXB : X = B := (inf_eq_left.mpr hx).symm.trans hXM
    have hPB : P ≤ B := le_sup_left.trans hXB.le
    have hPT : P = (T : Subgroup G) := (inf_eq_left.mpr hPB).symm.trans
      (intersection_eq_sylow hP.2 hB.2 hqP.some hqB.some hne)
    have hi : (T : Subgroup G).relIndex P = 3 :=
      SymmetricThreeTwoCore.sylow_index_three hqP.some (T.subtype hP.2)
    rw [←hPT,relIndex_self] at hi
    omega
  have hdist := pair_fixed_subgroups_ne hP.2 hB.2 hqP.some hqB.some hne (Or.inl hr)
  obtain ⟨hZ,hF₁,hF₂,hinf,hsup,hZL⟩ :=
    original_pair_fixed_lines h structural D m hnotM hindex hiP hiB hdist
  have hfix₁ := omega_fixed_twoResidual P hP.2
  have hfix₂ := omega_fixed_twoResidual B hB.2
  change Z ⊓ centralizer (K₁ : Set G) = Z ⊓ centralizer (P : Set G) at hfix₁
  change Z ⊓ centralizer (K₂ : Set G) = Z ⊓ centralizer (B : Set G) at hfix₂
  obtain ⟨_,hkernelP,_,_⟩ := original_pair_action_kernel h₀ D m
    hP.2 hB.2 hqP.some hqB.some hne hiP hiB
  change P ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 at hkernelP
  have hkerle : X ⊓ centralizer (V₀ : Set G) ≤ P := by
    apply le_trans ?_ hC₁.le
    exact inf_le_inf_left X (centralizer_le (inf_le_left.trans (le_conjugateSpanBy Z X)))
  have hkernel : X ⊓ centralizer (V₀ : Set G) = X.pCoreIn 2 := by
    apply le_antisymm
    · rw [←hkernelP]
      exact le_inf hkerle inf_le_right
    · exact le_inf (X.pCoreIn_le 2) (hkernelP.symm.le.trans inf_le_right)
  have hnorm₁ := kernel_normalizes_residual X Z K₁ hK₁X hn₁
  have hnorm₂ := kernel_normalizes_residual X Z K₂ hK₂X hn₂
  rw [hkernel] at hnorm₁ hnorm₂
  have hcop := original_pair_kernel_primeToThree h₀ D m hP.2 hB.2 hqP.some hqB.some
    hne hiP hiB (Or.inl hr)
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  have hseed := (original_R1_full_seed h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342).1
  refine ⟨W,hW,hT,hlocal,hseed,hZ,hZL,?_,?_,?_,?_,hkernel,hcop,
    le_inf hnorm₁ hnorm₂,pair_twoResidual_eq_primeToThree hP.2 hB.2 hqP.some hqB.some hne,?_⟩
  · change Nat.card (Z ⊓ centralizer (K₁ : Set G) : Subgroup G) = 2
    rw [hfix₁]
    exact hF₁
  · change Nat.card (Z ⊓ centralizer (K₂ : Set G) : Subgroup G) = 2
    rw [hfix₂]
    exact hF₂
  · change (Z ⊓ centralizer (K₁ : Set G)) ⊓ (Z ⊓ centralizer (K₂ : Set G)) = ⊥
    rw [hfix₁,hfix₂]
    exact hinf
  · change (Z ⊓ centralizer (K₁ : Set G)) ⊔ (Z ⊓ centralizer (K₂ : Set G)) = Z
    rw [hfix₁,hfix₂]
    exact hsup
  · intro hc
    exact hexclude (commutator_bound_of_quotient X K₁ K₂ hK₁X hK₂X
      (isPPerfect_embedded_pResidual 2 P) hnorm₁ hc)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
