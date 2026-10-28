module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.SourceSylow.Application

/-!
# The G.2.5 kernel and product on the original conjugate span

Instantiate the completed G.2.5 structure theorems with the original flag.
The three marked conjugates generate the full span I=LU. Restriction of the
literal star kernel identifies C_I(V) with O₂(I), which normalizes U.
The ordered product of U∩O₂(I) and its two marked conjugates is transported
into I itself, exactly as required by the source Sylow constructor.

The natural quotient action is constructed from the same restricted star map,
and its actual action on V is retained. `NaturalSetup.Frame` adapts these
coordinates to the ordered flag. The radical images and complement are
subsequent 14.4.7 steps.

Source: Aschbacher--Smith, G.2.5 and 14.4.7, printed pp.335--336,1009.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
open LargerDimension.RankCore.GaschutzComplement


/-- The original Frattini calculation supplies the second explicit G.2.2 input. -/
theorem source_frattini (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    (frattini F.U).map F.U.subtype ≤ F.Vi 1 := by
  obtain ⟨_, he, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  rw [he, map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
    (F.le_seed 1).trans (le_conjugateSpanBy V F.H))]

private theorem span_eq_of_g25 (F : InvariantFlag T V 3) (g l : G)
    (B : ChapterG.Section02.LinearThree.Hypothesis (sourceSetup F L) (ZMod 2) 1 g l)
    (hUT : F.U ≤ (T : Subgroup G))
    (hphi : (frattini F.U).map F.U.subtype ≤ F.Vi 1) :
    conjugateSpan F.U L = ChapterG.Section02.LinearThree.I (sourceSetup F L) g l := by
  apply le_antisymm
  · apply iSup_le
    intro x
    exact conjugate_le_of_normalizes
      (show F.U ≤ ChapterG.Section02.LinearThree.I (sourceSetup F L) g l from
        le_sup_left.trans le_sup_left) x
      ((ChapterG.Section02.LinearThree.I (sourceSetup F L) g l).le_normalizer
        (B.L_le_I hUT hphi x.property))
  · exact sup_le (sup_le (le_conjugateSpan F.U L)
      (conjugate_le_span F.U L B.g_mem)) (conjugate_le_span F.U L B.h_mem)

/-- Apply G.2.5 to the original flag: the entire L-conjugate closure is LU. -/
theorem source_span_eq (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugateSpan F.U L = L ⊔ F.U := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  exact (span_eq_of_g25 F g l B hUT hphi).trans (B.I_eq_LU hUT hphi)

/-- The literal restricted centralizer is exactly O₂(I), not O₂(LT).
This discharges the kernel premise of the source Sylow construction. -/
theorem source_span_kernel (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (centralizer (V : Set G)).subgroupOf (conjugateSpan F.U L) =
      pCore 2 (conjugateSpan F.U L) := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  rw [span_eq_of_g25 F g l B hUT hphi]
  apply Subgroup.map_injective (ChapterG.Section02.LinearThree.I (sourceSetup F L) g l).subtype_injective
  change _ = ChapterG.Section02.LinearThree.S (sourceSetup F L) g l
  rw [subgroupOf_map_subtype, inf_comm, B.S_eq_star_kernel hUT hphi]
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact (higherRankHypothesis d earlier hq chosen).centralizer_LT structural ▸
      (show x ∈ (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from
        ⟨B.I_le_LT hUT hx.1, hx.2⟩)
  · exact inf_le_inf_left _ chosen.core_centralizes

/-- Normalization of U by the actual two-core, in the exact restricted carrier
used by `source_complement_of_g25`. -/
theorem source_span_core_normalizes (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    pCore 2 (conjugateSpan F.U L) ≤
      normalizer (F.U.subgroupOf (conjugateSpan F.U L) : Set (conjugateSpan F.U L)) := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  rw [span_eq_of_g25 F g l B hUT hphi]
  intro x hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  exact Subgroup.mem_normalizer_iff.mp (B.S_normalizes_U hUT hphi
    (mem_map_of_mem _ hx)) u.val

omit [Finite G] in
private theorem restricted_product (I A B C : Subgroup G)
    (hA : A ≤ I.pCoreIn 2) (hB : B ≤ I.pCoreIn 2) (hC : C ≤ I.pCoreIn 2)
    (h : (I.pCoreIn 2 : Set G) = (A : Set G) * (B : Set G) * (C : Set G)) :
    (pCore 2 I : Set I) = (A.subgroupOf I : Set I) * (B.subgroupOf I : Set I) *
      (C.subgroupOf I : Set I) := by
  have mem_core (x : I) : x ∈ pCore 2 I ↔ (x : G) ∈ I.pCoreIn 2 :=
    (mem_map_iff_mem (f := I.subtype) I.subtype_injective).symm
  ext x
  change x ∈ pCore 2 I ↔ _
  rw [mem_core]
  change (x : G) ∈ (I.pCoreIn 2 : Set G) ↔ _
  rw [h]
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, he⟩
    exact ⟨⟨a * b, I.mul_mem (I.pCoreIn_le 2 (hA ha)) (I.pCoreIn_le 2 (hB hb))⟩,
      ⟨⟨a, I.pCoreIn_le 2 (hA ha)⟩, ha, ⟨b, I.pCoreIn_le 2 (hB hb)⟩, hb, rfl⟩,
      ⟨c, I.pCoreIn_le 2 (hC hc)⟩, hc, Subtype.ext he⟩
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, he⟩
    exact ⟨(a : G) * b, ⟨a, ha, b, hb, rfl⟩, c, hc, congrArg Subtype.val he⟩

/-- Restrict G.2.5's ordered kernel product to the actual conjugate span,
retaining both supplied transporters. This allows the frame and product to
be constructed with the same third point. -/
theorem marked_span_core_product (F : InvariantFlag T V 3) (g l : G)
    (B : ChapterG.Section02.LinearThree.Hypothesis (sourceSetup F L) (ZMod 2) 1 g l)
    (hUT : F.U ≤ (T : Subgroup G))
    (hphi : (frattini F.U).map F.U.subtype ≤ F.Vi 1) :
    let I := conjugateSpan F.U L
    (pCore 2 I : Set I) =
      (F.U.subgroupOf I ⊓ pCore 2 I : Set I) *
      ((rightConjugate F.U g).subgroupOf I ⊓ pCore 2 I : Set I) *
      ((rightConjugate F.U l).subgroupOf I ⊓ pCore 2 I : Set I) := by
  dsimp only
  rw [span_eq_of_g25 F g l B hUT hphi]
  let D := sourceSetup F L
  let I := ChapterG.Section02.LinearThree.I D g l
  have hprod := B.S_eq_product hUT hphi
  rw [ChapterG.Section02.LinearThree.conjugate_W D g l g (B.L_le_I hUT hphi B.g_mem),
    ChapterG.Section02.LinearThree.conjugate_W D g l l (B.L_le_I hUT hphi B.h_mem)] at hprod
  have hh := restricted_product I (F.U ⊓ I.pCoreIn 2)
    (rightConjugate F.U g ⊓ I.pCoreIn 2) (rightConjugate F.U l ⊓ I.pCoreIn 2)
    inf_le_right inf_le_right inf_le_right hprod
  have hsub : (I.pCoreIn 2).subgroupOf I = pCore 2 I := by
    change ((pCore 2 I).map I.subtype).comap I.subtype = _
    exact comap_map_eq_self_of_injective I.subtype_injective _
  have hinf (A : Subgroup G) : (A ⊓ I.pCoreIn 2).subgroupOf I =
      A.subgroupOf I ⊓ pCore 2 I := by
    change A.comap I.subtype ⊓ (I.pCoreIn 2).subgroupOf I = _
    rw [hsub]
    rfl
  simpa only [hinf, coe_inf, Set.inf_eq_inter, I, D] using hh

/-- The source's third transporter and ordered kernel factorization on the
actual conjugate span. The first factor is U∩O₂(I), distinct from C_U(V₂). -/
theorem source_span_core_product (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      let I := conjugateSpan F.U L
      (pCore 2 I : Set I) =
        (F.U.subgroupOf I ⊓ pCore 2 I : Set I) *
        ((rightConjugate F.U g).subgroupOf I ⊓ pCore 2 I : Set I) *
        ((rightConjugate F.U l).subgroupOf I ⊓ pCore 2 I : Set I) := by
  obtain ⟨l, hl, hlP, hplane, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  refine ⟨l, hl, hlP, hplane, ?_⟩
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  exact marked_span_core_product F g l B hUT hphi

/-- Normalization of the original seed by its full conjugate span. -/
theorem source_span_normalizes (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugateSpan F.U L ≤ normalizer (V : Set G) := by
  rw [source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH]
  exact sup_le chosen.normalizes
    ((source_closure_le_sylow d earlier hq chosen structural alternatives F).trans
      (F.last ▸ F.invariant 3))

/-- The actual quotient I/O₂(I) acts naturally on V through the restricted
star projection. This constructs the action before adapting its coordinates
to the ordered flag (V₁ᵍ,V₁,V₁ˡ). -/
theorem source_span_natural_action (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ (hIV : conjugateSpan F.U L ≤ normalizer (V : Set G))
      (m : SourceNaturalAction (conjugateSpan F.U L) V hIV),
      Function.Surjective m.actor ∧ m.actor.ker = pCore 2 (conjugateSpan F.U L) := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  rw [span_eq_of_g25 F g l B hUT hphi]
  let I := ChapterG.Section02.LinearThree.I (sourceSetup F L) g l
  let e := B.sourceCoreQuotientEquiv hUT hphi
  let a : I →* Matrix.PSL3Two.SL := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let m : SourceNaturalAction I V (B.I_normalizes hUT) := {
    actor := a
    space := B.coordinates
    intertwines := B.sourceCoreQuotientEquiv_equivariant hUT hphi }
  refine ⟨B.I_normalizes hUT, m,
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext i
  change e (QuotientGroup.mk' (pCore 2 I) i) = 1 ↔ i ∈ pCore 2 I
  rw [← e.map_one, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
