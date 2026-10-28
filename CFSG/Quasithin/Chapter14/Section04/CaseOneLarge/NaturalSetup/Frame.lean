module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Kernel
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Basis

/-!
# The actual natural frame in the last paragraph of 14.4.7

Choose a basis on the three original marked points in the order
(V₁ᵍ,V₁,V₁ˡ). Conjugating the constructed SL₃(2) action by this basis
preserves its literal conjugation on V and identifies V₂ with the first
coordinate plane. The same transporter l is retained in G.2.5's ordered
kernel product. Both quotient maps and the kernel O₂(I) are the original ones.

The resulting frame is a genuine input to the existing source Sylow theorem.
Its action is onto SL₃(2), and the plane-centralizer calculation identifies
C_I(V₂) with the preimage of the actual pointwise plane fixer. Identifying
the two radical images and completing the complement remain subsequent steps.

Source: Aschbacher--Smith, 14.4.7, printed p.1009, using G.2.5,
printed pp.335--336; refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.RankCore.GaschutzComplement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem basis_line_mem (b : Basis (Fin 3) (ZMod 2) (Fin 3 → ZMod 2))
    (w : Fin 3 → ZMod 2) (i : Fin 3) :
    w ∈ Submodule.span (ZMod 2) {b i} ↔ ∀ j, j ≠ i → b.equivFun w j = 0 := by
  constructor
  · intro hw j hji
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [Ne.symm hji]
  · intro hw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b.equivFun w i, b.equivFun.injective ?_⟩
    ext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, hw j (Ne.symm hij)]

private theorem basis_plane_mem (b : Basis (Fin 3) (ZMod 2) (Fin 3 → ZMod 2))
    (w : Fin 3 → ZMod 2) :
    w ∈ Submodule.span (ZMod 2) {b 0} ⊔ Submodule.span (ZMod 2) {b 1} ↔
      b.equivFun w 2 = 0 := by
  constructor
  · intro hw
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    have ha2 := (basis_line_mem b a 0).mp ha 2 (by decide)
    have hc2 := (basis_line_mem b c 1).mp hc 2 (by decide)
    simp only [map_add, Pi.add_apply, ha2, hc2, add_zero]
  · intro hw
    apply Submodule.mem_sup.mpr
    refine ⟨b.equivFun w 0 • b 0, Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),
      b.equivFun w 1 • b 1, Submodule.smul_mem _ _ (Submodule.subset_span (by simp)), ?_⟩
    apply b.equivFun.injective
    ext i
    fin_cases i <;> simp [hw]

omit [Finite G] in
private theorem space_sup_mem [IsMulCommutative V]
    (e : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (A B : Subgroup G) (P Q : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hAV : A ≤ V) (hBV : B ≤ V)
    (hA : ∀ v : V, (v : G) ∈ A ↔ (e v).toAdd ∈ P)
    (hB : ∀ v : V, (v : G) ∈ B ↔ (e v).toAdd ∈ Q) (v : V) :
    (v : G) ∈ A ⊔ B ↔ (e v).toAdd ∈ P ⊔ Q := by
  have hn : B ≤ normalizer (A : Set G) := by
    apply (show B ≤ centralizer (A : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact congrArg Subtype.val (mul_comm (⟨a,hAV ha⟩ : V) ⟨b,hBV hb⟩)
  have hp : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    coe_mul_of_right_le_normalizer_left A B hn
  constructor
  · intro hv
    have hm : (v : G) ∈ (A : Set G) * (B : Set G) := hp ▸ hv
    obtain ⟨a,ha,b,hb,he⟩ := hm
    have he' : v = (⟨a,hAV ha⟩ : V) * ⟨b,hBV hb⟩ := Subtype.ext he.symm
    rw [he',map_mul,toAdd_mul]
    exact Submodule.mem_sup.mpr ⟨_,(hA _).mp ha,_,(hB _).mp hb,rfl⟩
  · intro hv
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
    let va := e.symm (Multiplicative.ofAdd a)
    let vb := e.symm (Multiplicative.ofAdd b)
    have hva : (va : G) ∈ A := (hA va).mpr (by simpa [va] using ha)
    have hvb : (vb : G) ∈ B := (hB vb).mpr (by simpa [vb] using hb)
    have he' : va * vb = v := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      simpa [va,vb] using he
    exact he' ▸ (A ⊔ B).mul_mem (mem_sup_left hva) (mem_sup_right hvb)

omit [Finite G] in
private def changeCoordinates {I : Subgroup G} {hIV : I ≤ normalizer (V : Set G)}
    (m : SourceNaturalAction I V hIV)
    (E : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    SourceNaturalAction I V hIV where
  actor := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    ((MulAut.conj E).toMonoidHom.comp
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom.comp m.actor))
  space := m.space.trans E.toAddEquiv.toMultiplicative
  intertwines := by
    intro x v
    change E ((m.space (V.normalizerMonoidHom (inclusion hIV x) v)).toAdd) =
      (BinaryLinear.OuterCyclic.slEquivLinear 3
        ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm
          ((MulAut.conj E) (BinaryLinear.OuterCyclic.slEquivLinear 3 (m.actor x)))))
        (E (m.space v).toAdd)
    rw [MulEquiv.apply_symm_apply, m.intertwines]
    change E ((BinaryLinear.OuterCyclic.slEquivLinear 3 (m.actor x)) (m.space v).toAdd) =
      E ((BinaryLinear.OuterCyclic.slEquivLinear 3 (m.actor x)) (E.symm (E (m.space v).toAdd)))
    rw [E.symm_apply_apply]

/-- Adapt the genuine natural action to the original marked lines, in the
order used by the source Sylow theorem. No coordinate premise is assumed. -/
theorem source_natural_frame (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      ∃ hIV : conjugateSpan F.U L ≤ normalizer (V : Set G),
        ∃ m : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV,
          Function.Surjective m.actor ∧
          m.actor.ker = pCore 2 (conjugateSpan F.U L) ∧
          (let I := conjugateSpan F.U L
           (pCore 2 I : Set I) =
             (F.U.subgroupOf I ⊓ pCore 2 I : Set I) *
             ((rightConjugate F.U g).subgroupOf I ⊓ pCore 2 I : Set I) *
             ((rightConjugate F.U l).subgroupOf I ⊓ pCore 2 I : Set I)) ∧
          ∀ x : conjugateSpan F.U L, (x : G) ∈ centralizer (F.Vi 2 : Set G) ↔
            m.actor x ∈ Matrix.PSL3Two.SourceFlag.planeFixer := by
  let := chosen.elementary
  obtain ⟨l,hl,hlP,hplane,⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  let D := sourceSetup F L
  let I := ChapterG.Section02.LinearThree.I D g l
  have hspan : conjugateSpan F.U L = I :=
    (source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH).trans
      (B.I_eq_LU hUT hphi).symm
  let hIV := source_span_normalizes d earlier hq chosen structural alternatives F hne g hg hgP hgH
  let eI := MulEquiv.subgroupCongr hspan
  let e := B.sourceCoreQuotientEquiv hUT hphi
  let a : conjugateSpan F.U L →* Matrix.PSL3Two.SL :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 I)).comp eI.toMonoidHom)
  let m : SourceNaturalAction (conjugateSpan F.U L) V hIV := {
    actor := a
    space := B.coordinates
    intertwines := fun x v => B.sourceCoreQuotientEquiv_equivariant hUT hphi (eI x) v }
  let pg := Matrix.PSL3.PointRadicalGeneration.conjugatePoint B.point
    (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨g,hg⟩))
  let pl := Matrix.PSL3.PointRadicalGeneration.conjugatePoint B.point
    (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨l,hl⟩))
  let frame : Matrix.SpecialLinearGroup.FrameGeometry.Frame (ZMod 2) := {
    point := ![pg,B.point,pl]
    dimension := by
      intro i
      fin_cases i
      · exact (Matrix.PSL3.PointRadicalGeneration.conjugatePoint_finrank _ _).trans B.point_dimension
      · exact B.point_dimension
      · exact (Matrix.PSL3.PointRadicalGeneration.conjugatePoint_finrank _ _).trans B.point_dimension
    disjoint := B.model_points_disjoint.symm
    third_disjoint := by
      change Disjoint (pg ⊔ B.point) pl
      rw [sup_comm pg B.point]
      exact B.model_third_disjoint
    span := by
      change (pg ⊔ B.point) ⊔ pl = ⊤
      rw [sup_comm pg B.point]
      exact B.model_points_span }
  obtain ⟨b,hb⟩ := frame.exists_basis
  have hb0 : Submodule.span (ZMod 2) {b 0} = pg := hb 0
  have hb1 : Submodule.span (ZMod 2) {b 1} = B.point := hb 1
  have hb2 : Submodule.span (ZMod 2) {b 2} = pl := hb 2
  let m' := changeCoordinates m b.equivFun
  have h0 (v : V) : (v : G) ∈ conjugate (F.Vi 1) g ↔
      b.equivFun (B.coordinates v).toAdd 1 = 0 ∧ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    have hp : (v : G) ∈ conjugate (F.Vi 1) g ↔ (B.coordinates v).toAdd ∈ pg :=
      (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm
    rw [hp, ← hb0, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have h1 (v : V) : (v : G) ∈ F.Vi 1 ↔
      b.equivFun (B.coordinates v).toAdd 0 = 0 ∧ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    rw [B.point_mem, ← hb1, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have h2 (v : V) : (v : G) ∈ conjugate (F.Vi 1) l ↔
      b.equivFun (B.coordinates v).toAdd 0 = 0 ∧ b.equivFun (B.coordinates v).toAdd 1 = 0 := by
    have hp : (v : G) ∈ conjugate (F.Vi 1) l ↔ (B.coordinates v).toAdd ∈ pl :=
      (B.model_conjugatePoint_mem ⟨l,hl⟩ v).symm
    rw [hp, ← hb2, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have hAV := conjugate_le_of_normalizes (F.le_seed 1) g (chosen.normalizes hg)
  have hplane' (v : V) : (v : G) ∈ F.Vi 2 ↔ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    rw [← hplane, sup_comm]
    rw [space_sup_mem B.coordinates _ _ pg B.point hAV (F.le_seed 1)
      (fun v => (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm) B.point_mem,
      ← hb0, ← hb1, basis_plane_mem]
  let f : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV := {
    toSourceNaturalAction := m'
    plane_le := F.le_seed 2
    plane := hplane'
    line_g := h0
    line_one := h1
    line_l := h2
    line_g_le := hAV
    line_one_le := F.le_seed 1
    line_l_le := conjugate_le_of_normalizes (F.le_seed 1) l (chosen.normalizes hl) }
  refine ⟨l,hl,hlP,hIV,f, ?_, ?_, marked_span_core_product F g l B hUT hphi, ?_⟩
  · exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
      ((MulAut.conj b.equivFun).surjective.comp
        ((BinaryLinear.OuterCyclic.slEquivLinear 3).surjective.comp
          (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eI.surjective))))
  · exact f.toSourceNaturalAction.ker_eq.trans
      (source_span_kernel d earlier hq chosen structural alternatives F hne g hg hgP hgH)
  · exact f.toSourceNaturalAction.centralizer_plane (F.Vi 2) f.plane_le f.plane
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

