module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ReflectionPinning

/-!
# Recovering a whole source pinning from its local marking

A whole SL₂ pinning carrying the upper root onto the specified simple root and
Weyl matrix to the specified source reflection can be recovered by the existing
canonical pinning construction. Use its inverse and the original panel
projection to define the local PSL₂ marking. The canonical Sylow equivalences
are conjugations; hence their upper-root coordinates differ by a scalar.
Reflection alignment preserves this scalar form, and the rank-one braid at
parameter one forces the scalar to be one. Upper roots and the Weyl matrix
generate SL₂, so the entire pinnings agree.

This makes the common-field relabeling usable by every existing source root,
torus and Weyl calculation without assuming naturality of classical choices.
It includes the binary and four-element fields. NormalizedRelations applies
it to the complete long pinning constructed from the middle coefficient.

Source: Fong--Seitz II §7 and (9.13)--(9.14), printed pp.192,215--216.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open MulAction in
private theorem sylow_conj {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P Q : Sylow p G) : ∃ g : G, ∀ x : P, (P.equiv Q x : G) = g*x*g⁻¹ := by
  classical
  let g := Classical.choose (exists_smul_eq G P Q)
  have hg : g • P = Q := Classical.choose_spec (exists_smul_eq G P Q)
  refine ⟨g, ?_⟩
  have hh (Q' : Sylow p G) (he : g • P = Q') (x : P) :
      ((Eq.mpr (congrArg (fun T : Sylow p G => P ≃* T) he.symm)
        (P.equivSMul g)) x : G) = g*x*g⁻¹ := by
    cases he
    rfl
  exact hh Q hg

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private theorem sylow_coordinates_conj (T : Sylow 2 PSL(2,F)) :
    ∃ g : SL2 F, ∀ a : F,
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T (.ofAdd a) : PSL(2,F)) =
        BenderSuzuki.ZD.Linear.sl2QuotientEquiv F (g*uni a*g⁻¹) := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  let e := BenderSuzuki.ZD.Linear.sl2QuotientEquiv F
  let V := U.mapSurjective e.surjective
  obtain ⟨c,hc⟩ := sylow_conj U U
  obtain ⟨b,hb⟩ := sylow_conj V T
  refine ⟨e.symm b*c, ?_⟩
  intro a
  dsimp only [BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive, MulEquiv.trans_apply]
  rw [hb]
  have he : e (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 U (.ofAdd a)) =
      e (c*uni a*c⁻¹) := congrArg e (hc ⟨uni a,⟨.ofAdd a,rfl⟩⟩)
  change b * e (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 U (.ofAdd a)) * b⁻¹ = _
  rw [he]
  change b * e (c*uni a*c⁻¹) * b⁻¹ = e ((e.symm b*c)*uni a*(e.symm b*c)⁻¹)
  simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  group

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F))
  (n : RootReflection Q split i)
  (p : SL2 F ≃* rankOne Q split i)

/-- The local marking obtained from a specified whole rank-one pinning. -/
def localMarkingOfPinning : localGroup Q split i ≃* PSL(2,F) :=
  (rankOnePanelEquiv Q split i hV μ).symm.trans
    (p.symm.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F))

private theorem localMarkingOfPinning_projection (g : SL2 F) :
    localMarkingOfPinning Q split i hV μ p (RootLocalCover.projection Q split i (p g)) =
      BenderSuzuki.ZD.Linear.sl2QuotientEquiv F g := by
  change BenderSuzuki.ZD.Linear.sl2QuotientEquiv F
    (p.symm ((rankOnePanelEquiv Q split i hV μ).symm
      ((rankOnePanelEquiv Q split i hV μ) (p g)))) = _
  simp only [MulEquiv.symm_apply_apply]

/-- A pinning preserving the actual upper root and specified reflection is
recovered exactly by the existing canonical construction, with its induced local marking. -/
theorem alignedPinning_recovers
    (hU : (Unip F).map ((rankOne Q split i).subtype.comp p.toMonoidHom) = simpleRoot Q split i)
    (hw : (p (weyl F) : X ⧸ Q.D) = n.val) :
    alignedPinning Q split i hV (localMarkingOfPinning Q split i hV μ p) n = p := by
  let ν := localMarkingOfPinning Q split i hV μ p
  let f := (rankOne Q split i).subtype.comp p.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp p.injective
  obtain ⟨g,hg⟩ := sylow_coordinates_conj (linearSylow Q split i ν)
  have hsp (a : F) : simpleParameter Q split i hV ν (.ofAdd a) = f (g*uni a*g⁻¹) := by
    suffices he : inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)
        (simpleRootFieldEquiv Q split i hV ν (.ofAdd a)) = p (g*uni a*g⁻¹) from
      congrArg Subtype.val he
    apply rankOne_projection_injective Q split i hV μ
    apply ν.injective
    have hproj (u : simpleRoot Q split i) :
        RootLocalCover.projection Q split i (inclusion (show simpleRoot Q split i ≤
          rankOne Q split i from le_sup_left) u) = simpleRootLocalMap Q split i u := by
      apply Subtype.ext
      rw [RootLocalCover.projection_apply,localAction_eq_panelAction,simpleRootLocalMap_apply]
      rfl
    rw [hproj]
    have he := simpleRootFieldEquiv_model Q split i hV ν (.ofAdd a)
    rw [hg] at he
    exact he.trans (localMarkingOfPinning_projection Q split i hV μ p _).symm
  have hgU : g*uni (1:F)*g⁻¹ ∈ Unip F := by
    have hm : f (g*uni (1:F)*g⁻¹) ∈ simpleRoot Q split i := by
      rw [←hsp]
      exact (simpleRootFieldEquiv Q split i hV ν (.ofAdd 1)).property
    rw [←hU] at hm
    obtain ⟨u,hu,he⟩ := hm
    exact hf he ▸ hu
  obtain ⟨t,ht⟩ := (mem_Unip_iff _).mp hgU
  have hgB : g ∈ Borel F := by
    rw [mem_Borel_iff]
    have hh : g*uni (1:F) = uni t*g := by rw [←ht]; group
    have he := congrArg (fun x : SL2 F => x.val 1 1) hh
    simpa [Matrix.mul_apply,Fin.sum_univ_two] using he
  let a := (alignedPinning Q split i hV ν n).trans p.symm
  have ha (t : F) : a (uni t) =
      uni (g.val 0 0^2 * (((alignmentMatrix Q split i hV ν n)⁻¹).val 0 0^2*t)) := by
    apply p.injective
    apply Subtype.val_injective
    dsimp only [a,MulEquiv.trans_apply]
    rw [p.apply_symm_apply]
    change alignedSimpleParameter Q split i hV ν n (.ofAdd t) = _
    rw [alignedSimpleParameter_scaling,hsp,Borel_conj_uni hgB]
    rfl
  have haU : (Unip F).map a.toMonoidHom = Unip F := by
    apply Subgroup.map_injective hf
    rw [map_map]
    have he : f.comp a.toMonoidHom = alignedPinningHom Q split i hV ν n := by
      ext x
      exact congrArg Subtype.val (p.apply_symm_apply _)
    rw [he,alignedPinningHom_unip_map,hU]
  have haw : a (weyl F) = weyl F := by
    apply p.injective
    apply Subtype.val_injective
    change (p (p.symm _):X ⧸ Q.D) = _
    rw [p.apply_symm_apply]
    change alignedPinningHom Q split i hV ν n (weyl F) = _
    exact (alignedPinningHom_weyl Q split i hV ν n).trans hw.symm
  have hscalar : g.val 0 0^2 * ((alignmentMatrix Q split i hV ν n)⁻¹).val 0 0^2 = 1 := by
    have hh := rootParameter_one a haU haw
    simpa [rootParameter,ha] using hh
  have hai : a.toMonoidHom = MonoidHom.id _ := by
    apply sl2_hom_ext_root_weyl
    · intro t
      change a (uni t)=uni t
      rw [ha,←mul_assoc,hscalar,one_mul]
    · exact haw
  ext x
  have he := DFunLike.congr_fun hai x
  have hp := congrArg p he
  simpa only [a,MulEquiv.trans_apply,MonoidHom.id_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using congrArg Subtype.val hp
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
