module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.NonsolvableFive
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FourDimensional

/-!
# The symmetric-six centerlessness contradiction

Assuming the original center is nontrivial, the shifted involution has
nontrivial hatted action and its H-normal closure centralizes Z(U).
Consequently every self-centralizing simple normal subgroup of the literal
dotted quotient lies in the image of C_H(Z(U)). In the S6 row this applies
to A6. Cubics fixing the marked point then preserve the original isotropic
intersection plane. The concrete A6 point-stabilizer calculation moves such
a plane, a contradiction. This uses the earlier four-dimensional geometry
and no result whose centerlessness premise remains undischarged.

The preceding seed exclusion is constructed from the literal S6 model.
The final combined consumer covers S5, A6 and S6 and retains the independent
ActionStructure premise. The G2 and Goldschmidt contradictions and the
exhaustive earlier alternatives remain with this owner. Import directly:
the earlier point-action extension is above the lower Centerless umbrella.
Source: Aschbacher--Smith 14.3.23--25 and 14.3.28--31, pp.1000--1003;
the cubic-plane calculation gives an alternative to the A.3.18 step in
14.3.31, using the same original subgroups and action quotient.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

omit [IsElementaryAbelian 2 F.Uhat] in
/-- The shifted involution forces a self-centralizing simple normal subgroup
into the literal center-centralizing action image in the contrary branch. -/
theorem source_contrary_simple_normal_le_center_centralizer
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (K : Subgroup F.TerminalHdot) [K.Normal] [IsSimpleGroup K]
    (hKa : ¬ IsMulCommutative K) (hKc : centralizer (K : Set F.TerminalHdot) = ⊥) :
    K ≤ F.terminalDot (centralizer (F.ZU : Set G)) := by
  obtain ⟨g,l,e,hgL,hgP,hgH,hlL,hl,hspace,hgen,he,heI,heT,heU,heV,
    haH,ha,hfaith,_,hNC,_⟩ :=
    source_shifted_amalgam_faithful d earlier hq chosen structural alternatives F hne hseed hI
  let a := l⁻¹ * e * l
  let N := conjugateSpanBy (zpowers a) F.H
  have hNH : N ≤ F.H := conjugateSpanBy_le_self (zpowers_le.mpr haH)
  let : (N.subgroupOf F.H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : (F.terminalDot N).Normal := Normal.map inferInstance
    (QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hN : F.terminalDot N ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' F.terminalHatAction.ker ⟨a,haH⟩ ∈ F.terminalDot N :=
      mem_map_of_mem _ (le_conjugateSpanBy _ _ (mem_zpowers a))
    have hh := (QuotientGroup.eq_one_iff (⟨a,haH⟩ : F.H)).mp (mem_bot.mp (hbot ▸ hmem))
    exact hfaith hh
  exact (simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc _ hN).trans
    (map_mono (comap_mono hNC))

/-- The contrary center forces point cubics to preserve a plane that the
actual alternating-six action moves. -/
theorem source_no_alternating_six_image_of_contrary_center
    (hseed : centralLTSeed F L = ⊥) (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (c : B.IsometryEquiv polarForm)
    (he : ∀ a w, c (F.terminalRepresentation a w) = polarAction (j a) (c w)) :
    ¬ alternatingGroup (Fin 6) ≤ j.range := by
  intro hA
  let K := (alternatingGroup (Fin 6)).comap j
  have hmap : K.map j = alternatingGroup (Fin 6) := by
    change ((alternatingGroup (Fin 6)).comap j).map j = _
    exact map_comap_eq_self hA
  let eK := (K.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : K.Normal := inferInstanceAs (((alternatingGroup (Fin 6)).comap j).Normal)
  have hKa : ¬ IsMulCommutative K := by
    intro hab
    let := hab
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective)
  have hKc : centralizer (K : Set F.TerminalHdot) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply hj
    rw [map_one]
    apply mem_bot.mp
    rw [← _root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)]
    intro a ha
    obtain ⟨k,hk,rfl⟩ := (show a ∈ K.map j from hmap.symm ▸ ha)
    exact (map_mul j k x).symm.trans ((congrArg j (hx k hk)).trans (map_mul j x k))
  have hKC := source_contrary_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
    F hne hseed hI K hKa hKc
  obtain ⟨_,_,hdim,_⟩ := source_four_marked_geometry d earlier hq chosen structural alternatives
    F hne hd g hgP hgH
  let W := (hatSpace F (F.E g)).map c.toLinearEquiv.toLinearMap
  have hWdim : finrank (ZMod 2) W=2 := (c.toLinearEquiv.finrank_map_eq _).trans hdim
  have hiso : ∀ x∈W, ∀ y∈W, polarForm x y=0 := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    change polarForm (c x) (c y)=0
    rw [c.map_app]
    exact hyp.isotropic x hx y hy
  have hv : c v ≠ 0 := fun hz => hyp.point_ne_zero (c.injective (hz.trans c.map_zero.symm))
  obtain ⟨a,ha3,hav,w,hw,haw⟩ := PointCubicPlane.exists_matrix_cubic (c v) hv W hWdim hiso
    ⟨v,hyp.point_mem,rfl⟩
  obtain ⟨b,hb⟩ := hA a.property
  have hbK : b ∈ K := by change j b ∈ alternatingGroup (Fin 6); rw [hb]; exact a.property
  have hb3 : b^3=1 := by
    apply hj
    rw [map_pow,hb,map_one]
    exact congrArg Subtype.val ha3
  have hbv : b ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
    apply c.injective
    change c (F.terminalRepresentation b v)=c v
    rw [he,hb]
    exact hav
  obtain ⟨x,hx,rfl⟩ := hw
  apply haw
  change polarAction a.val (c x) ∈ W
  rw [←hb,←he]
  exact ⟨F.terminalRepresentation b x,
    source_point_cube_preserves_intersection d earlier hq chosen structural alternatives F hne
      v hline g hgP b hbv (hKC hbK) hb3 x hx,rfl⟩


omit [IsElementaryAbelian 2 F.Uhat] in
/-- The S6 row of the original centerlessness theorem, with its seed row constructed. -/
theorem source_centerless_of_symmetricSix_model
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  have hseed := source_seed_exclusion_of_six_model d earlier hq chosen structural alternatives
    classification F hne hc (.inr model)
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hd : finrank (ZMod 2) (Additive F.Uhat)=4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨c,j,hj,he⟩ := exists_binarySymplecticFour_embedding F.terminalRepresentation
    hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  have hform : Matrix.PSp4Three.form (n := 2) (F := ZMod 2)=polarForm := by
    unfold Matrix.PSp4Three.form polarForm
    congr 1
    ext i k
    exact ZMod.neg_eq_self_mod_two _
  let c' : B.IsometryEquiv polarForm := { c.toLinearEquiv with
    map_app' := fun x y => by rw [←hform]; exact c.map_app y x }
  let j' := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  have hj' : Function.Injective j' :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj
  have he' : ∀ a w, c' (F.terminalRepresentation a w) = polarAction (j' a) (c' w) := by
    intro a w
    have heq : polarRepresentation (j' a)=j a := by
      rw [← Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
      exact Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply (j a)
    change c (F.terminalRepresentation a w) = polarAction (j' a) (c w)
    rw [← polarRepresentation_apply,heq]
    exact he a w
  have hnot := source_no_alternating_six_image_of_contrary_center d earlier hq chosen structural alternatives
    F hne hseed hI hd g hgP hgH B v hyp hline.symm j' hj' c' he'
  obtain ⟨e⟩ := model
  have hsur : Function.Surjective j' := by
    have h := Finite.surjective_of_injective (hj'.comp e.symm.injective)
    intro a
    obtain ⟨b,hb⟩ := h a
    exact ⟨e.symm b,hb⟩
  apply hnot
  rw [MonoidHom.range_eq_top.mpr hsur]
  exact le_top

omit [IsElementaryAbelian 2 F.Uhat] in
/-- Apply the proved S6 centerlessness branch to the literal LocalStructure consumer. -/
theorem localStructure_of_symmetricSix_model_action
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6)))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_symmetricSix_model d earlier hq chosen structural alternatives
      F hne classification hc model) action

omit [IsElementaryAbelian 2 F.Uhat] in
/-- All three original nonsolvable four-space rows imply centerlessness,
with their marked seed rows and seed exclusions constructed. -/
theorem source_centerless_of_four_nonsolvable_model
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  rcases model with h5 | h6 | hS
  · exact source_centerless_of_symmetricFive_model d earlier hq chosen structural alternatives
      classification F hne hZ hc h5
  · exact source_centerless_of_alternatingSix_model d earlier hq chosen structural alternatives
      classification F hne hc h6
  · exact source_centerless_of_symmetricSix_model d earlier hq chosen structural alternatives
      F hne classification hc hS

omit [IsElementaryAbelian 2 F.Uhat] in
/-- Literal LocalStructure application of the complete nonsolvable
four-dimensional centerlessness family. -/
theorem localStructure_of_four_nonsolvable_model_action
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6)))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_four_nonsolvable_model d earlier hq chosen structural alternatives
      F hne classification hZ hc model) action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
