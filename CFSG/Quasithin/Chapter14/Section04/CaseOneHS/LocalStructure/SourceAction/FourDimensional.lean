module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.G2Exclusion
public import Theory.GroupTheory.CoprimeSubgroupLift

public import Theory.SpecificGroups.SymmetricSix.Parabolics.PointCubicPlane
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.Representation.BinarySymplecticFourEmbedding
public import Theory.Alternating.Aut

/-!
# Excluding A₆ and S₆ from the original four-dimensional HS action

A cubic fixing the marked point and lying in the image of C_H(Z(U)) lifts
through a two-group kernel to a cubic centralizing V₂. The full centralizer
of V₂ normalizes W and W^g, hence their actual intersection E. In dimension
four the previously proved order calculation gives E = V.

If the faithful symplectic image contains A₆, that simple normal subgroup
centralizes Z(U) in the dotted image: the normal closure of Z(U)^g is
nontrivial, centralizes Z(U), and meets every self-centralizing simple normal
subgroup. The concrete cubic point-stabilizer calculation then moves an
isotropic plane, contradicting preservation of E. The resulting order
obstruction excludes both A₆ and S₆ with any faithful symplectic marking.

The final theorem applies this to the existing alternatives on the original
rank-three flag. The four-dimensional solvable/A₅ identification and the
whole-component recognition still remain; this is not ActionStructure.
Centerlessness is the preceding premise, owned by qt-d-hs-local-structure.
Source: Aschbacher--Smith 14.3.23(2)(iii) and 14.3.32, printed pp.1000,1004.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem plane_centralizer_normalizes_intersection (F : InvariantFlag T V 3)
    (g : G) (hg : g ∈ F.Gi 2) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (F.E g : Set G) := by
  have hCH : centralizer (F.Vi 2 : Set G) ≤ F.H :=
    (centralizer_le (F.monotone (by decide : 1≤2))).trans (Subgroup.centralizer_le_normalizer _)
  have hCW : centralizer (F.Vi 2 : Set G) ≤ normalizer (F.W : Set G) :=
    (le_inf (hCH.trans (le_normalizer_conjugateSpanBy V F.H))
      (centralizer (F.Vi 2 : Set G)).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hCg : conjugate (centralizer (F.Vi 2 : Set G)) g = centralizer (F.Vi 2 : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge (conjugate_centralizer_le _ _ hg)
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hCX : centralizer (F.Vi 2 : Set G) ≤ normalizer (F.X g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCW
    rw [map_equiv_normalizer_eq] at hh
    exact hCg ▸ hh
  exact (le_inf hCW hCX).trans inf_normalizer_le_normalizer_inf

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- A cubic point fixer in the center-centralizing image preserves the literal intersection E. -/
theorem source_point_cube_preserves_intersection
    (v : Additive F.Uhat) (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (g : G) (hgP : g ∈ F.P L)
    (a : F.TerminalHdot)
    (ha : a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : a ∈ F.terminalDot (centralizer (F.ZU : Set G))) (ha3 : a^3=1)
    (w : Additive F.Uhat) (hw : w ∈ hatSpace F (F.E g)) :
    F.terminalRepresentation a w ∈ hatSpace F (F.E g) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let D := C.map q
  let f : C →* D := q.subgroupMap C
  have hk : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ (pCore 2 F.H).subgroupOf C := by
      intro x hx
      apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
      exact ⟨x.property,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
    exact (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf C)).to_le hle
  let aa : D := ⟨a,haZ⟩
  have hao : orderOf aa ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext ha3)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card (zpowers aa)) := by
    rw [hn,Nat.card_zpowers]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).coprime_dvd_right hao
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel (q.subgroupMap_surjective C)
    (zpowers aa) hcop
  let b : C := s ⟨aa,mem_zpowers aa⟩
  have hb3 : b^3=1 := by
    rw [← map_pow]
    have hh : (⟨aa,mem_zpowers aa⟩ : zpowers aa)^3=1 := Subtype.ext (Subtype.ext ha3)
    rw [hh,map_one]
  have hba : q b.val = a := by
    have hh : f b = aa := DFunLike.congr_fun hs (⟨aa,mem_zpowers aa⟩ : zpowers aa)
    exact congrArg Subtype.val hh
  have hbplane : (b.val:G) ∈ centralizer (F.Vi 2 : Set G) :=
    source_point_preimage_centralizes_plane_of_cube_one d earlier hq chosen structural alternatives
      F hne v hline b.val (hba.symm ▸ ha) b.property (congrArg Subtype.val hb3)
  have hbn := plane_centralizer_normalizes_intersection F g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hbplane
  obtain ⟨x,hx,he⟩ := (show w.toMul ∈ hatImage F (F.E g) from hw)
  refine ⟨F.uAction b.val x,(mem_normalizer_iff.mp hbn (x:G)).mp hx,?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b.val x) = _
  rw [← F.uhatAction_apply_mk,he]
  change F.terminalRepresentation (q b.val) w = F.terminalRepresentation a w
  rw [hba]
open Theory.SpecificGroups.SymmetricSix

/-- The original four-dimensional action cannot contain the full alternating
six-group in its symplectic coordinates. -/
theorem source_no_alternating_six_image
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
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
  have hKC := source_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  have hE := source_intersection_eq_seed_of_card_sixteen d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hdim : finrank (ZMod 2) (hatSpace F (F.E g)) = 2 := by
    rw [hE]
    exact seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2
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

/-- Every original degree-four HS action has literal symplectic coordinates
whose six-letter image omits A₆. This excludes both source A₆/S₆ rows. -/
theorem source_four_symplectic_embedding_of_centerless
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
    ∃ c : B.IsometryEquiv polarForm,
    ∃ j : F.TerminalHdot →* Equiv.Perm (Fin 6), Function.Injective j ∧
      (∀ a w, c (F.terminalRepresentation a w) = polarAction (j a) (c w)) ∧
      ¬ alternatingGroup (Fin 6) ≤ j.range := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hd : finrank (ZMod 2) (Additive F.Uhat)=4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide) (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
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
  exact ⟨B,c',j',hj',he',source_no_alternating_six_image d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH B v hyp hline.symm j' hj' c' he'⟩

/-- The original four-space excludes both A₆ and S₆ by their literal order,
without assuming any particular marking of either group. -/
theorem source_four_card_not_multiple_of_360
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16) : ¬ 360 ∣ Nat.card F.TerminalHdot := by
  intro h360
  obtain ⟨B,c,j,hj,_,hn⟩ := source_four_symplectic_embedding_of_centerless
    d earlier hq chosen structural alternatives F hne hZ hI hc
  have hjc : Nat.card j.range = Nat.card F.TerminalHdot :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hi := j.range.index_mul_card
  rw [s6_order] at hi
  have hd : 360 ≤ Nat.card j.range := by
    rw [hjc]
    exact Nat.le_of_dvd (Nat.card_pos) h360
  have hip : 0 < j.range.index := Nat.pos_of_ne_zero j.range.index_ne_zero_of_finite
  have hi2 : j.range.index ≤ 2 := by nlinarith
  apply hn
  by_cases h1 : j.range.index = 1
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · let : j.range.Normal := normal_of_index_eq_two (by omega)
    let : Nontrivial j.range := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simp) inferInstance

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The original HS alternatives, with both alternating-six four-space rows
excluded and the remaining whole-component obligations unchanged. -/
theorem source_four_or_whole_recognition_of_centerless (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((CaseTwo F.terminalRepresentation B ∧ ¬ 360 ∣ Nat.card F.TerminalHdot) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_four_or_whole_action_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with hfour | hwhole
  · have hc : Nat.card F.Uhat = 16 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
      change Nat.card F.Uhat = _ at hh
      simpa only [Nat.card_zmod,hfour.1,show (2 : ℕ)^4=16 by decide] using hh
    exact .inl ⟨hfour,source_four_card_not_multiple_of_360 d earlier hq chosen
      structural alternatives F hne hZ hI hc⟩
  · exact .inr hwhole

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
