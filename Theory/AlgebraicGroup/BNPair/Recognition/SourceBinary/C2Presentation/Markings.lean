module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Weyl
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Recognition
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility
public import Theory.SpecificGroups.SymplecticFour.BorelLocalCover
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.Quasithin.EvenCharacteristic

/-!
# The full marked symplectic comparison on the same finite quotient

The proved presentation and the internally established quotient order greater
than two construct a root-preserving equivalence with the whole Sp₄. Positive
generation identifies U; its normalizer identifies the full Borel. Local
characteristic two places each source parabolic inside one model parabolic,
and the two negative-root witnesses select the orientation. Source maximality
then upgrades each inclusion to equality. Restrictions of this single ambient
equivalence give both endpoint squares and the whole common-Borel map.
The PSp output uses the literal central quotient projection.

Source: DGS, Groups and Graphs, row II(a) p.209 and Theorem D p.224;
Steinberg §6, pp.68–74. Source field reconstruction and mixed-root equations
remain with the source recognition owner, as specified by RootData.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.RootPresentation
open Representation.OneCohomology.SymplecticFour
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
variable {P : Fin 2 → Subgroup X} {Q : MarkedQuotient P} {split : SplitData Q.tits}
namespace RootData
variable (d : RootData (F := F) Q split)

/-- Recognition of this very quotient, from its literal eight-root relations. -/
def equiv : (X ⧸ Q.D) ≃* Sp F := d.relations.modelEquiv d.generate (two_lt_card Q)

@[simp] theorem equiv_root (r : Fin 8) (t : F) :
    d.equiv (d.x r (.ofAdd t)) = rootElement r t := d.relations.modelEquiv_root _ _ r t

/-- Positive generation identifies the entire source unipotent group. -/
theorem map_unipotent : split.U.map d.equiv.toMonoidHom = unipotent (F := F) := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨b,k,w,v,he⟩ := d.positive_normal_form u hu
    rw [← he]
    simp only [map_mul,equiv_root,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe]
    exact mul_mem (mul_mem (mul_mem (positive_root_mem_unipotent 6 b (by simp))
      (positive_root_mem_unipotent 0 k (by simp))) (positive_root_mem_unipotent 4 w (by simp)))
      (positive_root_mem_unipotent 2 v (by simp))
  · intro u hu
    obtain ⟨⟨b,k,w,v⟩,he⟩ := CentralRootGeometry.element_surjective ⟨u,hu⟩
    refine ⟨d.x 6 (.ofAdd b) * d.x 0 (.ofAdd (k+b*w)) * d.x 4 (.ofAdd w) * d.x 2 (.ofAdd v),
      mul_mem (mul_mem (mul_mem (d.positive_root_mem 6 (by simp) b)
        (d.positive_root_mem 0 (by simp) _)) (d.positive_root_mem 4 (by simp) w))
        (d.positive_root_mem 2 (by simp) v),?_⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,map_mul,equiv_root,
      CentralRootGeometry.element] using congrArg Subtype.val he

/-- The full Borel, including its odd torus, is recovered as the U normalizer. -/
theorem map_borel : Q.tits.B.map d.equiv.toMonoidHom = borel (F := F) := by
  rw [← split.normalizer_eq,map_normalizer_eq_of_bijective _ d.equiv.bijective,
    d.map_unipotent,← borel_eq_normalizer_unipotent]

omit [Finite F] [CharP F 2] in
private theorem negative_long_not_plane : rootElement (K := F) 3 1 ∉ planeParabolic := by
  intro h
  have he := (mem_planeParabolic_iff _).mp h 1 1
  change (rootMatrix 3 (1 : F)) (.inr 1) (.inl 1) = 0 at he
  simp [rootMatrix,Matrix.fromBlocks,Matrix.single] at he

omit [Finite F] [CharP F 2] in
private theorem negative_short_not_point : rootElement (K := F) 7 1 ∉ pointParabolic := by
  intro h
  have he := ((mem_pointParabolic_iff _).mp h).1
  change (rootMatrix 7 (1 : F)) (.inl 1) (.inl 0) = 0 at he
  simp [rootMatrix,Matrix.fromBlocks,Matrix.single] at he

variable (hc : ∀ i : Fin 2,
  centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
    Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))

include hc in
private theorem mapped_characteristicTwo (i : Fin 2) :
    centralizer (pCore 2 ((Q.tits.standardParabolic {Q.simple i}).map d.equiv.toMonoidHom) :
      Set ((Q.tits.standardParabolic {Q.simple i}).map d.equiv.toMonoidHom)) ≤
      pCore 2 ((Q.tits.standardParabolic {Q.simple i}).map d.equiv.toMonoidHom) :=
  (Theory.Quasithin.centralizer_pCore_le_iff 2 (d.equiv.subgroupMap _)).mp (hc i)

include hc in
/-- Source maximality and the negative long root select the full point parabolic. -/
theorem map_point : (Q.tits.standardParabolic {Q.simple 0}).map d.equiv.toMonoidHom =
    pointParabolic (F := F) := by
  let J := (Q.tits.standardParabolic {Q.simple 0}).map d.equiv.toMonoidHom
  have hmax : IsCoatom J := (OrderIso.isCoatom_iff d.equiv.mapSubgroup _).mpr (Q.parabolic_isCoatom 0)
  have hb : borel (F := F) ≤ J := d.map_borel ▸ map_mono (Q.tits.B_le_standardParabolic _)
  have hle : J ≤ pointParabolic := by
    rcases borel_overgroup_parabolic_of_characteristicTwo J hb (d.mapped_characteristicTwo hc 0) with hp|hp
    · exact hp
    · exact (negative_long_not_plane (hp (d.equiv_root 3 1 ▸ mem_map_of_mem d.equiv.toMonoidHom d.negative_long))).elim
  have hp : (pointParabolic (F := F)) ≠ ⊤ := by
    intro he
    exact negative_short_not_point (he ▸ mem_top _)
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hmax).2 _ hp hle)

include hc in
/-- The negative short root fixes the other orientation; both maps use one e. -/
theorem map_plane : (Q.tits.standardParabolic {Q.simple 1}).map d.equiv.toMonoidHom =
    planeParabolic (F := F) := by
  let J := (Q.tits.standardParabolic {Q.simple 1}).map d.equiv.toMonoidHom
  have hmax : IsCoatom J := (OrderIso.isCoatom_iff d.equiv.mapSubgroup _).mpr (Q.parabolic_isCoatom 1)
  have hb : borel (F := F) ≤ J := d.map_borel ▸ map_mono (Q.tits.B_le_standardParabolic _)
  have hle : J ≤ planeParabolic := by
    rcases borel_overgroup_parabolic_of_characteristicTwo J hb (d.mapped_characteristicTwo hc 1) with hp|hp
    · exact (negative_short_not_point (hp (d.equiv_root 7 1 ▸ mem_map_of_mem d.equiv.toMonoidHom d.negative_short))).elim
    · exact hp
  have hp : (planeParabolic (F := F)) ≠ ⊤ := by
    intro he
    exact negative_long_not_plane (he ▸ mem_top _)
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hmax).2 _ hp hle)

/-- The literal PSp carrier and its actual central quotient map. -/
def projectiveEquiv : (X ⧸ Q.D) ≃* (Sp F ⧸ center (Sp F)) :=
  d.equiv.trans EvenProjective.equiv

@[simp] theorem projectiveEquiv_root (r : Fin 8) (t : F) :
    d.projectiveEquiv (d.x r (.ofAdd t)) = QuotientGroup.mk (rootElement r t) := by
  change EvenProjective.equiv (d.equiv _) = _
  rw [d.equiv_root,EvenProjective.equiv_apply]

include hc in
/-- The same markings on the literal PSp quotient, through its actual projection. -/
theorem projective_subgroup_images :
    Q.tits.B.map d.projectiveEquiv.toMonoidHom =
      (borel (F := F)).map (QuotientGroup.mk' (center (Sp F))) ∧
    (Q.tits.standardParabolic {Q.simple 0}).map d.projectiveEquiv.toMonoidHom =
      (pointParabolic (F := F)).map (QuotientGroup.mk' (center (Sp F))) ∧
    (Q.tits.standardParabolic {Q.simple 1}).map d.projectiveEquiv.toMonoidHom =
      (planeParabolic (F := F)).map (QuotientGroup.mk' (center (Sp F))) := by
  have he : d.projectiveEquiv.toMonoidHom =
      (QuotientGroup.mk' (center (Sp F))).comp d.equiv.toMonoidHom := by
    ext g
    exact EvenProjective.equiv_apply _
  simp only [he,← Subgroup.map_map,d.map_borel,d.map_point hc,d.map_plane hc,and_self]

omit [Finite F] [CharP F 2] in
/-- The point/whole-Borel/plane inclusion amalgam. -/
def flagAmalgam (F : Type*) [Field F] :
    RankTwoAmalgam (pointParabolic (F := F)) (borel (F := F)) (planeParabolic (F := F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Restrict the one constructed ambient equivalence to all three subgroups. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F) where
  left := (d.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr (d.map_point hc))
  middle := (d.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr d.map_borel)
  right := (d.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr (d.map_plane hc))
  left_commutes b := by
    apply Subtype.ext
    change d.equiv (Q.standardAmalgam.left b : X ⧸ Q.D) = d.equiv b
    apply congrArg d.equiv
    obtain ⟨a,rfl⟩ := Q.markedIso.middle.surjective b
    rw [← Q.markedIso.left_commutes,Q.markedIso_left_apply,Q.markedIso_middle_apply]
    rfl
  right_commutes b := by
    apply Subtype.ext
    change d.equiv (Q.standardAmalgam.right b : X ⧸ Q.D) = d.equiv b
    apply congrArg d.equiv
    obtain ⟨a,rfl⟩ := Q.markedIso.middle.surjective b
    rw [← Q.markedIso.right_commutes,Q.markedIso_right_apply,Q.markedIso_middle_apply]
    rfl

@[simp] theorem markedIso_left_apply (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((d.markedIso hc).left a : Sp F) = d.equiv a := rfl

@[simp] theorem markedIso_middle_apply (b : Q.tits.B) :
    ((d.markedIso hc).middle b : Sp F) = d.equiv b := rfl

@[simp] theorem markedIso_right_apply (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((d.markedIso hc).right a : Sp F) = d.equiv a := rfl

/-- The comparison from the actual original numerator, retaining Q.q. -/
def quotientMarkedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
    (flagAmalgam F) := Q.markedIso.trans (d.markedIso hc)

@[simp] theorem quotientMarkedIso_left_apply (a : P 0) :
    ((d.quotientMarkedIso hc).left a : Sp F) = d.equiv (Q.q a) := by
  change d.equiv (Q.markedIso.left a : X ⧸ Q.D) = _
  rw [Q.markedIso_left_apply]

@[simp] theorem quotientMarkedIso_middle_apply (b : (P 0 ⊓ P 1 : Subgroup X)) :
    ((d.quotientMarkedIso hc).middle b : Sp F) = d.equiv (Q.q b) := by
  change d.equiv (Q.markedIso.middle b : X ⧸ Q.D) = _
  rw [Q.markedIso_middle_apply]

@[simp] theorem quotientMarkedIso_right_apply (a : P 1) :
    ((d.quotientMarkedIso hc).right a : Sp F) = d.equiv (Q.q a) := by
  change d.equiv (Q.markedIso.right a : X ⧸ Q.D) = _
  rw [Q.markedIso_right_apply]
end RootData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
