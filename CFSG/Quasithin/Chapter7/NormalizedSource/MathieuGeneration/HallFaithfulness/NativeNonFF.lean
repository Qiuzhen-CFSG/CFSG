module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadicalNormalizer
public import Theory.GroupTheory.ThompsonNormalizerGrowth
public import Theory.GroupTheory.ElementaryThompsonElementaryCore

/-!
# Non-FF transport through the original containing component

The literal component inclusion and central quotient are bijective on the
original module. Conjugating its automorphism groups through those bijections
transfers the original non-FF assumption to the native residual normalizer.
For M₁₂ its elementary module centralizer is the Sylow Thompson subgroup.
The normalizer condition then promotes that local Sylow to a full J₄ Sylow.
All component centers and the original residual/module maps are retained.

Source: Aschbacher–Smith B.2.5–8, 4.2.13 and 4.4.14,
printed pp.76,611–612,624–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterD.UniqueFactor

private theorem image_ff_map_iff {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (C E : Subgroup G) (hn : C ≤ normalizer (E : Set G))
    [IsElementaryAbelian 2 E] (hi : Function.Injective (f.subgroupMap E))
    :
    letI : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map f
    IsFFModule (imageRepresentation C E hn) ↔
      IsFFModule (imageRepresentation (C.map f) (E.map f)
        ((map_mono hn).trans (E.le_normalizer_map f))) := by
  let : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map f
  let e : E ≃* E.map f := MulEquiv.ofBijective (f.subgroupMap E)
    ⟨hi,f.subgroupMap_surjective E⟩
  let hn' := (map_mono hn).trans (E.le_normalizer_map f)
  let a := actionHom C E hn
  let b := actionHom (C.map f) (E.map f) hn'
  have he (g : C) : MulAut.congr e (a g) = b (f.subgroupMap C g) := by
    apply MulEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := e.surjective v
    apply Subtype.ext
    change f ((g : G) * (e.symm (e w) : G) * (g : G)⁻¹) =
      f g * (e w : Q) * (f g)⁻¹
    rw [e.symm_apply_apply]
    exact (map_mul f _ _).trans (congrArg₂ (· * ·) (map_mul f _ _) (map_inv f _))
  let ψ : a.range →* b.range :=
    { toFun x := ⟨MulAut.congr e x.val, by
        obtain ⟨g,hg⟩ := x.property
        exact ⟨f.subgroupMap C g,(he g).symm.trans (congrArg (MulAut.congr e) hg)⟩⟩
      map_one' := by apply Subtype.ext; exact map_one _
      map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _ }
  have hψi : Function.Injective ψ := by
    intro x y hh
    exact Subtype.ext ((MulAut.congr e).injective (congrArg Subtype.val hh))
  have hψs : Function.Surjective ψ := by
    rintro ⟨_,g,rfl⟩
    obtain ⟨c,rfl⟩ := f.subgroupMap_surjective C g
    exact ⟨⟨a c,⟨c,rfl⟩⟩,Subtype.ext (he c)⟩
  let d := MulEquiv.ofBijective ψ ⟨hψi,hψs⟩
  let l : Additive (E.map f) ≃ₗ[ZMod 2] Additive E :=
    LinearEquiv.ofBijective (e.symm.toMonoidHom.toAdditive.toZModLinearMap 2) e.symm.bijective
  constructor
  · intro hh
    let l' : Additive E ≃ₗ[ZMod 2] Additive (E.map f) :=
      LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
    apply hh.map_equivariant _ _ d.toMonoidHom d.injective l'
    intro x v
    change e (x.val v.toMul) = e (x.val (e.symm (e v.toMul)))
    rw [e.symm_apply_apply]
  intro hh
  apply hh.map_equivariant _ _ d.symm.toMonoidHom d.symm.injective l
  intro x v
  obtain ⟨y,rfl⟩ := d.surjective x
  change e.symm ((MulAut.congr e y.val) v.toMul) =
    (d.symm (d y)).val (e.symm v.toMul)
  rw [d.symm_apply_apply]
  exact e.symm_apply_apply _

private theorem image_ff_congr {X : Type*} [Group X]
    {C E C' E' : Subgroup X} [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 E']
    (hC : C = C') (hE : E = E') (hn : C ≤ normalizer (E : Set X))
    (hn' : C' ≤ normalizer (E' : Set X)) :
    IsFFModule (imageRepresentation C E hn) ↔ IsFFModule (imageRepresentation C' E' hn') := by
  subst C'
  subst E'
  rfl

private theorem automizer_ff_congr {X : Type*} [Group X]
    {E E' : Subgroup X} [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 E']
    (he : E = E') :
    IsFFModule (ChapterE.automizerRepresentation E) ↔
      IsFFModule (ChapterE.automizerRepresentation E') := by
  subst E'
  rfl

open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The literal native residual normalizer inherits non-FF from the original
ambient module, through the complete central cover and its faithful module image. -/
theorem sourceOrbit_pushingUp_native_nonFF
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    letI : IsElementaryAbelian 2 E :=
      (D.sourceOrbit_pushingUp_native_radical hfix hw K hK e).2.2.2.2.2.2.1
    ¬ IsFFModule (imageRepresentation (normalizer (B : Set Janko4.Model)) E
      (D.sourceOrbit_pushingUp_native_normalizer_core h hV hfix hm hw K hK e).2.2.2) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  let Ek := V.comap j
  let Ck := M.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  let d : Ek ≃* V := (Ek.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hEV)
  let := D.elementary
  let : IsElementaryAbelian 2 Ek := IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  have hc := hw.2.2.2.2.2.2.1
  have hMF : M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  have hn : Ck ≤ normalizer (Ek : Set K) :=
    ((comap_mono hMF).trans (F.le_normalizer_comap j)).trans
      (D.sourceOrbit_pushingUp_cover_module_normalizer h hV hfix hm hw K hK e)
  have hnoV : ¬ IsFFModule (ChapterE.automizerRepresentation V) := by
    intro hh
    exact D.sourceOrbit_automizer_nonFF h hnon ((automizer_ff_congr hV).mp hh)
  let : IsElementaryAbelian 2 (Ek.map j) := IsElementaryAbelian.map j
  let : IsElementaryAbelian 2 (Ek.map q) := IsElementaryAbelian.map q
  have n : Ck.map j ≤ normalizer (V : Set G) := by
    rw [←hEV]
    exact (map_mono hn).trans (Ek.le_normalizer_map j)
  have hnoj' : ¬ IsFFModule (imageRepresentation (Ck.map j) V n) := by
    intro hh
    apply hnoV
    let i : ChapterD.internalActionImage (Ck.map j) V n →* ChapterE.Automizer V :=
      inclusion (by
        rintro _ ⟨x,rfl⟩
        exact ⟨inclusion n x,rfl⟩)
    exact hh.map_equivariant _ _ i (inclusion_injective _)
      (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hnoj : ¬ IsFFModule (imageRepresentation (Ck.map j) (Ek.map j)
      ((map_mono hn).trans (Ek.le_normalizer_map j))) := fun hh =>
    hnoj' ((image_ff_congr rfl hEV _ n).mp hh)
  have hnj : ¬ IsFFModule (imageRepresentation Ck Ek hn) := by
    intro hh
    exact hnoj ((image_ff_map_iff j Ck Ek hn (by
      intro x y he
      apply Subtype.ext
      apply hj
      exact congrArg (fun z : Ek.map j => (z : G)) he)).mp hh)
  have hnat := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hnat
  have hiq : Function.Injective (q.subgroupMap Ek) :=
    ((q.subgroupMap_surjective Ek).bijective_of_nat_card_le
      ((Nat.card_congr d.toEquiv).le.trans hnat.2.2.2.2.2.2.2.1.symm.le)).1
  have hnoq : ¬ IsFFModule (imageRepresentation (Ck.map q) (Ek.map q)
      ((map_mono hn).trans (Ek.le_normalizer_map q))) := by
    intro hh
    exact hnj ((image_ff_map_iff q Ck Ek hn hiq).mpr hh)
  have hN := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have heC : Ck.map q = normalizer ((F.comap j).map q : Set Janko4.Model) := hN.1.symm
  dsimp only
  intro hh
  exact hnoq ((image_ff_congr heC rfl _ _).mpr hh)


/-- The M12 native residual normalizer contains a full ambient Sylow, whose
Thompson subgroup is precisely the same elementary radical. -/
theorem sourceOrbit_pushingUp_m12_native_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let B := (F.comap j).map q
    ∃ P : Sylow 2 Janko4.Model,
      (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
        Stellmacher.elementaryAbelianMaxJ (P : Subgroup Janko4.Model) = U := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  let C := normalizer (B : Set Janko4.Model)
  have hn := D.sourceOrbit_pushingUp_native_normalizer_core h hV hfix (.inl hm) hw K hK e
  have hU := D.sourceOrbit_pushingUp_m12_native_radical_normalizer h hV hfix hm hw K hK e
  change C.pCoreIn 2 = U ∧ normalizer (U : Set Janko4.Model) = C ∧
    centralizer (U : Set Janko4.Model) = U at hU
  have hC := D.sourceOrbit_pushingUp_m12_module_centralizer h hV hfix hm hw K hK e
  have hnat := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  let : IsElementaryAbelian 2 E := hnat.2.2.2.2.2.2.1
  let : IsElementaryAbelian 2 U :=
    (D.sourceOrbit_pushingUp_m12_radical_elementary h hV hfix hm hw K hK e).1
  have hEC : E ≤ C := hn.1.trans (map_subtype_le _)
  let Ec := E.subgroupOf C
  let : Ec.Normal := normal_subgroupOf_of_le_normalizer hn.2.2.2
  let : IsElementaryAbelian 2 Ec := IsElementaryAbelian.subgroupOf hEC
  let nc : (⊤ : Subgroup C) ≤ normalizer (Ec : Set C) := le_normalizer_of_normal
  let : IsElementaryAbelian 2 (Ec.map C.subtype) := IsElementaryAbelian.map C.subtype
  have hno : ¬ IsFFModule (imageRepresentation (⊤ : Subgroup C) Ec nc) := by
    intro hf
    have hi : Function.Injective (C.subtype.subgroupMap Ec) := by
      intro x y he
      apply Subtype.ext
      apply C.subtype_injective
      exact congrArg (fun z : Ec.map C.subtype => (z : Janko4.Model)) he
    have hmapped := (image_ff_map_iff C.subtype ⊤ Ec nc hi).mp hf
    have hnff := D.sourceOrbit_pushingUp_native_nonFF h hV hfix (.inl hm) hnon hw K hK e
    apply hnff
    have ht : (⊤ : Subgroup C).map C.subtype = C := by rw [←MonoidHom.range_eq_map,range_subtype]
    exact (image_ff_congr ht (map_subgroupOf_eq_of_le hEC) _ _).mp hmapped
  let S : Sylow 2 C := Classical.choice inferInstance
  have hES : Ec ≤ (S : Subgroup C) := (IsElementaryAbelian.isPGroup 2 Ec).le_sylow_of_normal S
  have hJC : Stellmacher.elementaryAbelianMaxJ (S : Subgroup C) ≤ centralizer (Ec : Set C) := by
    by_contra hh
    exact hno (Chapter3.internalActionImage_isFFModule_of_thompson_not_le S ⊤ Ec
      le_top hES nc hh)
  have hJU : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype ≤ U := by
    rintro _ ⟨x,hx,rfl⟩
    apply hC.le
    refine ⟨x.property,?_⟩
    intro v hv
    exact congrArg C.subtype (hJC hx ⟨v,hEC hv⟩ hv)
  have hUS : U ≤ (S : Subgroup C).map C.subtype := by
    exact hU.1.symm.le.trans (C.pCoreIn_le_sylow S)
  have hJeq : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype = U := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective] at hJU ⊢
    exact Stellmacher.elementaryAbelianMaxJ_eq_of_elementary_overgroup _ U hJU hUS inferInstance
  obtain ⟨P,hSP⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  have heq : (S : Subgroup C).map C.subtype = (P : Subgroup Janko4.Model) := by
    by_contra hh
    have hlt := lt_normalizer_of_sylow_thompson C U (by rw [hU.2.1]) S hJeq P
      (lt_of_le_of_ne hSP hh)
    rw [hU.2.1] at hlt
    exact lt_irrefl _ hlt
  refine ⟨P,heq ▸ map_subtype_le _,?_⟩
  rw [←heq,Stellmacher.elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective]
  exact hJeq
/-- An elementary module centralizer which controls its own normalizer,
under non-FF, is the Thompson subgroup of a full native Sylow. -/
theorem native_sylow_of_elementary_core_nonFF
    (U E B : Subgroup Janko4.Model)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 E]
    (hEU : E ≤ U)
    (hcore : (normalizer (B : Set Janko4.Model)).pCoreIn 2 = U)
    (hnorm : normalizer (U : Set Janko4.Model) = normalizer (B : Set Janko4.Model))
    (hcent : normalizer (B : Set Janko4.Model) ⊓ centralizer (E : Set Janko4.Model) = U)
    (hNE : normalizer (B : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model))
    (hnon : ¬ IsFFModule (imageRepresentation (normalizer (B : Set Janko4.Model)) E hNE)) :
    ∃ P : Sylow 2 Janko4.Model,
      (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
        Stellmacher.elementaryAbelianMaxJ (P : Subgroup Janko4.Model) = U := by
  let C := normalizer (B : Set Janko4.Model)
  have hEC : E ≤ C := hEU.trans (hcore.symm.le.trans (map_subtype_le _))
  let Ec := E.subgroupOf C
  let : Ec.Normal := normal_subgroupOf_of_le_normalizer hNE
  let : IsElementaryAbelian 2 Ec := IsElementaryAbelian.subgroupOf hEC
  let nc : (⊤ : Subgroup C) ≤ normalizer (Ec : Set C) := le_normalizer_of_normal
  let : IsElementaryAbelian 2 (Ec.map C.subtype) := IsElementaryAbelian.map C.subtype
  have hno : ¬ IsFFModule (imageRepresentation (⊤ : Subgroup C) Ec nc) := by
    intro hf
    have hi : Function.Injective (C.subtype.subgroupMap Ec) := by
      intro x y he
      apply Subtype.ext
      apply C.subtype_injective
      exact congrArg (fun z : Ec.map C.subtype => (z : Janko4.Model)) he
    have hmapped := (image_ff_map_iff C.subtype ⊤ Ec nc hi).mp hf
    apply hnon
    have ht : (⊤ : Subgroup C).map C.subtype = C := by rw [←MonoidHom.range_eq_map,range_subtype]
    exact (image_ff_congr ht (map_subgroupOf_eq_of_le hEC) _ _).mp hmapped
  let S : Sylow 2 C := Classical.choice inferInstance
  have hES : Ec ≤ (S : Subgroup C) := (IsElementaryAbelian.isPGroup 2 Ec).le_sylow_of_normal S
  have hJC : Stellmacher.elementaryAbelianMaxJ (S : Subgroup C) ≤ centralizer (Ec : Set C) := by
    by_contra hh
    exact hno (Chapter3.internalActionImage_isFFModule_of_thompson_not_le S ⊤ Ec
      le_top hES nc hh)
  have hJU : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype ≤ U := by
    rintro _ ⟨x,hx,rfl⟩
    apply hcent.le
    refine ⟨x.property,?_⟩
    intro v hv
    exact congrArg C.subtype (hJC hx ⟨v,hEC hv⟩ hv)
  have hUS : U ≤ (S : Subgroup C).map C.subtype := by
    exact hcore.symm.le.trans (C.pCoreIn_le_sylow S)
  have hJeq : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype = U := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective] at hJU ⊢
    exact Stellmacher.elementaryAbelianMaxJ_eq_of_elementary_overgroup _ U hJU hUS inferInstance
  obtain ⟨P,hSP⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  have heq : (S : Subgroup C).map C.subtype = (P : Subgroup Janko4.Model) := by
    by_contra hh
    have hlt := lt_normalizer_of_sylow_thompson C U (by rw [hnorm]) S hJeq P
      (lt_of_le_of_ne hSP hh)
    rw [hnorm] at hlt
    exact lt_irrefl _ hlt
  refine ⟨P,heq ▸ map_subtype_le _,?_⟩
  rw [←heq,Stellmacher.elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective]
  exact hJeq
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
