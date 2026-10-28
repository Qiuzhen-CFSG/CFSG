module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.SquareCentralizers
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.ThirdCentralizer
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.PlaneCentralizers

/-!
# Global containment for the third symplectic involution centralizer

The compatible pure amalgam identifies the two elementary abelian wings
with the actual parabolic two-cores, including their whole embeddings in
G. They exhaust the noncentral involution centralizers in the inner Sylow.

Assuming the transfer conclusion S = T, Burnside fusion and the exact
root-center normalizers identify N_G(Z(T)) with the whole middle D.
Characteristic two of each square-involution centralizer then forces its
two-core either to have omega-center Z(T), or to equal one parabolic core.
The resulting global containment in a full normalizer combines with the
previous local square-centralizer calculation to give C_G(z) ≤ D.

This proves the Sp₄ global step of Aschbacher–Smith F.4.39, printed p.294
of `refs/quasithin.pdf`, on the original prepared pair of 5.3.1–3. The
transfer S = T is an explicit earlier-source premise still to be discharged;
no ambient order conclusion or completed recognition is used. Both pure
orientations, n = 2, and the whole residual of H are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem wing_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {S P : Subgroup G} (hSP : S ≤ P)
    (a : S ≃* unipotent (F := F)) (i : Bool)
    (f : P →* Sp F) (hf : Function.Injective f)
    (hfa : ∀ s : S, f ⟨s.val,hSP s.property⟩ = (a s).val)
    (hcore : (pCore 2 P).map f = (wing i).map unipotent.subtype) :
    ((wing i).comap a.toMonoidHom).map S.subtype = P.pCoreIn 2 := by
  ext x
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hh : f ⟨s.val,hSP s.property⟩ ∈ (pCore 2 P).map f := by
      rw [hcore,hfa]
      exact mem_map_of_mem _ hs
    obtain ⟨p,hp,he⟩ := hh
    have he' : p = ⟨s.val,hSP s.property⟩ := hf he
    exact ⟨p,hp,congrArg Subtype.val he'⟩
  · rintro ⟨p,hp,rfl⟩
    have hh : f p ∈ (wing i).map unipotent.subtype :=
      hcore ▸ mem_map_of_mem f hp
    obtain ⟨u,hu,he⟩ := hh
    let s := a.symm u
    have hsp : (⟨s.val,hSP s.property⟩ : P) = p := by
      apply hf
      rw [hfa]
      simpa only [s,a.apply_symm_apply,Subgroup.subtype_apply] using he
    refine ⟨s,?_,congrArg Subtype.val hsp⟩
    change a (a.symm u) ∈ wing i
    rwa [a.apply_symm_apply]

private theorem pair_wing_geometry
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m)
    {P Q C S : Subgroup G} (hCP : C ≤ P) (hCQ : C ≤ Q) (hSC : S ≤ C)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) :
    IsElementaryAbelian 2 (center S) ∧
    ∃ R : Fin 2 → Subgroup S,
      (∀ i, (R i).map S.subtype = (![P,Q] i).pCoreIn 2) ∧
      (∀ i, IsElementaryAbelian 2 (R i)) ∧
      (∀ x : S, x^2=1 → x ∉ center S → ∃ i, centralizer ({x} : Set S) = R i) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF (by omega)).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.middle.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.middle.toMonoidHom) e.middle.surjective) U)
  let a : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.middle.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  have hl (s : S) :
      (e.left ⟨s.val,(hSC.trans hCP) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.left_commutes ⟨s.val,hSC s.property⟩)
  have hr (s : S) :
      (e.right ⟨s.val,(hSC.trans hCQ) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.right_commutes ⟨s.val,hSC s.property⟩)
  have hcorel : (pCore 2 P).map (pointParabolic.subtype.comp e.left.toMonoidHom) =
      (wing false).map (unipotent (F := F)).subtype := by
    rw [←map_map,pCore_map_iso 2 e.left,
      pointParabolic_core_map_eq_radical hF hm]
    exact SymplecticConjugatePair.pointRadical_eq_wing
  have hcorer : (pCore 2 Q).map (planeParabolic.subtype.comp e.right.toMonoidHom) =
      (wing true).map (unipotent (F := F)).subtype := by
    rw [←map_map,pCore_map_iso 2 e.right,
      planeParabolic_core_map_eq_radical hF hm]
    exact SymplecticConjugatePair.planeRadical_eq_wing
  let R' : Fin 2 → Subgroup S :=
    ![(wing false).comap a.toMonoidHom,(wing true).comap a.toMonoidHom]
  have helem (i : Bool) : IsElementaryAbelian 2 ((wing i).comap a.toMonoidHom) := by
    let _ := wing_elementary (F := F) i
    exact IsElementaryAbelian.comap_of_injective _ a.injective _
  have hZ : IsElementaryAbelian 2 (center S) := by
    let _ := center_elementary (F := F)
    exact IsElementaryAbelian.of_injective (centerCongr a).toMonoidHom (centerCongr a).injective
  refine ⟨hZ,R',?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact wing_transport (hSC.trans hCP) a false _
        (pointParabolic.subtype_injective.comp e.left.injective) hl hcorel
    · exact wing_transport (hSC.trans hCQ) a true _
        (planeParabolic.subtype_injective.comp e.right.injective) hr hcorer
  · intro i
    fin_cases i
    · exact helem false
    · exact helem true
  · intro x hx hxZ
    have hax : (a x)^2=1 := by rw [←map_pow,hx,map_one]
    have haxZ : a x ∉ center (unipotent (F := F)) := by
      intro hh
      apply hxZ
      apply mem_center_iff.mpr
      intro s
      apply a.injective
      simpa only [map_mul] using (mem_center_iff.mp hh) (a s)
    have hpull (i : Bool) (hi : centralizer ({a x} : Set (unipotent (F := F))) = wing i) :
        centralizer ({x} : Set S) = (wing i).comap a.toMonoidHom := by
      ext s
      change s ∈ centralizer ({x} : Set S) ↔ a s ∈ wing i
      rw [←hi,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
      exact ⟨fun h => by simpa only [map_mul] using congrArg a h,
        fun h => a.injective (by simpa only [map_mul] using h)⟩
    rcases centralizer_involution (a x) hax haxZ with hc | hc
    · exact ⟨0,hpull false hc⟩
    · exact ⟨1,hpull true hc⟩

/-- The two actual parabolic cores are elementary abelian and give all
noncentral involution centralizers of the original inner Sylow. -/
theorem Preparation.symplectic_sylow_wing_geometry
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    : IsElementaryAbelian 2 (center (sourceS L H)) ∧
      (∀ i : Fin 2, IsElementaryAbelian 2
        ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2)) ∧
      (∀ x : sourceS L H, x^2=1 → x ∉ center (sourceS L H) →
        ∃ i : Fin 2, (centralizer ({x} : Set (sourceS L H))).map (sourceS L H).subtype =
          (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).pCoreIn 2) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hf := d.hypothesisF11 h hH.1.1.2
  have hm' : 1 < m :=
    (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1.symm ▸ h.exponent
  have hSC : sourceS L H ≤ C := le_inf (le_sup_right.trans le_sup_left)
    (le_sup_right.trans le_sup_left)
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hdirect {P Q : Subgroup G}
      (hh : IsElementaryAbelian 2 (center (sourceS L H)) ∧
        ∃ R : Fin 2 → Subgroup (sourceS L H),
          (∀ i, (R i).map (sourceS L H).subtype = (![P,Q] i).pCoreIn 2) ∧
          (∀ i, IsElementaryAbelian 2 (R i)) ∧
          (∀ x : sourceS L H, x^2=1 → x ∉ center (sourceS L H) →
            ∃ i, centralizer ({x} : Set (sourceS L H)) = R i)) :
      IsElementaryAbelian 2 (center (sourceS L H)) ∧
      (∀ i : Fin 2, IsElementaryAbelian 2 ((![P,Q] i).pCoreIn 2)) ∧
      (∀ x : sourceS L H, x^2=1 → x ∉ center (sourceS L H) →
        ∃ i : Fin 2, (centralizer ({x} : Set (sourceS L H))).map (sourceS L H).subtype =
          (![P,Q] i).pCoreIn 2) := by
    obtain ⟨hZ,R,hR,hRe,hRc⟩ := hh
    refine ⟨hZ,?_,?_⟩
    · intro i
      rw [←hR i]
      let _ := hRe i
      exact IsElementaryAbelian.map _
    · intro x hx hxZ
      obtain ⟨i,hi⟩ := hRc x hx hxZ
      exact ⟨i,by rw [hi,hR]⟩
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · have heta : ![P 0,P 1] = P := by
      funext i
      fin_cases i <;> rfl
    have hh := hdirect (P := P 0) (Q := P 1)
      (pair_wing_geometry hF hm' inf_le_left inf_le_right hSC hs e)
    rw [heta] at hh
    exact hh
  · obtain ⟨hZ,hE,hC⟩ := hdirect
      (pair_wing_geometry hF hm' inf_le_right inf_le_left hSC hs e.reverse)
    refine ⟨hZ,?_,?_⟩
    · intro i
      fin_cases i
      · exact hE 1
      · exact hE 0
    · intro x hx hxZ
      obtain ⟨i,hi⟩ := hC x hx hxZ
      fin_cases i
      · exact ⟨1,hi⟩
      · exact ⟨0,hi⟩

/-- Once the inner Sylow is the ambient Sylow, its whole center has
exactly the original full-normalizer intersection as normalizer. -/
theorem Preparation.symplectic_center_normalizer_eq_middle_of_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hST : sourceS L H = (T : Subgroup G)) :
    normalizer ((center (sourceS L H)).map (sourceS L H).subtype : Set G) =
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  let M : Fin 2 → Subgroup G := fun i => normalizer (![L,residual H] i : Set G)
  let D := M 0 ⊓ M 1
  have hf := d.hypothesisF11 h hH.1.1.2
  have hTS (i : Fin 2) : (T : Subgroup G) ≤ ![L,residual H] i :=
    hST ▸ d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he i
  have hlocal := d.symplectic_normalizer_local_conditions h hH hp F hm hF he
  have hD : D = normalizer (T : Set G) := by
    have hh := hlocal.normalizer_eq_middle.symm
    change normalizer (L : Set G) ⊓ normalizer (residual H : Set G) =
      normalizer ((T : Subgroup G) ⊓ L : Set G) at hh
    exact hh.trans (congrArg normalizer (inf_eq_left.mpr
      (show (T : Set G) ≤ (L : Set G) from hTS 0)))
  have hZnorm (i : Fin 2) := (d.symplectic_root_center_fusion h hH hp F hm hF he i).2.2
  have hZ (i : Fin 2) :
      (center (![L,residual H] i)).map (![L,residual H] i).subtype ≤
        (center T).map (T : Subgroup G).subtype := by
    rintro _ ⟨z,hz,rfl⟩
    have hzcore : z ∈ pCore 2 (![L,residual H] i) :=
      hf.local_core_selfCentralizing i (center_le_centralizer _ hz)
    have hzT : z.val ∈ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow (![L,residual H] i) (T.subtype (hTS i))
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (hTS i)] at hh
      exact hh (mem_map_of_mem _ hzcore)
    refine ⟨⟨z.val,hzT⟩,mem_center_iff.mpr ?_,rfl⟩
    intro t
    exact Subtype.ext (congrArg (fun z : ![L,residual H] i => z.val)
      ((mem_center_iff.mp hz) ⟨t.val,hTS i t.property⟩))
  have hNZ (i : Fin 2) :
      normalizer ((center T).map (T : Subgroup G).subtype : Set G) ≤ M i := by
    change normalizer ((center T).map (T : Subgroup G).subtype : Set G) ≤
      normalizer (![L,residual H] i : Set G)
    rw [←hZnorm i]
    apply Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.center_normalizer_le_of_sylow_normalizer_le T _ (hZ i)
    rw [hZnorm i,←hD]
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  rw [hST]
  apply le_antisymm (le_inf (hNZ 0) (hNZ 1))
  change D ≤ _
  rw [hD]
  exact normalizer_le_normalizer_characteristic_image (T : Subgroup G) (center T)

/-- The global centralizer of a nonidentity Sylow square is in the whole
middle, conditional only on the earlier transfer conclusion S = T. -/
theorem Preparation.symplectic_square_centralizer_le_middle_of_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hST : sourceS L H = (T : Subgroup G))
    (z : sourceS L H) (hz : orderOf z = 2) (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := centralizer ({z.val} : Set G)
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz
  have hSC : sourceS L H ≤ C := by
    intro s hs
    have hh := (d.symplectic_square_parabolic_centralizers h hH.1.1.2 F hm hF he 0 z hz1 hsq).symm ▸ hs
    exact hh.1
  have hTC : (T : Subgroup G) ≤ C := hST ▸ hSC
  have hf := d.hypothesisF11 h hH.1.1.2
  have hcore (i : Fin 2) : (P i).pCoreIn 2 ≤ (T : Subgroup G) :=
    hST ▸ hf.parabolic_core_le_S i
  let R : Fin 2 → Subgroup T := fun i => ((P i).pCoreIn 2).subgroupOf (T : Subgroup G)
  have hR (i : Fin 2) : (R i).map (T : Subgroup G).subtype = (P i).pCoreIn 2 :=
    map_subgroupOf_eq_of_le (hcore i)
  have hg := d.symplectic_sylow_wing_geometry h hH hp F hm hF he
  have hZ : IsElementaryAbelian 2 (center T) := hST ▸ hg.1
  have hRelem (i : Fin 2) : IsElementaryAbelian 2 (R i) := by
    let _ := hg.2.1 i
    exact IsElementaryAbelian.subgroupOf (hcore i)
  have hcent (x : T) (hx : x^2=1) (hxZ : x ∉ center T) :
      ∃ i, centralizer ({x} : Set T) = R i := by
    have hg' : ∀ x : (T : Subgroup G), x^2=1 → x ∉ center T →
        ∃ i : Fin 2, (centralizer ({x} : Set T)).map (T : Subgroup G).subtype =
          (P i).pCoreIn 2 := by
      have hh := hg.2.2
      rw [hST] at hh
      simpa only [P,hST] using hh
    obtain ⟨i,hi⟩ := hg' x hx hxZ
    refine ⟨i,?_⟩
    apply map_injective (T : Subgroup G).subtype_injective
    exact hi.trans (hR i).symm
  have hself : C ⊓ centralizer (C.pCoreIn 2 : Set G) ≤ C.pCoreIn 2 :=
    (inf_centralizer_pCoreIn_le_iff 2 C).mpr
      (d.symplectic_square_centralizer_characteristicTwo h hH.1.1.2 F hm hF he z hz hsq)
  apply Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.le_of_noncentral_involution_centralizers T C D hTC hself hZ R
    (fun i => (hRelem i).toIsMulCommutative) hcent
  · have hh := d.symplectic_center_normalizer_eq_middle_of_sylow h hH hp F hm hF he hST
    rw [hST] at hh
    exact hh.le
  · intro i
    have heq : (center ((P i).pCoreIn 2)).map ((P i).pCoreIn 2).subtype = (P i).pCoreIn 2 := by
      let _ := hg.2.1 i
      rw [center_eq_top,←MonoidHom.range_eq_map,range_subtype]
    have hn := (d.symplectic_parabolic_core_center_normalizers h hH hp F hm hF he i).2
    change normalizer ((center ((P i).pCoreIn 2)).map ((P i).pCoreIn 2).subtype : Set G) = _ at hn
    rw [heq] at hn
    rw [hR i,hn]
    exact (d.symplectic_square_full_normalizer_centralizers h hH hp F hm hF he i z hz1 hsq).le.trans inf_le_right

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
