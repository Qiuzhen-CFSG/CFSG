module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# Natural A6 offender obstruction in the original MS pair

The nonzero natural module is an elementary abelian subgroup of the actual
edge two-group. MS3 forces a maximum elementary subgroup of that edge group
outside the two-core; its image under the specified natural action is a
binary offender. The finite six-point offender classification shows that an
offender inside the point radical contains an odd transposition, whereas an
A6 image contains only even permutations. This is a source-specific exclusion
that survives characteristic replacement through the original map.

Source: Meierfrankenfeld--Stellmacher (1993), (3.2)(vi) and (3.8), printed
pp. 863--865 and 877--879; Aschbacher--Smith C.1.37, printed pp.141--143.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
namespace AlternatingOffenders
open ChapterB.Offenders ChapterB.Offenders.Six Stellmacher
abbrev S := Equiv.Perm (Fin 6)
noncomputable abbrev rho := BinaryPermutation.naturalRepresentation (Fin 6)

theorem even_offender_iff (A : Subgroup S) (he : A ≤ alternatingGroup (Fin 6)) :
    IsOffender rho A ↔ IsConjugateTo A (evenPart 6) := by
  rw [isOffender_natural_iff]
  exact ⟨fun h => (caseBFamily_even_iff A).mp ⟨h,he⟩,
    fun h => ((caseBFamily_even_iff A).mpr h).1⟩

theorem even_offender_card {A : Subgroup S} (he : A ≤ alternatingGroup (Fin 6))
    (hA : IsOffender rho A) : Nat.card A = 4 :=
  ((even_offender_iff A he).mp hA).card_eq.trans card_evenPart

theorem even_offender_codim {A : Subgroup S} (he : A ≤ alternatingGroup (Fin 6))
    (hA : IsOffender rho A) : fixedCodim rho A = 2 := by
  obtain ⟨g,rfl⟩ := (even_offender_iff A he).mp hA
  rw [fixedCodim_map_conj]
  exact fixedCodim_evenPart.2.2.2

theorem even_offender_unique {T A B : Subgroup S} (hT : IsPGroup 2 T)
    (he : T ≤ alternatingGroup (Fin 6)) (hAT : A ≤ T) (hBT : B ≤ T)
    (hA : IsOffender rho A) (hB : IsOffender rho B) : A = B := by
  obtain ⟨Q,hTQ⟩ := hT.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S Q sylow
  have move (C : Subgroup S) (hCT : C ≤ T) (hC : IsOffender rho C) :
      C.map (MulAut.conj g).toMonoidHom = evenPart 6 := by
    apply (caseBFamily_even_le_sylowCarrier_iff _).mp
    refine ⟨?_,?_,?_⟩
    · rw [← isOffender_natural_iff]
      exact ⟨⟨fun hz => hC.1.1 ((C.map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp hz),
        by let := hC.1.2; exact IsElementaryAbelian.map _⟩,by
          rw [fixedCodim_map_conj,rank_map_injective _ (MulAut.conj g).injective]
          exact hC.2⟩
    · rintro x ⟨c,hc,rfl⟩
      change (MulAut.conj g) c ∈ (sylow : Subgroup S)
      rw [← hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hTQ (hCT hc))
    · exact (map_mono (hCT.trans he)).trans_eq (Subgroup.Normal.map_conj_eq _ g)
  exact Subgroup.map_injective (MulAut.conj g).injective ((move A hAT hA).trans (move B hBT hB).symm)

end AlternatingOffenders
open AlternatingOffenders ChapterB.Offenders ChapterB.Offenders.Six Stellmacher
namespace SymplecticSetup.Source
open SymplecticSetup
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M}
    [L.Normal] [W.Normal] (s : SymplecticSetup.Source L R W)

include s

omit [Finite M] in
private theorem elementary : IsElementaryAbelian 2 W := by
  let : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.natural (Fin 6))) :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro v
        change (2 : ℕ) • v.toAdd = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
        exact zero_smul (ZMod 2) v.toAdd) }
  exact IsElementaryAbelian.of_injective s.coordinates.toMonoidHom s.coordinates.injective

private def addCoordinates : Additive W ≃+ BinaryPermutation.natural (Fin 6) where
  toFun v := (s.coordinates v.toMul).toAdd
  invFun v := Additive.ofMul (s.coordinates.symm (Multiplicative.ofAdd v))
  left_inv v := s.coordinates.symm_apply_apply v
  right_inv v := s.coordinates.apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := s.coordinates.map_mul v.toMul w.toMul

/-- Every maximum elementary subgroup outside the literal action kernel is
an offender on the specified four-dimensional natural module. -/
theorem maxElementary_offender (E : Subgroup M)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups R)
    (hne : ¬ E ≤ pCore 2 M) : IsOffender rho (E.map s.projection) := by
  let := elementary s
  let q := s.projection.rangeRestrict
  have hk : q.ker = centralizer (W : Set M) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact RankOne.SymmetricSix.natural_six_kernel_eq_centralizer W s.projection s.coordinates s.action
  let r := Representation.NormalElementaryQuotient.representation W q
    s.projection.rangeRestrict_surjective hk
  let e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    { addCoordinates s with map_smul' := ZMod.map_smul (addCoordinates s) }
  have he (a : s.projection.range) (v : Additive W) :
      e (r a v) = rho a.val (e v) := by
    obtain ⟨g,rfl⟩ := s.projection.rangeRestrict_surjective a
    have hc : (r (q g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext
      (Representation.NormalElementaryQuotient.representation_apply W q
        s.projection.rangeRestrict_surjective hk g v)
    change (s.coordinates _).toAdd = _
    rw [hc]
    exact s.action g v.toMul
  have ho := Representation.NormalElementaryQuotient.maxElementary_isOffender W q
    s.projection.rangeRestrict_surjective hk R E (s.module_le_core.trans s.core_le) hE
    (by simpa only [q,MonoidHom.ker_rangeRestrict,s.projection_kernel] using hne)
  have ht := ho.map_equivariant r rho s.projection.range.subtype
    s.projection.range.subtype_injective e he
  rw [Subgroup.map_map] at ht
  have hf : s.projection.range.subtype.comp q = s.projection := rfl
  rwa [hf] at ht

/-- Literal image and fixed-codimension output in the A6 branch. -/
theorem maxElementary_image (himage : s.projection.range = alternatingGroup (Fin 6))
    (E : Subgroup M) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups R)
    (hne : ¬ E ≤ pCore 2 M) :
    IsConjugateTo (E.map s.projection) (evenPart 6) ∧
      Nat.card (E.map s.projection) = 4 ∧ fixedCodim rho (E.map s.projection) = 2 := by
  have he : E.map s.projection ≤ alternatingGroup (Fin 6) := by
    rw [← himage]
    exact Subgroup.map_le_range s.projection E
  have ho := maxElementary_offender s E hE hne
  exact ⟨(even_offender_iff _ he).mp ho,even_offender_card he ho,even_offender_codim he ho⟩

/-- MS3 forces the elementary Thompson subgroup of the literal edge group
outside the kernel of the original natural action. -/
theorem thompson_not_le_core : ¬ elementaryAbelianMaxJ R ≤ pCore 2 M := by
  intro hle
  have hNR := s.core_le
  have heqOrder : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder (pCore 2 M) :=
    le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hNR).1
  have heqJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 M) :=
    le_antisymm ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).2 heqOrder)
      ((elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hNR).2 heqOrder.symm)
  have hmap (T : Subgroup M) :
      (elementaryAbelianMaxJ (⊤ : Subgroup T)).map T.subtype = elementaryAbelianMaxJ T := by
    rw [← elementaryAbelianMaxJ_map_injective _ T.subtype_injective,
      ← MonoidHom.range_eq_map, T.range_subtype]
  let C : Subgroup R := elementaryAbelianMaxJ ⊤
  let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hn : (C.map R.subtype).Normal := by
    change ((elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype).Normal
    rw [hmap, heqJ, ← hmap (pCore 2 M)]
    let : (elementaryAbelianMaxJ (⊤ : Subgroup (pCore 2 M))).Characteristic :=
      elementaryAbelianMaxJ_top_characteristic
    infer_instance
  have hC : C = ⊥ := s.characteristic.eq_bot_of_normal C hn
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr s.radical_ne_bot
  let D : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  have hD : D ≠ ⊥ := omega_center_ne_bot s.two_group
  have hDe : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 (omega₁ (center R) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center R)
    exact IsElementaryAbelian.map (center R).subtype
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup R)
  have hAC : A ≤ C := le_sSup hA
  have hAbot : A = ⊥ := le_bot_iff.mp (hC ▸ hAC)
  have hcard := hA.2.2 D le_top hDe
  rw [hAbot, card_bot] at hcard
  exact hD (eq_bot_of_card_le D hcard)

/-- The source supplies an actual maximum elementary offender, retaining the
original quotient map and natural coordinates. -/
theorem exists_maxElementary_offender :
    ∃ E ∈ elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 M ∧
      IsOffender rho (E.map s.projection) := by
  classical
  have hex : ∃ E ∈ elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 M := by
    by_contra! hall
    exact thompson_not_le_core s (sSup_le hall)
  obtain ⟨E,hE,hne⟩ := hex
  exact ⟨E,hE,hne,maxElementary_offender s E hE hne⟩

/-- The inherited point-radical containment excludes an alternating image.
The finite calculation is on the image of the actual maximum elementary
subgroup, rather than on an independently chosen action. -/
theorem not_alternating_image_of_radical_image_le
    (hR : R.map s.projection ≤ Model.E) :
    s.projection.range ≠ alternatingGroup (Fin 6) := by
  intro himage
  obtain ⟨E,hE,hne,ho⟩ := exists_maxElementary_offender s
  have hEimage : E.map s.projection ≤ Model.E := (map_mono hE.1).trans hR
  have hb : IsBestOffender rho (E.map s.projection) :=
    (isBestOffender_natural_iff _).mpr ((isOffender_natural_iff _).mp ho)
  have hswap := Model.best_contains_swap hEimage hb
  have heven : E.map s.projection ≤ alternatingGroup (Fin 6) := by
    rw [← himage]
    exact Subgroup.map_le_range s.projection E
  exact (by decide : pairSwap 6 2 ∉ alternatingGroup (Fin 6)) (heven hswap)

/-- The same exclusion preserves an arbitrary original point marking. -/
theorem not_alternating_image_of_radical_image_le_conjugate (g : S)
    (hR : R.map s.projection ≤ Model.E.map (MulAut.conj g).toMonoidHom) :
    s.projection.range ≠ alternatingGroup (Fin 6) := by
  intro himage
  obtain ⟨E,hE,hne,ho⟩ := exists_maxElementary_offender s
  let A := (E.map s.projection).map (MulAut.conj g⁻¹).toMonoidHom
  have hA : A ≤ Model.E := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      ((map_mono hE.1).trans hR)
    have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id S := by ext x; simp [MulAut.conj_apply,mul_assoc]
    simpa only [A,Subgroup.map_map,hc,Subgroup.map_id] using hh
  have hao : IsOffender rho A := ⟨ho.1.map_conj g⁻¹,by
    dsimp only [A]
    rw [fixedCodim_map_conj,rank_map_conj]
    exact ho.2⟩
  have heven : A ≤ alternatingGroup (Fin 6) := by
    have hm : E.map s.projection ≤ alternatingGroup (Fin 6) := by
      rw [← himage]
      exact Subgroup.map_le_range s.projection E
    exact (map_mono hm).trans_eq (Subgroup.Normal.map_conj_eq _ g⁻¹)
  exact exceptional_not_conjugate_evenPart hA ((even_offender_iff A heven).mp hao)

/-- The original point-radical family has full S6 image after every
characteristic replacement preserving this containment. -/
theorem projection_surjective_of_radical_image_le_conjugate (g : S)
    (hR : R.map s.projection ≤ Model.E.map (MulAut.conj g).toMonoidHom) :
    Function.Surjective s.projection := by
  apply MonoidHom.range_eq_top.mp
  have hd : s.projection.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      index_dvd_of_le s.image_contains_alternating
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact index_eq_one.mp hi
  · exact (s.not_alternating_image_of_radical_image_le_conjugate g hR
      (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi)).elim

/-- Literal large-distance A6 exclusion for the original point-radical
family. Its image-containment premise survives the source reduction. -/
theorem large_distance_alternating_false
    (hR : R.map s.projection ≤ Model.E)
    (himage : s.projection.range = alternatingGroup (Fin 6))
    (_hb : 2 < s.geometry.b R) : False :=
  not_alternating_image_of_radical_image_le s hR himage

end SymplecticSetup.Source
end CFSG.Quasithin.ChapterC.NaturalSixControl
