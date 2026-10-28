module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SylowModels
public import Theory.SpecificGroups.G2.OddSupplement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSupplement
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSupplement

/-!
# Excluding rank-two quotients by the original odd action

The actual residual image is nonsolvable and proper in K/O₂(K). If that
quotient has two maximal overgroups of its actual Sylow with solvable
intersection, exactly one contains the residual. The original odd supplement
fixes both overgroups, while the original T fixes the uniquely selected one.
Thus the full enlarged local group normalizes it. In particular every inner
automorphism of K/O₂(K) preserves it, contradicting C-component minimality.

The concrete projective linear-three, symplectic-four and split-octonion
parabolics discharge this geometric premise. All actions are induced by the
original conjugation and quotient maps. The source escape application
excludes these actual containing models; the remaining J₁ recognition,
intersection escape and terminal geometry stay with
qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.12, case (2) of A.3.12 in the proof,
printed pp.589--590. The imported concrete models retain the attribution
and license recorded in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

omit [Finite G] in
private theorem quotient_action_preserves (K B : Subgroup G)
    (g : normalizer (K : Set G)) (hg : (g : G) ∈ normalizer (B : Set G)) :
    ((B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
      (coreQuotientAction K g).toMonoidHom =
        (B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) := by
  have he : (B.subgroupOf K).map (K.normalizerMonoidHom g).toMonoidHom = B.subgroupOf K := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      exact (hg b).mp hb
    · intro b hb
      refine ⟨K.normalizerMonoidHom g⁻¹ b,?_,?_⟩
      · exact ((normalizer (B : Set G)).inv_mem hg b).mp hb
      · rw [map_inv K.normalizerMonoidHom]
        exact (K.normalizerMonoidHom g).apply_symm_apply b
  change ((B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
    (quotientAut (pCore 2 K) (K.normalizerMonoidHom g)).toMonoidHom = _
  have hq : (quotientAut (pCore 2 K) (K.normalizerMonoidHom g)).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 K)) =
      (QuotientGroup.mk' (pCore 2 K)).comp (K.normalizerMonoidHom g).toMonoidHom := by
    ext x
    exact quotientAut_apply_mk _ _ x
  rw [map_map,hq,←map_map,he]

omit [Finite G] in
private theorem quotient_action_internal (K : Subgroup G) (k : K) :
    coreQuotientAction K ⟨k,K.le_normalizer k.property⟩ =
      MulAut.conj (QuotientGroup.mk' (pCore 2 K) k) := by
  ext x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 K) (k * x * k⁻¹) = _
  rw [map_mul,map_mul,map_inv,MulAut.conj_apply]

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The original residual image is nonsolvable in its literal containing quotient. -/
theorem residualImage_not_solvable : ¬ Group.IsSolvable E.residualImage := by
  have h := E.residualImage_local
  let e := subgroupOfEquivOfLe (show E.residualImage ≤ E.residualImage ⊔ E.quotientSylow from le_sup_left)
  intro hs
  let := hs
  exact h.not_isSolvable (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

/-- The actual Sylow image normalizes the actual residual image. -/
theorem quotientSylow_normalizes_residualImage :
    E.quotientSylow ≤ normalizer (E.residualImage : Set _) := by
  apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 E.component)))
  intro t ht
  exact fun y => f.sylow_normalizes_Li E.index ht y

private theorem quotient_normal_subgroup_solvable
    (B : Subgroup (E.component ⧸ pCore 2 E.component)) (hn : B.Normal) (hne : B ≠ ⊤) :
    Group.IsSolvable B := by
  let e : (E.component ⧸ pCore 2 E.component) ≃* (⊤ : Subgroup _) := topEquiv.symm
  have hn' : (B.map e.toMonoidHom).Normal := Normal.map hn e.toMonoidHom e.surjective
  have hne' : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he,map_top_of_surjective _ e.surjective]
  let := E.componentQuotient_isCComponent.isSolvable_of_subnormal_lt_top hn'.isSubnormal hne'
  exact Group.isSolvable_of_surjective
    (f := (B.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom)
    (B.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

/-- The original residual and full Sylow have proper join in the quotient. -/
theorem residualImage_sup_quotientSylow_ne_top :
    E.residualImage ⊔ E.quotientSylow ≠ ⊤ := by
  intro he
  have hn : E.residualImage.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← he]
    exact sup_le E.residualImage.le_normalizer E.quotientSylow_normalizes_residualImage)
  exact E.residualImage_not_solvable
    (E.quotient_normal_subgroup_solvable E.residualImage hn E.residualImage_ne_top)

/-- Two maximal Sylow overgroups with solvable intersection exclude the actual
moved component. The odd supplement acts on that pair through its original
quotient action; no independent parabolic action is postulated. -/
theorem false_of_two_sylow_overgroups
    (hgeometry : ∀ U : Sylow 2 (E.component ⧸ pCore 2 E.component),
      ∃ P Q : Subgroup (E.component ⧸ pCore 2 E.component),
        IsCoatom P ∧ IsCoatom Q ∧ (U : Subgroup _) ≤ P ∧ (U : Subgroup _) ≤ Q ∧
        Group.IsSolvable (P ⊓ Q : Subgroup _) ∧
        ∀ J : Subgroup _, (U : Subgroup _) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q) : False := by
  let B := E.residualImage
  let U := E.quotientSylow
  have hBns : ¬ Group.IsSolvable B := E.residualImage_not_solvable
  have hBU : B ⊔ U ≠ ⊤ := E.residualImage_sup_quotientSylow_ne_top
  obtain ⟨U',hU'⟩ := E.quotientSylow_isSylow
  obtain ⟨P,Q,hP,hQ,hUP,hUQ,hsol,hcover⟩ := hgeometry U'
  rw [hU'] at hUP hUQ hcover
  have perm (a : MulAut (E.component ⧸ pCore 2 E.component)) (ha : U.map a.toMonoidHom = U)
      (J : Subgroup _) (hJ : J = P ∨ J = Q) :
      J.map a.toMonoidHom = P ∨ J.map a.toMonoidHom = Q := by
    have hc : IsCoatom J := hJ.elim (fun he => he ▸ hP) (fun he => he ▸ hQ)
    have hUJ : U ≤ J := hJ.elim (fun he => he ▸ hUP) (fun he => he ▸ hUQ)
    have hm := (a.mapSubgroup.isCoatom_iff J).mpr hc
    have hu : U ≤ J.map a.toMonoidHom := by
      rw [← ha]
      exact map_mono hUJ
    rcases hcover _ hu hm.ne_top with hp | hq
    · exact .inl ((hm.le_iff_eq hP.ne_top).mp hp).symm
    · exact .inr ((hm.le_iff_eq hQ.ne_top).mp hq).symm
  obtain ⟨J,hJ,hBJ⟩ : ∃ J : Subgroup _, (J = P ∨ J = Q) ∧ B ≤ J := by
    rcases hcover (B ⊔ U) le_sup_right hBU with hp | hq
    · exact ⟨P,.inl rfl,le_sup_left.trans hp⟩
    · exact ⟨Q,.inr rfl,le_sup_left.trans hq⟩
  have unique (Y Z : Subgroup _) (hY : Y = P ∨ Y = Q) (hZ : Z = P ∨ Z = Q)
      (hBY : B ≤ Y) (hBZ : B ≤ Z) : Y = Z := by
    have bad : ¬ B ≤ P ⊓ Q := by
      intro hh
      let := hsol
      exact hBns (Group.isSolvable_of_isSolvable_injective (inclusion_injective hh))
    rcases hY with rfl | rfl <;> rcases hZ with rfl | rfl
    · rfl
    · exact (bad (le_inf hBY hBZ)).elim
    · exact (bad (le_inf hBZ hBY)).elim
    · rfl
  let N : Subgroup G := ((MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) J).comap
    (coreQuotientAction E.component)).map (normalizer (E.component : Set G)).subtype
  have lift_fixed (x : G) (hx : x ∈ normalizer (E.component : Set G))
      (hf : J.map (coreQuotientAction E.component ⟨x,hx⟩).toMonoidHom = J) : x ∈ N :=
    ⟨⟨x,hx⟩,hf,rfl⟩
  have hYN : f.Li E.index ≤ N := by
    intro y hy
    apply lift_fixed y (E.component.le_normalizer (E.contains.le hy))
    rw [quotient_action_internal E.component ⟨y,E.contains.le hy⟩]
    apply mem_normalizer_iff_map_conj_eq.mp
    apply J.le_normalizer
    exact hBJ (mem_map_of_mem (QuotientGroup.mk' (pCore 2 E.component)) hy)
  have hTN : (T : Subgroup G) ≤ N := by
    intro t ht
    have htk := E.local_normalizes (mem_sup_left (mem_sup_right ht))
    apply lift_fixed t htk
    let a := coreQuotientAction E.component ⟨t,htk⟩
    have hu : U.map a.toMonoidHom = U :=
      quotient_action_preserves E.component (T : Subgroup G) _ ((T : Subgroup G).le_normalizer ht)
    have hb : B.map a.toMonoidHom = B :=
      quotient_action_preserves E.component (f.Li E.index) _ (f.sylow_normalizes_Li E.index ht)
    exact unique _ J (perm a hu J hJ) hJ (hb ▸ map_mono hBJ) hBJ
  have hAN : A.subgroup ≤ N := by
    have hh := odd_preserves_pair E.oddAction A.odd hJ (fun a Y hY =>
      perm (E.oddAction a)
        (E.oddAction_preserves_quotientSylow ⟨a,rfl⟩) Y hY)
    intro a ha
    exact lift_fixed a (E.local_normalizes (mem_sup_right ha)) (hh ⟨a,ha⟩)
  have hKN : E.component ≤ N := E.normal_component.1.1.trans (sup_le (sup_le hYN hTN) hAN)
  have hJn : J.Normal := by
    constructor
    intro x hx g
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.component) g
    obtain ⟨a,ha,hak⟩ := hKN k.property
    have he : a = ⟨k,E.component.le_normalizer k.property⟩ := Subtype.ext hak
    rw [he] at ha
    change J.map (coreQuotientAction E.component _).toMonoidHom = J at ha
    rw [quotient_action_internal] at ha
    exact (mem_normalizer_iff_map_conj_eq.mpr ha x).mp hx
  have hproper : J ≠ ⊤ := hJ.elim (fun he => he ▸ hP.ne_top) (fun he => he ▸ hQ.ne_top)
  let := E.quotient_normal_subgroup_solvable J hJn hproper
  exact hBns (Group.isSolvable_of_isSolvable_injective (inclusion_injective hBJ))

/-- Neither the binary nor the nonbinary projective linear-three row admits
this actual escaping odd action. -/
theorem quotient_not_even_linear_three {n : ℕ} (hn : 1 ≤ n) :
    ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 3 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  exact E.false_of_two_sylow_overgroups
    (Matrix.PSL3.LinearThree.OddSupplement.two_sylow_overgroups_of_equiv hF hn e)

/-- The literal symplectic matrix quotient is excluded in every nonbinary field. -/
theorem quotient_not_even_symplectic_four {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSp (E.component ⧸ pCore 2 E.component) 2 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  exact E.false_of_two_sylow_overgroups
    (Theory.SpecificGroups.SymplecticFour.two_sylow_overgroups_of_equiv hF (by omega) a)

/-- The actual split-octonion G₂ quotient is excluded, with its original field. -/
theorem quotient_not_even_g2 {n : ℕ} (_hn : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At (E.component ⧸ pCore 2 E.component) (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact E.false_of_two_sylow_overgroups (Atlas.G2.two_sylow_overgroups_of_equiv e)

end MovedComponent

/-- The source escape now excludes the three untwisted rank-two families
in its original containing component quotient. -/
theorem exists_moved_component_not_untwisted_rank_two (f : InvariantFlag c)
    (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      (∀ n, 1 ≤ n → ¬ ClassicalGroup.IsPSL (E.component ⧸ pCore 2 E.component) 3 (2^n)) ∧
      (∀ n, 2 ≤ n → ¬ ClassicalGroup.IsPSp (E.component ⧸ pCore 2 E.component) 2 (2^n)) ∧
      (∀ n, 2 ≤ n → ¬ ClassificationModels.IsG2At (E.component ⧸ pCore 2 E.component) (2^n)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,fun _ hn => E.quotient_not_even_linear_three hn,
    fun _ hn => E.quotient_not_even_symplectic_four hn, fun _ hn => E.quotient_not_even_g2 hn⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
