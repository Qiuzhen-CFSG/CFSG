module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.PCoreImage

/-!
# Faithful detection of a moved flag residual in the component quotient

The two-core of the containing normal component K lies in the original T,
so it normalizes the perfect flag residual Y. Hence Y is the solvable
residual of YO₂(K). An automorphism of K preserves the image of Y in
K/O₂(K) exactly when it preserves Y itself. Applied to the original odd
Sylow complement, this gives a nontrivial odd action moving that same
residual image and preserving the actual Sylow image in K/O₂(K).

The final application constructs these data from the original normalizer
escape, before any component model has been recognized. Model comparison,
the escape of K intersect A, and terminal exclusion remain with the assembly
owner qt-d-1222-natural-line-action; this module does not claim 3.3.16.

Source: Aschbacher--Smith, 3.3.12, especially (*) and (**), pp.589--590,
and its application in 3.3.15--16, pp.590--591.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise

private theorem perfect_core_image_invariant {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [Group.IsPerfect B]
    (hn : pCore 2 G ≤ normalizer (B : Set G)) (a : MulAut G)
    (ha : (B.map (QuotientGroup.mk' (pCore 2 G))).map
      (quotientAut (pCore 2 G) a).toMonoidHom = B.map (QuotientGroup.mk' (pCore 2 G))) :
    B.map a.toMonoidHom = B := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hcomp : q.comp a.toMonoidHom = (quotientAut (pCore 2 G) a).toMonoidHom.comp q := by
    ext x
    exact (quotientAut_apply_mk (pCore 2 G) a x).symm
  have hmap : (B.map a.toMonoidHom).map q = B.map q := by
    rw [map_map,hcomp,←map_map]
    exact ha
  have hle : B.map a.toMonoidHom ≤ B ⊔ pCore 2 G := by
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using
      (map_le_iff_le_comap.mp hmap.le)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let : Group.IsPerfect (B.map a.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := (a.subgroupMap B).toMonoidHom) (a.subgroupMap B).surjective
  have hres := le_map_solvableResidual_of_isPerfect (B.map a.toMonoidHom)
    (B ⊔ pCore 2 G) hle
  rw [map_solvableResidual_sup_eq_of_perfect_normalized B (pCore 2 G) hn] at hres
  exact eq_of_le_of_card_ge hres (by rw [card_map_of_injective a.injective])

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

/-- The actual normal component before its exceptional quotient is recognized. -/
structure MovedComponent (S : D.NonbinaryNaturalInput) (f : InvariantFlag c)
    (A : OddSupplement T) where
  index : Fin 2
  component : Subgroup G
  normal_component : Source.NormalComponentIn
    ((f.Li index ⊔ (T : Subgroup G)) ⊔ A.subgroup) component
  contains : f.Li index < component
  moves : ¬ A.subgroup ≤ normalizer (f.Li index : Set G)

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Normality is relative to the original enlarged parabolic. -/
theorem local_normalizes :
    ((f.Li E.index ⊔ (T : Subgroup G)) ⊔ A.subgroup) ≤ normalizer (E.component : Set G) :=
  (normal_subgroupOf_iff_le_normalizer E.normal_component.1.1).mp E.normal_component.2

/-- Relative normality puts the component two-core inside the original Sylow. -/
theorem component_core_le_sylow : E.component.pCoreIn 2 ≤ (T : Subgroup G) := by
  let H := (f.Li E.index ⊔ (T : Subgroup G)) ⊔ A.subgroup
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_left
  have hcore : E.component.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes E.normal_component.1.1 E.local_normalizes
  have hh := pCoreIn_le_sylow H (T.subtype hTH)
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hcore.trans hh

/-- Original residual image in the component two-core quotient. -/
def residualImage : Subgroup (E.component ⧸ pCore 2 E.component) :=
  (f.Li E.index).subgroupOf E.component |>.map (QuotientGroup.mk' (pCore 2 E.component))

/-- Original odd complement action on the component quotient. -/
def oddAction : A.subgroup →* MulAut (E.component ⧸ pCore 2 E.component) :=
  (coreQuotientAction E.component).comp (inclusion (le_sup_right.trans E.local_normalizes))

/-- Passing to the component quotient reflects the exact residual stabilizer. -/
theorem residualImage_fixed_iff (g : normalizer (E.component : Set G)) :
    E.residualImage.map (coreQuotientAction E.component g).toMonoidHom = E.residualImage ↔
      (g : G) ∈ normalizer (f.Li E.index : Set G) := by
  let Y := f.Li E.index
  let B := Y.subgroupOf E.component
  let : Group.IsPerfect Y := localResidual_perfect _
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe E.contains.le).symm.toMonoidHom)
    (subgroupOfEquivOfLe E.contains.le).symm.surjective
  have hn : pCore 2 E.component ≤ normalizer (B : Set E.component) := by
    intro r hr y
    exact f.sylow_normalizes_Li E.index
      (E.component_core_le_sylow (mem_map_of_mem E.component.subtype hr)) y
  have hcomm : E.component.subtype.comp (E.component.normalizerMonoidHom g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp E.component.subtype := by
    ext x
    rfl
  have hB : B.map E.component.subtype = Y := map_subgroupOf_eq_of_le E.contains.le
  constructor
  · intro h
    have hb := perfect_core_image_invariant B hn (E.component.normalizerMonoidHom g) h
    have he := congrArg (map E.component.subtype) hb
    rw [map_map,hcomm,←map_map,hB] at he
    exact mem_normalizer_iff_map_conj_eq.mpr he
  · intro h
    have he : B.map (E.component.normalizerMonoidHom g).toMonoidHom = B := by
      apply map_injective E.component.subtype_injective
      rw [map_map,hcomm,←map_map,hB]
      exact mem_normalizer_iff_map_conj_eq.mp h
    change (B.map (QuotientGroup.mk' (pCore 2 E.component))).map
      (quotientAut (pCore 2 E.component) (E.component.normalizerMonoidHom g)).toMonoidHom = _
    rw [map_map]
    have hq : (quotientAut (pCore 2 E.component) (E.component.normalizerMonoidHom g)).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 E.component)) =
        (QuotientGroup.mk' (pCore 2 E.component)).comp
          (E.component.normalizerMonoidHom g).toMonoidHom := by
      ext x
      exact quotientAut_apply_mk _ _ x
    rw [hq,←map_map,he]
    rfl

/-- The action retains exactly the normalizer of the original residual. -/
theorem oddAction_stabilizer_comap :
    (MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.residualImage).comap
      E.oddAction = (normalizer (f.Li E.index : Set G)).subgroupOf A.subgroup := by
  ext a
  exact E.residualImage_fixed_iff
    ⟨a,E.local_normalizes (mem_sup_right a.property)⟩

/-- The escaping complement still moves the same residual in the actual quotient. -/
theorem oddAction_moves : ¬ E.oddAction.range ≤
    MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.residualImage := by
  intro h
  apply E.moves
  intro a ha
  have hh : (⟨a,ha⟩ : A.subgroup) ∈
      (MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.residualImage).comap
        E.oddAction := h ⟨⟨a,ha⟩,rfl⟩
  rw [E.oddAction_stabilizer_comap] at hh
  exact hh

/-- The actual component action has a nontrivial odd image. -/
theorem oddAction_range_ne_bot : E.oddAction.range ≠ ⊥ := by
  intro he
  apply E.oddAction_moves
  rw [he]
  exact bot_le

/-- The actual action image retains odd order. -/
theorem oddAction_range_odd : Odd (Nat.card E.oddAction.range) :=
  A.odd.of_dvd_nat (card_range_dvd E.oddAction)

/-- The quotient of the original Sylow intersection, with no new marking. -/
def quotientSylow : Subgroup (E.component ⧸ pCore 2 E.component) :=
  ((T : Subgroup G).subgroupOf E.component).map (QuotientGroup.mk' (pCore 2 E.component))

/-- This literal subgroup really is Sylow in K/O₂(K). -/
theorem quotientSylow_isSylow :
    ∃ P : Sylow 2 (E.component ⧸ pCore 2 E.component), (P : Subgroup _) = E.quotientSylow := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T E.component
    (le_sup_right.trans le_sup_left |>.trans E.local_normalizes)
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 E.component)),?_⟩
  change (P : Subgroup E.component).map _ = _
  rw [hP]
  rfl

/-- The same odd image preserves the actual Sylow in the component quotient. -/
theorem oddAction_preserves_quotientSylow : E.oddAction.range ≤
    MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.quotientSylow := by
  rintro _ ⟨a,rfl⟩
  let g : normalizer (E.component : Set G) :=
    ⟨a,E.local_normalizes (mem_sup_right a.property)⟩
  let B := (T : Subgroup G).subgroupOf E.component
  have he : B.map (E.component.normalizerMonoidHom g).toMonoidHom = B := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      exact (A.normalizes a.property b).mp hb
    · intro b hb
      refine ⟨E.component.normalizerMonoidHom g⁻¹ b,?_,?_⟩
      · exact (A.normalizes (A.subgroup.inv_mem a.property) b).mp hb
      · rw [map_inv E.component.normalizerMonoidHom]
        exact (E.component.normalizerMonoidHom g).apply_symm_apply b
  change (B.map (QuotientGroup.mk' (pCore 2 E.component))).map
    (quotientAut (pCore 2 E.component) (E.component.normalizerMonoidHom g)).toMonoidHom = _
  have hq : (quotientAut (pCore 2 E.component) (E.component.normalizerMonoidHom g)).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 E.component)) =
      (QuotientGroup.mk' (pCore 2 E.component)).comp
        (E.component.normalizerMonoidHom g).toMonoidHom := by
    ext x
    exact quotientAut_apply_mk _ _ x
  rw [map_map,hq,←map_map,he]
  rfl

/-- Source (**): the automorphisms preserving this Sylow are not a two-group. -/
theorem quotientSylow_stabilizer_not_twoGroup : ¬ IsPGroup 2
    (MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.quotientSylow) := by
  intro hp
  obtain ⟨n,hn⟩ := (hp.to_le E.oddAction_preserves_quotientSylow).exists_card_eq
  have ho := E.oddAction_range_odd
  have hzero : n = 0 := by
    by_contra hne
    have hd : 2 ∣ Nat.card E.oddAction.range := by
      rw [hn]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  apply E.oddAction_range_ne_bot
  apply card_eq_one.mp
  rw [hn,hzero,pow_zero]

end MovedComponent

/-- The actual source escape constructs the quotient-action input to the model sieve. -/
theorem exists_movedComponent (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty (MovedComponent S f A) := by
  obtain ⟨i,K,hm,hK,hlt⟩ := (invariantFlag_geometry D S f).2.2.moved_component_source A hescape
  exact ⟨⟨i,K,hK,hlt,hm⟩⟩

/-- A Sylow-normalizer escape supplies an actual nontrivial odd Sylow stabilizer
moving the residual image, prior to identifying any component model. -/
theorem exists_moved_component_action (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      Odd (Nat.card E.oddAction.range) ∧ E.oddAction.range ≠ ⊥ ∧
      E.oddAction.range ≤ MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.quotientSylow ∧
      ¬ E.oddAction.range ≤ MulAction.stabilizer (MulAut (E.component ⧸ pCore 2 E.component)) E.residualImage := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.oddAction_range_odd,E.oddAction_range_ne_bot,
    E.oddAction_preserves_quotientSylow,E.oddAction_moves⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
