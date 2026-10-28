module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Thompson
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Preparation from the actual binary-three natural module

Natural SL₃(2) coordinates identify nonidentity vectors of W=[V,L] with
nonzero columns. Transitivity sends a nonzero C_W(C_T(v))-vector to every
nonzero vector of W, giving W≤VI. Applying the same argument to J(T)
produces a conjugate of J(T) fixing v. Point-Sylow saturation and Thompson
weak closure then identify J(C_T(v)) with J(T).

Point-Sylow saturation also forces the full half-Sylow equality, and any
nonidentity seed vector generates the literal orbit under I.

The centralizer and Thompson-movement arguments supply every field of
Prepared and hence the literal FF-action conclusions. Only the original
natural marking is assumed: neither moved-span inclusion nor the half-Sylow
equality is an input. The other source module rows still require their
own preparation.

Source: Aschbacher--Smith, 10.2.9, printed pp.751--752.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem natural_three_transitive
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (a b : (⁅D.fullModule,L⁆ : Subgroup G)) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ l : L, (MulAut.conj (l : G)) (a : G) = (b : G) := by
  have hi : Function.Injective s.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [s.kernel_eq,bot_subgroupOf])
  have hne (x : (⁅D.fullModule,L⁆ : Subgroup G)) (hx : x ≠ 1) : (s.coordinates x).toAdd ≠ 0 := by
    intro hz
    apply hx
    apply hi
    exact hz.trans (map_one s.coordinates).symm
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (s.coordinates a).toAdd (s.coordinates b).toAdd (hne a ha) (hne b hb)
  obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
  change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
  refine ⟨l,?_⟩
  have he := s.equivariant l a
  change (s.coordinates _).toAdd = specialLinearNatural 3 (e (QuotientGroup.mk' (pCore 2 L) l))
    (s.coordinates a).toAdd at he
  rw [hl] at he
  exact congrArg Subtype.val (hi (Multiplicative.toAdd.injective (he.trans hg)))

private theorem moved_le_of_transitive (c : Context D t v I)
    (htrans : ∀ a b : (⁅D.fullModule,L⁆ : Subgroup G), a ≠ 1 → b ≠ 1 →
      ∃ l : L, (MulAut.conj (l : G)) (a : G) = (b : G)) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  let S := pointSylow T v
  let W := ⁅D.fullModule,L⁆
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T))
      c.escaping.sylow_normalizes).trans (source_moved_normalizer_local_containment D)
  have hfix := inf_centralizer_ne_bot_of_pGroups S W (T.isPGroup'.to_le inf_le_left)
    (source_original_full_moved_elementary D).isPGroup hSW (source_full_moved_ne_bot D)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hfix
  have hzne : (⟨z,z.property.1⟩ : W) ≠ 1 :=
    fun he => hz (Subtype.ext (congrArg (fun a : W => (a : G)) he))
  intro w hw
  by_cases hwne : w = 1
  · exact hwne ▸ one_mem _
  obtain ⟨l,hl⟩ := htrans ⟨z,z.property.1⟩ ⟨w,hw⟩ hzne
    (fun he => hwne (congrArg Subtype.val he))
  change (MulAut.conj (l : G)) (z : G) = w at hl
  rw [←hl]
  exact (mem_normalizer_iff.mp
    (le_normalizer_conjugateSpanBy _ I (c.escaping.strict.le l.property)) z).mp
      (le_conjugateSpanBy _ _ z.property)

private theorem thompson_eq_of_transitive (c : Context D t v I)
    (htrans : ∀ a b : (⁅D.fullModule,L⁆ : Subgroup G), a ≠ 1 → b ≠ 1 →
      ∃ l : L, (MulAut.conj (l : G)) (a : G) = (b : G)) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let W := ⁅D.fullModule,L⁆
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJW : J ≤ normalizer (W : Set G) :=
    (le_inf (hJT.trans (le_normalizer_componentOrbit L T)) D.thompson_normalizes_component).trans
      (source_moved_normalizer_local_containment D)
  have hfix := inf_centralizer_ne_bot_of_pGroups J W (T.isPGroup'.to_le hJT)
    (source_original_full_moved_elementary D).isPGroup hJW (source_full_moved_ne_bot D)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hfix
  obtain ⟨w,hw,hwt⟩ := c.escaping.v_mem
  have hwne : (⟨w,hw⟩ : W) ≠ 1 := by
    intro he
    apply c.escaping.v_ne
    rw [←hwt,show w = 1 from congrArg Subtype.val he,map_one]
  obtain ⟨l,hl⟩ := htrans ⟨z,z.property.1⟩ ⟨w,hw⟩
    (fun he => hz (Subtype.ext (congrArg (fun a : W => (a : G)) he))) hwne
  have hzv : (MulAut.conj (t*l)) (z : G) = v := by
    change t*l*(z : G)*(t*l)⁻¹ = v
    change l*(z : G)*(l : G)⁻¹ = w at hl
    change t*w*t⁻¹ = v at hwt
    calc
      _ = t*(l*(z : G)*(l : G)⁻¹)*t⁻¹ := by group
      _ = v := by rw [hl,hwt]
  have hsM : Chapter1.IsSylowIn 2 (pointSylow T v)
      (D.maximalLocal ⊓ centralizer ({v} : Set G)) :=
    c.escaping.sylow.restrict
      (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right) inf_le_right
  apply source_point_thompson_eq_of_conjugate_fixed D hsM
  refine ⟨t*l,D.maximalLocal.mul_mem
    (le_normalizer_componentOrbit L T c.escaping.t_mem)
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) l.property),?_⟩
  rintro _ ⟨j,hj,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (MulAut.conj (t*l)) (z.property.2 j hj)
  rw [(MulAut.conj (t*l)).map_mul j (z : G),
    (MulAut.conj (t*l)).map_mul (z : G) j,hzv] at hh
  exact hh

/-- The original binary-three natural marking forces full moved-span inclusion.
Only the point two-group action and the genuine natural coordinates are used. -/
theorem Context.moved_le_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I :=
  moved_le_of_transitive c (natural_three_transitive e s)

/-- In the actual natural-three row, point saturation and a nonzero
Thompson-fixed vector give J(C_T(v))=J(T), with no half-Sylow equality input. -/
theorem Context.thompson_eq_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) :=
  thompson_eq_of_transitive c (natural_three_transitive e s)

/-- All preparation fields follow from the original natural-three marking. -/
theorem Context.prepared_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Prepared D v I :=
  c.prepared_of_centralizer_of_thompson_eq
    (c.centralizer_le_of_moved_le (c.moved_le_of_natural_three e s))
    (c.thompson_eq_of_natural_three e s)

/-- Actual FF-action application: the marking supplies every preparation
premise on the original orbit and quotient. -/
theorem Context.actionFacts_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ActionFacts c := c.actionFacts (c.prepared_of_natural_three e s)


/-- Natural transitivity and the prescribed saturated point force its Sylow
subgroup to be the entire half-Sylow, without assuming the terminal model. -/
theorem Context.pointSylow_eq_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    pointSylow T v = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  have hRW : R ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hfix := inf_centralizer_ne_bot_of_pGroups R W (T.isPGroup'.to_le inf_le_left)
    (source_original_full_moved_elementary D).isPGroup hRW (source_full_moved_ne_bot D)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hfix
  obtain ⟨w,hw,hwt⟩ := c.escaping.v_mem
  have hwne : (⟨w,hw⟩ : W) ≠ 1 := by
    intro he
    apply c.escaping.v_ne
    rw [←hwt,show w = 1 from congrArg Subtype.val he,map_one]
  obtain ⟨l,hl⟩ := natural_three_transitive e s ⟨z,z.property.1⟩ ⟨w,hw⟩
    (fun he => hz (Subtype.ext (congrArg (fun a : W => (a : G)) he))) hwne
  have hzv : (MulAut.conj (t*l)) (z : G) = v := by
    change t*l*(z : G)*(t*l)⁻¹ = v
    change l*(z : G)*(l : G)⁻¹ = w at hl
    change t*w*t⁻¹ = v at hwt
    calc
      _ = t*(l*(z : G)*(l : G)⁻¹)*t⁻¹ := by group
      _ = v := by rw [hl,hwt]
  let a := MulAut.conj (t*l)
  have hRC : R.map a.toMonoidHom ≤ centralizer ({v} : Set G) := by
    rintro _ ⟨r,hr,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg a (z.property.2 r hr)
    rw [a.map_mul r (z : G), a.map_mul (z : G) r,hzv] at hh
    exact hh
  obtain ⟨g,_,hg⟩ := ChapterB.exists_conjugate_le_relative_sylow _ _ (R.map a.toMonoidHom)
    c.escaping.sylow ((T.isPGroup'.to_le inf_le_left).map a.toMonoidHom) hRC
  apply eq_of_le_of_card_ge (le_inf inf_le_left c.escaping.sylow_normalizes)
  have he₁ : Nat.card (R.map a.toMonoidHom) = Nat.card R :=
    (Nat.card_congr (R.equivMapOfInjective a.toMonoidHom a.injective).toEquiv).symm
  have he₂ : Nat.card ((R.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom) =
      Nat.card (R.map a.toMonoidHom) :=
    (Nat.card_congr ((R.map a.toMonoidHom).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm
  exact he₁ ▸ he₂ ▸ card_le_of_le hg


/-- A nonidentity seed vector generates the entire literal I-orbit in the
natural-three row. This retains the original vector, I and conjugation action. -/
theorem Context.orbit_eq_of_natural_three_seed (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {u : G} (hu : u ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hu1 : u ≠ 1) : orbitModule D v I = conjugateSpanBy (zpowers u) I := by
  let U := conjugateSpanBy (zpowers u) I
  have hW : ⁅D.fullModule,L⁆ ≤ U := by
    intro w hw
    by_cases hw1 : w = 1
    · exact hw1 ▸ U.one_mem
    obtain ⟨l,hl⟩ := natural_three_transitive e s ⟨u,hu.1⟩ ⟨w,hw⟩
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
    change (MulAut.conj (l : G)) u = w at hl
    rw [←hl]
    exact (mem_normalizer_iff.mp
      (le_normalizer_conjugateSpanBy (zpowers u) I (c.escaping.strict.le l.property)) u).mp
        (le_conjugateSpanBy _ _ (mem_zpowers u))
  apply le_antisymm
  · exact conjugateSpanBy_le (inf_le_left.trans hW) (le_normalizer_conjugateSpanBy _ _)
  · exact conjugateSpanBy_mono (zpowers_le.mpr hu) le_rfl

end CFSG.Quasithin.Chapter10.PointControl.Constrained
