module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SmallImage
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Arithmetic
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder

/-!
# Arbitrary-prime scalar obstruction on the constrained action

An odd scalar prime dividing the smaller quotient and avoiding its outer
automorphism group places every prime-power lift in the original component
orbit. The section centralizer there fixes [V,L]. A scalar in the literal
point-action quotient lifts through its solvable kernel without changing
its image; the smaller kernel is a two-group. Conjugation equivariance then
excludes movement of every original moved vector lying in VI.

For a binary SL₂ quotient a primitive-divisor argument chooses a scalar
prime for every field degree greater than one, including degree six. Thus
no divisibility-by-three assumption is imposed on the field-unit torus.
The concrete model must still supply the moving scalar; that recognition
and the final exclusion remain with qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith, 10.2.9, printed pp.751--752, using 10.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 Chapter4 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Prime-power section scalars in the original configuration fix its moved factor. -/
theorem Context.primePower_scalar_fixes_moved (c : Context D t v I)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))))
    {x : G} (hx : ∃ n : ℕ, x ^ (p ^ n) = 1) (hxL : x ∈ sectionCentralizer L) :
    x ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D c.escaping.t_mem
        c.escaping.t_not_normalizes c.escaping.crossed))
  have hxM : x ∈ D.maximalLocal := c.escaping.component_normalizer
    (((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hxL)
  have hx0 : x ∈ localOrbit T L := by
    rw [←Quasisimple.primeToResidual_eq_orbit D hn hz p hp hd ho]
    let xM : D.maximalLocal := ⟨x,hxM⟩
    apply mem_map_of_mem D.maximalLocal.subtype (x := xM)
    obtain ⟨n,hn⟩ := hx
    exact mem_primeToResidual_of_pow (n := n) (Subtype.ext hn)
  exact Quasisimple.orbit_sectionCentralizer_centralizes_moved D hz hn
    c.escaping.t_mem c.escaping.t_not_normalizes hsep ⟨hx0,hxL⟩

omit [Finite G] in
private theorem sectionCentralizer_subgroupOf_map_le (I : Subgroup G) (hLI : L ≤ I) :
    (sectionCentralizer (L.subgroupOf I)).map I.subtype ≤ sectionCentralizer L := by
  have hc := (le_sectionCentralizer_iff (sectionCentralizer (L.subgroupOf I))
    (L.subgroupOf I)).mp le_rfl
  apply (le_sectionCentralizer_iff _ L).mpr
  constructor
  · have hn := (map_mono (f := I.subtype) hc.1).trans (le_normalizer_map I.subtype)
    rwa [map_subgroupOf_eq_of_le hLI] at hn
  · have hh := map_mono (f := I.subtype) hc.2
    rwa [map_commutator, map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hLI] at hh

/-- A scalar in a solvable-kernel image has a lift fixing the original moved group. -/
theorem Context.image_prime_lifts_to_moved_centralizer (c : Context D t v I)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))))
    {Q : Type*} [Group Q] [Finite Q] (f : I →* Q) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker]
    (hkn : f.ker ≤ normalizer (L.subgroupOf I : Set I))
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    {x : Q} (hxp : orderOf x = p)
    (hxL : x ∈ sectionCentralizer ((L.subgroupOf I).map f)) :
    ∃ y : I, f y = x ∧ (y : G) ∈
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (L.subgroupOf I) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe c.escaping.strict.le).symm.toMonoidHom) (subgroupOfEquivOfLe c.escaping.strict.le).symm.surjective
  obtain ⟨y,hy,n,hnpow⟩ := f.exists_primePower_lift hf (p := p) (n := 1)
    (by simpa only [pow_one] using hxp)
  have hyL : y ∈ sectionCentralizer (L.subgroupOf I) :=
    core_sectionCentralizer_comap_le f (L.subgroupOf I) hkn hk (by
      change f y ∈ sectionCentralizer ((L.subgroupOf I).map f)
      rwa [hy])
  have hyLG : (y : G) ∈ sectionCentralizer L :=
    sectionCentralizer_subgroupOf_map_le I c.escaping.strict.le (mem_map_of_mem I.subtype hyL)
  refine ⟨y,hy,c.primePower_scalar_fixes_moved hz p hp hd ho ?_ hyLG⟩
  exact ⟨n,congrArg Subtype.val hnpow⟩


/-- Literal consumer: a permitted scalar prime in the component image cannot
move any original moved vector in VI. The original quotient map is retained. -/
theorem Context.no_moving_action_prime (c : Context D t v I) (af : ActionFacts c)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))))
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    let H := pointJoin T v I
    let U := internalModule D v I
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let K := I.subgroupOf H
    let q := actionMk U
    let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
    ∀ (x : K.map q), orderOf x = p → x ∈ sectionCentralizer B →
      ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
        action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False := by

  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I
  let U := V.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let K := I.subgroupOf H
  let A := L.subgroupOf H
  let q := actionMk U
  let B := (A.map q).subgroupOf (K.map q)
  change ∀ (x : K.map q), orderOf x = p → x ∈ sectionCentralizer B →
    ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
      action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False
  intro x hxp hxB z hzW hmove
  let i : I ≃* K := (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm
  let g := q.subgroupMap K
  let f : I →* K.map q := g.comp i.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective K).comp i.surjective
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  let a : L.subgroupOf I ≃* A :=
    (subgroupOfEquivOfLe c.escaping.strict.le).trans (subgroupOfEquivOfLe hLH).symm
  let : Group.IsSolvable g.ker := af.solvable_kernel
  let j : f.ker →* g.ker :=
    (i.toMonoidHom.comp f.ker.subtype).codRestrict g.ker (fun y => y.property)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := j) (by
    intro y y' he
    apply Subtype.ext
    exact i.injective (congrArg Subtype.val he))
  have hV : V ≤ H := (conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans c.escaping.strict.le))).trans le_sup_left
  have hkn : f.ker ≤ normalizer (L.subgroupOf I : Set I) := by
    intro y hy
    have hyq : q ((i y : K) : H) = 1 := congrArg Subtype.val hy
    have hyC : ((i y : K) : H) ∈ centralizer (U : Set H) :=
      (QuotientGroup.eq_one_iff _).mp hyq
    have hyVG : (y : G) ∈ centralizer (V : Set G) := by
      intro w hw
      exact congrArg H.subtype (hyC ⟨w,hV hw⟩ hw)
    have hyN := source_a5_point_action_centralizer_normalizes_component
      D c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed V hspan
        ((Subgroup.centralizer_le_normalizer _).trans c.escaping.moved_normalizer) hyVG
    intro l
    exact hyN (l : G)
  have hkA := (c.small_image_twoCore af hz).1
  let fL := f.subgroupMap (L.subgroupOf I)
  let gL := q.subgroupMap A
  let ja : fL.ker →* gL.ker := (a.toMonoidHom.comp fL.ker.subtype).codRestrict gL.ker (by
    intro y
    apply Subtype.ext
    exact congrArg (fun b : (L.subgroupOf I).map f => ((b : K.map q) : ActionQuotient U)) y.property)
  have hk : IsPGroup 2 fL.ker := hkA.of_injective ja (by
    intro y y' he
    apply Subtype.ext
    exact a.injective (congrArg Subtype.val he))
  have hB : (L.subgroupOf I).map f = B := by
    ext b
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact mem_map.mpr ⟨⟨l,hLH hl⟩,hl,rfl⟩
    · rintro ⟨l,hl,he⟩
      exact ⟨⟨l,c.escaping.strict.le hl⟩,hl,Subtype.ext he⟩
  have hxL : x ∈ sectionCentralizer ((L.subgroupOf I).map f) := by
    rwa [hB]
  obtain ⟨y,hy,hyC⟩ := c.image_prime_lifts_to_moved_centralizer hz p hp hd ho f hf hkn hk hxp hxL
  apply hmove
  have hyq : q ((i y : K) : H) = (x : ActionQuotient U) := congrArg Subtype.val hy
  rw [←hyq]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have ha := congrArg H.subtype (action_apply U ((i y : K) : H) (Additive.ofMul z))
  exact ha.trans (by
    change (y : G) * ((z : H) : G) * (y : G)⁻¹ = ((z : H) : G)
    rw [←hyC _ hzW,mul_inv_cancel_right])

/-- Every nonbinary rank-one field supplies an admissible scalar prime on the
literal action quotient. No assumption that three divides the torus is used. -/
theorem Context.exists_rankOne_action_scalar_obstruction
    (c : Context D t v I) (af : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    ∃ (p : ℕ) (_ : p.Prime), p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧
      (let H := pointJoin T v I
       let U := internalModule D v I
       letI := c.reduced.normal
       letI := c.reduced.elementary
       let K := I.subgroupOf H
       let q := actionMk U
       let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
       ∀ (x : K.map q), orderOf x = p → x ∈ sectionCentralizer B →
         ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
           action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hh
    rw [Theory.PSL2.sl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  obtain ⟨p,hp,hp2,hpd,hpn⟩ := Quasisimple.exists_scalar_prime hn
  let : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    have hdiv : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      have he : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        nlinarith [Nat.sub_add_cancel hpow,
          Nat.sub_add_cancel (Nat.one_le_pow 2 (2 ^ n) (by positivity))]
      rw [he]
      exact dvd_mul_right _ _
    exact (hpd.trans hdiv).trans (dvd_mul_left _ _)
  have ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))) := by
    rw [Nat.card_congr (MulAut.outerCongr (e.trans (Theory.PSL2.sl2QuotientEquiv F))).toEquiv,
      Theory.PSL2.outer_card_eq_field_degree F hF]
    exact hpn
  exact ⟨p,hp,hp2,hpd,c.no_moving_action_prime af hz p hp2 hd ho hspan⟩

/-- The zero-kernel natural marking discharges preparation and orbit inclusion
in the actual scalar obstruction, before any containing-model choice. -/
theorem Context.rankOne_zero_kernel_scalar_obstruction (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) (hzero : sourceMovedFixed D = ⊥) :
    ∃ (p : ℕ) (_ : p.Prime), p ≠ 2 ∧
      (let H := pointJoin T v I
       let U := internalModule D v I
       letI := c.reduced.normal
       letI := c.reduced.elementary
       let K := I.subgroupOf H
       let q := actionMk U
       let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
       ∀ (x : K.map q), orderOf x = p → x ∈ sectionCentralizer B →
         ∀ z : U, ((z : H) : G) ∈ ⁅D.fullModule,L⁆ →
           action U (x : ActionQuotient U) (Additive.ofMul z) ≠ Additive.ofMul z → False) := by
  have af := c.actionFacts_of_rankOneNatural hmodel
  have hspan := c.moved_le_of_rankOneNatural_of_fixed_eq_bot hmodel hzero
  obtain ⟨n,hn,e,_⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨p,hp,hp2,_,hfix⟩ := c.exists_rankOne_action_scalar_obstruction af hF hn e hspan
  exact ⟨p,hp,hp2,hfix⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
