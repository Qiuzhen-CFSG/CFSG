module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Scalar
public import Theory.SpecificGroups.PSL3.LinearThreeNaturalScalars
public import Theory.SpecificGroups.SymplecticFour.NaturalScalars
public import Theory.Representation.G2.NaturalScalars
public import Theory.Representation.SymplecticNatural
public import CFSG.Quasithin.Chapter10.SourceA5PointActionSeed
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Concrete torus contradictions on the original constrained action

Choose a prime dividing the rank-one field-unit group and avoiding the
outer automorphism order. The original component forces its section scalars
to fix [V,L]. In the actual containing action, the smaller image's two-core
fixes the same original moved vectors: it lifts to O₂(L), which centralizes V.
The explicit SL₃, Sp₄ and G₂ model tori contradict that fixedness.

A proved nonfixed original seed survives every coordinate map whose kernel
is component-fixed. Consequently the applications allow the literal B.5.1
central quotient, as well as natural/dual sums, without assuming that VI is
itself irreducible. The source-section applications construct that projection
and derive full movement from fixed-span promotion. All group isomorphisms,
local-subgroup images and equivariance statements use the original quotient.

These results discharge the concrete scalar and fixed-vector requirements.
The owner qt-d-10-nona5-point-constrained still constructs the containing-model
markings and the full-span premise, and retains preparation, the other source
cases and final assembly. No unconditional 10.2.9 theorem is asserted here.
Source: Aschbacher--Smith, 10.2.9, printed pp.751--752.
-/

@[expose] public section
open Matrix.PSL3.LinearThree
open scoped commutatorElement
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 Chapter4 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
  (c : Context D t v I)
variable [((internalModule D v I)).Normal] [IsElementaryAbelian 2 (internalModule D v I)]

/-- Fixed-span promotion makes the actual orbit fully moved under its component image. -/
theorem Context.fully_moved_of_moved_le (c : Context D t v I)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    ChapterB.QuasisimpleSource.moved (V := Additive (internalModule D v I)) (action (internalModule D v I))
        (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) = ⊤ :=
  source_a5_point_action_fully_moved D I c.escaping.strict.le c.escaping.escapes
    ((Subgroup.centralizer_le_normalizer _).trans c.escaping.moved_normalizer) hspan c.reduced

/-- The literal smaller image's two-core fixes every original moved vector in VI. -/
theorem Context.small_image_core_fixes_moved (af : ActionFacts c)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (b : ↥((Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) : Subgroup
        (ActionQuotient (internalModule D v I)))) (hb : b ∈ ((Subgroup.subgroupOf (Subgroup.map (actionMk
        (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule
        D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).pCoreIn 2) (z : (internalModule D v I))
    (hzW : ((z : (pointJoin T v I)) : G) ∈ ⁅D.fullModule,L⁆) :
    action (internalModule D v I) (b : ActionQuotient (internalModule D v I)) (Additive.ofMul z) = Additive.ofMul z
        := by
  let K := L.subgroupOf (pointJoin T v I)
  let q := actionMk (internalModule D v I)
  let f := q.subgroupMap K
  have hLH : L ≤ (pointJoin T v I) := c.escaping.strict.le.trans le_sup_left
  have hKA : K.map q ≤ (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))
      := map_mono (comap_mono c.escaping.strict.le)
  let eB : (Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
      v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) ≃* K.map q
      := subgroupOfEquivOfLe hKA
  have hcore : (pCore 2 K).map f = pCore 2 (K.map q) := by
    rw [←f.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective K)
      (c.small_image_twoCore af hz).1,map_comap_eq_self_of_surjective (q.subgroupMap_surjective K)]
  obtain ⟨b,hb,rfl⟩ := hb
  have hb' : eB b ∈ pCore 2 (K.map q) := by
    rw [←pCore_map_iso 2 eB]
    exact mem_map_of_mem eB.toMonoidHom hb
  rw [←hcore] at hb'
  obtain ⟨l,hl,he⟩ := hb'
  have he' : q (l : (pointJoin T v I)) = ((b : ↥((Subgroup.map (actionMk (internalModule D v I))
      (Subgroup.subgroupOf I (pointJoin T v I))) : Subgroup (ActionQuotient (internalModule D v I)))) :
      ActionQuotient (internalModule D v I)) := congrArg Subtype.val he
  change action (internalModule D v I) b.val.val (Additive.ofMul z) = Additive.ofMul z
  rw [←he']
  have hlG : ((l : (pointJoin T v I)) : G) ∈ L.pCoreIn 2 := by
    have hmap := map_pCoreIn_of_injective 2 K ((pointJoin T v I)).subtype ((pointJoin T v I)).subtype_injective
    rw [map_subgroupOf_eq_of_le hLH] at hmap
    exact hmap ▸ mem_map_of_mem ((pointJoin T v I)).subtype (mem_map_of_mem K.subtype hl)
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hc := source_component_core_centralizes_fullModule D hlG _ (hWV hzW)
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have ha := congrArg ((pointJoin T v I)).subtype (action_apply (internalModule D v I) (l : (pointJoin T v I))
      (Additive.ofMul z))
  exact ha.trans (by
    change ((l : (pointJoin T v I)) : G) * ((z : (pointJoin T v I)) : G) * ((l : (pointJoin T v I)) : G)⁻¹ = ((z :
        (pointJoin T v I)) : G)
    rw [←hc,mul_inv_cancel_right])
private theorem no_rankOne_natural_model
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) X V) (P : Subgroup X)
    (E : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) ≃* X) (hB :
        ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
        I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.toMonoidHom = P)
    (j : Additive (internalModule D v I) →ₗ[ZMod 2] V) (hj : ∀ z, j z = 0 → z ∈ fixedSpace (V := Additive
        (internalModule D v I)) (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (hcoord : ∀ (x : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) (z
        : Additive (internalModule D v I)),
      j (action (internalModule D v I) (x : ActionQuotient (internalModule D v I)) z) = σ (E x) (j z))
    (hscalar : ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card F - 1 →
      ∀ z : V, z ≠ 0 → (∀ b ∈ P.pCoreIn 2, σ b z = z) →
        ∃ x : X, orderOf x = p ∧ x ∈ sectionCentralizer P ∧ σ x z ≠ z) : False := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hh
    rw [Theory.PSL2.sl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  obtain ⟨p,hp,hp2,hpd,hfix⟩ := c.exists_rankOne_action_scalar_obstruction af hF hn e hspan
  let : Fact p.Prime := ⟨hp⟩
  have hpF : p ∣ Nat.card F - 1 := by simpa only [hF] using hpd
  obtain ⟨z,hzW,hzP,hzn⟩ := source_a5_point_action_fixed_seed D I
    c.escaping.strict.le hspan c.reduced
  have hjz : j z ≠ 0 := fun h => hzn (hj z h)
  have hfixed : ∀ b ∈ P.pCoreIn 2, σ b (j z) = j z := by
    intro b hb
    have hcore : (((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L
        (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v
        I))))).pCoreIn 2).map E.toMonoidHom = P.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ _ E.injective,hB]
    rw [←hcore] at hb
    obtain ⟨a,ha,rfl⟩ := hb
    exact (hcoord a z).symm.trans (congrArg j
      (c.small_image_core_fixes_moved af hz a ha z.toMul hzW))
  obtain ⟨x,hxp,hxB,hmove⟩ := hscalar p hpF _ hjz hfixed
  have hxC : E.symm x ∈ sectionCentralizer (Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
      (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
      (Subgroup.subgroupOf I (pointJoin T v I)))) := by
    have hh := Subgroup.twoCoreSectionCentralizer_map_equiv_le (((Subgroup.subgroupOf (Subgroup.map (actionMk
        (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule
        D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom) E.symm
      (mem_map_of_mem E.symm.toMonoidHom (hB.symm ▸ hxB))
    have hb : (((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L
        (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v
        I))))).map E.toMonoidHom).map E.symm.toMonoidHom = (Subgroup.subgroupOf (Subgroup.map (actionMk
        (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule
        D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) :=
      (map_symm_eq_iff_map_eq _).mpr rfl
    simpa only [hb,sectionCentralizer,MulEquiv.coe_toMonoidHom] using hh
  apply hfix (E.symm x) ((E.symm.orderOf_eq x).trans hxp) hxC z.toMul hzW
  intro he
  change action (internalModule D v I) (E.symm x : ActionQuotient (internalModule D v I)) z = z at he
  apply hmove
  have hc := hcoord (E.symm x) z
  rw [he,E.apply_symm_apply] at hc
  exact hc.symm

/-- The actual SL₃ natural/dual sum row has a concrete torus contradiction.
All actions and the smaller local subgroup are marked in the same coordinates. -/
theorem Context.no_linearThree_natural_sum
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (E : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) F)
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.toMonoidHom = pointLocalSL F ∨ ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom = lineLocalSL F)
    {ι κ : Type*}
    (j : Additive (internalModule D v I) →ₗ[ZMod 2] ((ι → Fin 3 → F) × (κ → Fin 3 → F)))
    (hj : ∀ z, j z = 0 → z ∈ fixedSpace (V := Additive (internalModule D v I)) (action (internalModule D v I))
        (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))
    (hcoord : ∀ (x : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) (z
        : Additive (internalModule D v I)),
      j (action (internalModule D v I) (x : ActionQuotient (internalModule D v I)) z) =
        ((fun i => (E x).val.mulVec ((j z).1 i)),
          (fun k => (E x)⁻¹.val.transpose.mulVec ((j z).2 k)))) : False := by
  obtain ⟨p,hp,hp2,hpd,hfix⟩ := c.exists_rankOne_action_scalar_obstruction af hF hn e hspan
  let : Fact p.Prime := ⟨hp⟩
  have hpF : p ∣ Nat.card F - 1 := by simpa only [hF] using hpd
  obtain ⟨x,hxp,hxB,hxn,hxd⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) F,
      orderOf x = p ∧ x ∈ sectionCentralizer (((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
          (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
          (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom) ∧
      (∀ z : Fin 3 → F, x.val.mulVec z = z → z = 0) ∧
      (∀ z : Fin 3 → F, x⁻¹.val.transpose.mulVec z = z → z = 0) := by
    rcases hB with hb | hb
    · simpa only [hb,sectionCentralizer] using Scalar.exists_point_scalar F p hpF
    · simpa only [hb,sectionCentralizer] using Scalar.exists_line_scalar F p hpF
  have hxC : E.symm x ∈ sectionCentralizer (Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
      (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
      (Subgroup.subgroupOf I (pointJoin T v I)))) := by
    have hh := Subgroup.twoCoreSectionCentralizer_map_equiv_le (((Subgroup.subgroupOf (Subgroup.map (actionMk
        (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule
        D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom) E.symm
      (mem_map_of_mem E.symm.toMonoidHom hxB)
    have hb : (((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L
        (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v
        I))))).map E.toMonoidHom).map E.symm.toMonoidHom = (Subgroup.subgroupOf (Subgroup.map (actionMk
        (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule
        D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) :=
      (map_symm_eq_iff_map_eq _).mpr rfl
    simpa only [hb,sectionCentralizer,MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨z,hzW,hzP,hzn⟩ := source_a5_point_action_fixed_seed D I
    c.escaping.strict.le hspan c.reduced
  apply hfix (E.symm x) ((E.symm.orderOf_eq x).trans hxp) hxC z.toMul hzW
  intro he
  change action (internalModule D v I) (E.symm x : ActionQuotient (internalModule D v I)) z = z at he
  have hc := hcoord (E.symm x) z
  rw [he,E.apply_symm_apply] at hc
  have hz : j z = 0 := by
    apply Prod.ext
    · funext i
      exact hxn _ (congrFun (congrArg Prod.fst hc) i).symm
    · funext k
      exact hxd _ (congrFun (congrArg Prod.snd hc) k).symm
  exact hzn (hj z hz)
/-- Both symplectic local markings contradict the scalar obstruction on the
original moved vectors. The actual two-core fixed-space premise is derived. -/
theorem Context.no_symplecticFour_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (E : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F)
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointLocal ∨
      ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
          I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
          E.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeLocal)
    (j : Additive (internalModule D v I) →ₗ[ZMod 2] Theory.SpecificGroups.SymplecticFour.Vector F)
    (hj : ∀ z, j z = 0 → z ∈ fixedSpace (V := Additive (internalModule D v I)) (action (internalModule D v I))
        (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))
    (hcoord : ∀ (x : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) (z
        : Additive (internalModule D v I)),
      j (action (internalModule D v I) (x : ActionQuotient (internalModule D v I)) z) = E x • j z) : False := by
  let σ := Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hs (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
      (hp : P = Theory.SpecificGroups.SymplecticFour.pointLocal ∨
        P = Theory.SpecificGroups.SymplecticFour.planeLocal) :
      ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card F - 1 →
        ∀ z, z ≠ 0 → (∀ b ∈ P.pCoreIn 2, σ b z = z) →
          ∃ x, orderOf x = p ∧ x ∈ sectionCentralizer P ∧ σ x z ≠ z := by
    intro p _ hpd z hz hfix
    obtain ⟨x,hxp,hnx,hcx,hm⟩ : ∃ x : Theory.SpecificGroups.SymplecticFour.Sp F,
        orderOf x = p ∧ x ∈ normalizer (P : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) ∧
        (∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2) ∧ x • z ≠ z := by
      rcases hp with rfl | rfl
      · exact Theory.SpecificGroups.SymplecticFour.NaturalScalars.point_prime_moves_fixed
          hF hn hpd z hz hfix
      · exact Theory.SpecificGroups.SymplecticFour.NaturalScalars.plane_prime_moves_fixed
          hF hn hpd z hz hfix
    exact ⟨x,hxp,(mem_commutatorPreimage_iff _ _ _
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)) x).mpr ⟨hnx,hcx⟩,hm⟩
  exact no_rankOne_natural_model c af hF hn e hspan σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
      (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D
      v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom)
    E rfl j hj hcoord (hs _ hB)

/-- The short and long G₂ local markings have the same contradiction on the
literal natural module, for every nonbinary field degree. -/
theorem Context.no_g2_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (E : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) ≃*
        Atlas.G2.Model F)
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.toMonoidHom = Atlas.G2.LieParabolicSetup.local₁ ∨
      ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
          I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
          E.toMonoidHom = Atlas.G2.LieParabolicSetup.local₂)
    (j : Additive (internalModule D v I) →ₗ[ZMod 2] Atlas.G2.Natural.Space F)
    (hj : ∀ z, j z = 0 → z ∈ fixedSpace (V := Additive (internalModule D v I)) (action (internalModule D v I))
        (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))
    (hcoord : ∀ (x : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) (z
        : Additive (internalModule D v I)),
      j (action (internalModule D v I) (x : ActionQuotient (internalModule D v I)) z) = Atlas.G2.Natural.action F
          (E x) (j z)) : False := by
  let σ := Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F)
  have hs (P : Subgroup (Atlas.G2.Model F))
      (hp : P = Atlas.G2.LieParabolicSetup.local₁ ∨ P = Atlas.G2.LieParabolicSetup.local₂) :
      ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card F - 1 →
        ∀ z, z ≠ 0 → (∀ b ∈ P.pCoreIn 2, σ b z = z) →
          ∃ x, orderOf x = p ∧ x ∈ sectionCentralizer P ∧ σ x z ≠ z := by
    intro p _ hpd z hz hfix
    obtain ⟨x,hxp,hnx,hcx,hm⟩ : ∃ x : Atlas.G2.Model F,
        orderOf x = p ∧ x ∈ normalizer (P : Set (Atlas.G2.Model F)) ∧
        (∀ b ∈ P, ⁅x,b⁆ ∈ P.pCoreIn 2) ∧ σ x z ≠ z := by
      rcases hp with rfl | rfl
      · exact Atlas.G2.NaturalScalars.short_prime_moves_fixed hpd z hz hfix
      · exact Atlas.G2.NaturalScalars.long_prime_moves_fixed hpd z hz hfix
    exact ⟨x,hxp,(mem_commutatorPreimage_iff _ _ _
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)) x).mpr ⟨hnx,hcx⟩,hm⟩
  exact no_rankOne_natural_model c af hF hn e hspan σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
      (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D
      v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom)
    E rfl j hj hcoord (hs _ hB)

/-- The concrete natural SL₃ action excludes both marked local subgroups.
A central kernel is allowed: only the original nonfixed seed must survive. -/
theorem Context.no_linearThree_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (E : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) F)
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.toMonoidHom = pointLocalSL F ∨ ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom = lineLocalSL F)
    (j : Additive (internalModule D v I) →ₗ[ZMod 2] (Fin 3 → F))
    (hj : ∀ z, j z = 0 → z ∈ fixedSpace (V := Additive (internalModule D v I)) (action (internalModule D v I))
        (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))
    (hcoord : ∀ (x : (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I)))) (z
        : Additive (internalModule D v I)),
      j (action (internalModule D v I) (x : ActionQuotient (internalModule D v I)) z) = (E x).val.mulVec (j z)) :
          False := by
  let σ := Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
  apply no_rankOne_natural_model c af hF hn e hspan σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
      (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D
      v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom) E rfl j hj hcoord
  intro p _ hp z hz _
  obtain ⟨x,hxp,hxB,hxn,hxd⟩ : ∃ x : Matrix.SpecialLinearGroup (Fin 3) F,
      orderOf x = p ∧ x ∈ sectionCentralizer (((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I))
          (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D v I))
          (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom) ∧
      (∀ w : Fin 3 → F, x.val.mulVec w = w → w = 0) ∧
      (∀ w : Fin 3 → F, x⁻¹.val.transpose.mulVec w = w → w = 0) := by
    rcases hB with hb | hb
    · simpa only [hb,sectionCentralizer] using Scalar.exists_point_scalar F p hp
    · simpa only [hb,sectionCentralizer] using Scalar.exists_line_scalar F p hp
  exact ⟨x,hxp,hxB,fun h => hz (hxn z h)⟩

open ChapterB.QuasisimpleSource

/-- The literal B.5.1 central quotient supplies the allowed kernel, so a marked
natural SL₃ section is excluded without assuming that VI itself is irreducible. -/
theorem Context.no_linearThree_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)))
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.groupEquiv.toMonoidHom = pointLocalSL F ∨
      ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
          I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
          E.groupEquiv.toMonoidHom = lineLocalSL F) : False := by
  have hm := c.fully_moved_of_moved_le hspan
  apply c.no_linearThree_natural af hF hn e hspan E.groupEquiv hB
    (E.linearEquiv.toLinearMap.comp (s.fullProjection hm))
  · intro z hz
    apply (s.fullProjection_eq_zero_iff hm z).mp
    exact E.linearEquiv.injective (hz.trans E.linearEquiv.map_zero.symm)
  · intro x z
    change E.linearEquiv (s.fullProjection hm (action (internalModule D v I) (x : ActionQuotient (internalModule D
        v I)) z)) = _
    rw [s.fullProjection_intertwines]
    exact E.intertwines x (s.fullProjection hm z)

/-- The actual central-quotient projection discharges the kernel premise for
both symplectic local markings; no two-core fixed-vector callback remains. -/
theorem Context.no_symplecticFour_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.groupEquiv.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointLocal ∨
      ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
          I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
          E.groupEquiv.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeLocal) : False := by
  have hm := c.fully_moved_of_moved_le hspan
  apply c.no_symplecticFour_natural af hF hn e hspan E.groupEquiv hB
    (E.linearEquiv.toLinearMap.comp (s.fullProjection hm))
  · intro z hz
    apply (s.fullProjection_eq_zero_iff hm z).mp
    exact E.linearEquiv.injective (hz.trans E.linearEquiv.map_zero.symm)
  · intro x z
    change E.linearEquiv (s.fullProjection hm (action (internalModule D v I) (x : ActionQuotient (internalModule D
        v I)) z)) = _
    rw [s.fullProjection_intertwines]
    exact E.intertwines x (s.fullProjection hm z)

/-- Both G₂ local markings are excluded on the literal B.5.1 central quotient,
with its projection applied to a proved surviving original moved vector. -/
theorem Context.no_g2_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F)))
    (hB : ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T
        v I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
        E.groupEquiv.toMonoidHom = Atlas.G2.LieParabolicSetup.local₁ ∨
      ((Subgroup.subgroupOf (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v
          I))) (Subgroup.map (actionMk (internalModule D v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map
          E.groupEquiv.toMonoidHom = Atlas.G2.LieParabolicSetup.local₂) : False := by
  have hm := c.fully_moved_of_moved_le hspan
  apply c.no_g2_natural af hF hn e hspan E.groupEquiv hB
    (E.linearEquiv.toLinearMap.comp (s.fullProjection hm))
  · intro z hz
    apply (s.fullProjection_eq_zero_iff hm z).mp
    exact E.linearEquiv.injective (hz.trans E.linearEquiv.map_zero.symm)
  · intro x z
    change E.linearEquiv (s.fullProjection hm (action (internalModule D v I) (x : ActionQuotient (internalModule D
        v I)) z)) = _
    rw [s.fullProjection_intertwines]
    exact E.intertwines x (s.fullProjection hm z)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
