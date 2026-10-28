module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.OriginalAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankTwoReduction
public import Theory.SpecificGroups.ProjectiveLinearThree

/-!
# Recognizing the original constrained component before row marking

The literal action kernel normalizes L, so the moving-scalar obstruction
applies to the original point-fixed seed. This seed survives the B.5.1
central projection, and VI is fully moved. Transporting the actual local
component and the seed through the source coordinates excludes every
rank-two containing action without assuming [V_M,L] ≤ VI.

The complete source conclusion therefore has an A₇ or binary-linear actor.
The original two-core quotient is SL₃(2) in either case. Cubic component
order already prepares this literal action. The earlier nonnormal-component
catalogue shows that every remaining three-free quotient is a genuine
Suzuki group. Thus only SL₃(2) and Suzuki remain on the full original
Context, with actual quotient isomorphisms and no module marking assumed.

Source connects these results to the point-control contract. Recognition
of the original moved-module coordinates for these two quotient families
remains with this owner. The original full module, local module, VI and
fixed kernels remain distinct.

Source: Aschbacher--Smith 1.2.1(3), B.5.1 and10.2.9,
printed pp.504,99--103,751--752.
-/

public noncomputable section
open Matrix.PSL3.LinearThree
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 Chapter4 ChapterB.InternalThompsonAction
private def conjugateActionEquiv {A B V W : Type*} [Group A] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A V} {σ : Representation (ZMod 2) B W}
    (E : ActionEquiv ρ σ) (g : B) : ActionEquiv ρ σ where
  groupEquiv := E.groupEquiv.trans (MulAut.conj g)
  linearEquiv := E.linearEquiv.trans (LinearEquiv.ofBijective (σ g) (σ.apply_bijective g))
  intertwines x v := by
    change σ g (E.linearEquiv (ρ x v)) = σ (g * E.groupEquiv x * g⁻¹) (σ g (E.linearEquiv v))
    rw [E.intertwines]
    simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]

private def composeAction {A B C U V W : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A U} {σ : Representation (ZMod 2) B V}
    {τ : Representation (ZMod 2) C W} (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := by
    change f.linearEquiv (e.linearEquiv (ρ g v)) = _
    rw [e.intertwines,f.intertwines]
    rfl

private def liftCentralAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A N : Subgroup Q} (hAN : A ≤ N)
    (s : MovedSection (ρ.comp N.subtype) (A.subgroupOf N))
    (r : MovedSection ρ A) :
    ActionEquiv (r.action.comp A.subtype) (s.action.comp (A.subgroupOf N).subtype) := by
  apply s.componentEmbeddingEquiv r (subgroupOfEquivOfLe hAN).symm LinearMap.id
    (fun _ _ h => h)
  · intros; rfl
  · rw [moved_comp_map,map_subgroupOf_eq_of_le hAN,Submodule.map_id]

private def liftMovedAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A N : Subgroup Q} (hAN : A ≤ N)
    (s : MovedSection (ρ.comp N.subtype) (A.subgroupOf N))
    (r : MovedSection ρ A) :
    ActionEquiv (r.space.toRepresentation.comp A.subtype)
      (s.space.toRepresentation.comp (A.subgroupOf N).subtype) where
  groupEquiv := (subgroupOfEquivOfLe hAN).symm
  linearEquiv := LinearEquiv.ofEq _ _ (by
    rw [r.space_eq,s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN])
  intertwines g v := by apply Subtype.ext; rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
private theorem Context.original_scalar_obstruction
    (c : Context D t v I) (af : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    :
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
  exact ⟨p,hp,hp2,hpd,c.no_moving_original_action_prime af hz p hp2 hd ho⟩


section
variable (c : Context D t v I)
variable [(internalModule D v I).Normal] [IsElementaryAbelian 2 (internalModule D v I)]
private theorem original_no_rankOne_natural_model
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  obtain ⟨p,hp,hp2,hpd,hfix⟩ := c.original_scalar_obstruction af hF hn e
  let : Fact p.Prime := ⟨hp⟩
  have hpF : p ∣ Nat.card F - 1 := by simpa only [hF] using hpd
  obtain ⟨z,hzW,hzP,hzn⟩ := c.action_fixed_seed
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
private theorem Context.original_no_linearThree_natural_sum
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  obtain ⟨p,hp,hp2,hpd,hfix⟩ := c.original_scalar_obstruction af hF hn e
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
  obtain ⟨z,hzW,hzP,hzn⟩ := c.action_fixed_seed
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
private theorem Context.original_no_symplecticFour_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  exact original_no_rankOne_natural_model c af hF hn e σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
      (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D
      v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom)
    E rfl j hj hcoord (hs _ hB)

/-- The short and long G₂ local markings have the same contradiction on the
literal natural module, for every nonbinary field degree. -/
private theorem Context.original_no_g2_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  exact original_no_rankOne_natural_model c af hF hn e σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
      (internalModule D v I)) (Subgroup.subgroupOf L (pointJoin T v I))) (Subgroup.map (actionMk (internalModule D
      v I)) (Subgroup.subgroupOf I (pointJoin T v I))))).map E.toMonoidHom)
    E rfl j hj hcoord (hs _ hB)

/-- The concrete natural SL₃ action excludes both marked local subgroups.
A central kernel is allowed: only the original nonfixed seed must survive. -/
private theorem Context.original_no_linearThree_natural
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  apply original_no_rankOne_natural_model c af hF hn e σ (((Subgroup.subgroupOf (Subgroup.map (actionMk
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
private theorem Context.original_no_linearThree_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  have hm := c.fully_moved
  apply c.original_no_linearThree_natural af hF hn e E.groupEquiv hB
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
private theorem Context.original_no_symplecticFour_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  have hm := c.fully_moved
  apply c.original_no_symplecticFour_natural af hF hn e E.groupEquiv hB
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
private theorem Context.original_no_g2_source_section
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
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
  have hm := c.fully_moved
  apply c.original_no_g2_natural af hF hn e E.groupEquiv hB
    (E.linearEquiv.toLinearMap.comp (s.fullProjection hm))
  · intro z hz
    apply (s.fullProjection_eq_zero_iff hm z).mp
    exact E.linearEquiv.injective (hz.trans E.linearEquiv.map_zero.symm)
  · intro x z
    change E.linearEquiv (s.fullProjection hm (action (internalModule D v I) (x : ActionQuotient (internalModule D
        v I)) z)) = _
    rw [s.fullProjection_intertwines]
    exact E.intertwines x (s.fullProjection hm z)

/-- The SL₃ natural central section is excluded with its local placement proved. -/
private theorem Context.original_no_linearThree_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.special_linear_three_local_placement
    hF hn S _ hlocal hp
  apply c.original_no_linearThree_source_section af hF hn e s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg

/-- The Sp₄ natural central section is excluded with its local placement proved. -/
private theorem Context.original_no_symplecticFour_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hn S _ hlocal hp
  apply c.original_no_symplecticFour_source_section af hF hn e s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg

/-- The G₂ natural central section is excluded with its local placement proved. -/
private theorem Context.original_no_g2_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    omega
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hlarge S _ hlocal hp
  apply c.original_no_g2_source_section af hF hn e s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg


/-- The repeated natural row has the same placement obstruction, for any multiplicity. -/
private theorem Context.original_no_repeatedThree_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n r : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s : MovedSection (action (internalModule D v I))
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))))
    (E : ActionEquiv (s.space.toRepresentation.comp
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subtype)
      (repeated (Representation.restrictScalars (k := ZMod 2)
        (specialLinearNatural (k := F) 3)) r)) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.special_linear_three_local_placement
    hF hn S _ hlocal hp
  let E' := conjugateActionEquiv E g
  have hm := c.fully_moved
  let j : Additive (internalModule D v I) →ₗ[ZMod 2] s.space.toSubmodule :=
    (LinearMap.id : Additive (internalModule D v I) →ₗ[ZMod 2]
      Additive (internalModule D v I)).codRestrict s.space.toSubmodule
      (fun _ => by rw [s.space_eq,hm]; trivial)
  apply c.original_no_linearThree_natural_sum af hF hn e E'.groupEquiv
    (by simpa only [E',conjugateActionEquiv,show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl,map_map] using hg)
    ((E'.linearEquiv.toLinearMap.comp j).prod
      (0 : Additive (internalModule D v I) →ₗ[ZMod 2] (Empty → Fin 3 → F)))
  · intro z hz
    have he : E'.linearEquiv (j z) = 0 := congrArg Prod.fst hz
    have hz' : z = 0 := congrArg Subtype.val
      (E'.linearEquiv.injective (he.trans E'.linearEquiv.map_zero.symm))
    exact hz' ▸ (fixedSpace _ _).zero_mem
  · intro x z
    apply Prod.ext
    · exact E'.intertwines x (j z)
    · funext i
      exact Empty.elim i

end
/-- The four rank-two source actions are excluded on the actual restricted FF section,
using the original surviving seed and without a full moved-span premise. -/
theorem Context.no_original_rankTwo_action (c : Context D t v I) (a : ActionFacts c)
    :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      ¬ RankTwoAction s := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let K := I.subgroupOf H
  let q := actionMk U
  let A := K.map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  dsimp only
  intro N hAN s hs
  let r := MovedSection.ofNormal (action U) A
  cases hs with
  | linearThree F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_linear_three a F.card_eq hn E'.groupEquiv
    exact c.original_no_linearThree_source_section_of_local a F.card_eq hn e r E'
  | doubleThree F hn E =>
    let E' := composeAction (liftMovedAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_linear_three a F.card_eq hn E'.groupEquiv
    exact c.original_no_repeatedThree_source_section_of_local a F.card_eq hn e r E'
  | symplectic F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_symplectic_four a F.card_eq hn E'.groupEquiv
    exact c.original_no_symplecticFour_source_section_of_local a F.card_eq hn e r E'
  | g2 F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      omega
    obtain ⟨e⟩ := c.rank_one_quotient_of_g2 a hF E'.groupEquiv
    exact c.original_no_g2_source_section_of_local a F.card_eq hn e r E'

/-- The actual source conclusion retains only A₇ and binary-linear actions after the torus argument. -/
theorem Context.original_binary_or_seven_action (c : Context D t v I) (a : ActionFacts c)
    :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      BinaryOrSevenAction h.sectionData := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let K := I.subgroupOf H
  let q := actionMk U
  let A := K.map q
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  let B := ((L.subgroupOf H).map q).subgroupOf A
  obtain ⟨hA,hAN,_,_,_,⟨h⟩⟩ := a.classification
  let e : A ≃* C := (subgroupOfEquivOfLe hAN).symm
  let : IsQuasisimple A := hA
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact Group.isSolvable_of_comm (fun x y => by
      have hx : x = 1 := Subtype.ext (mem_bot.mp x.property)
      rw [hx,one_mul,mul_one])
  obtain ⟨hp,R,_,hl⟩ := a.small_local
  let S := R.mapSurjective (q.subgroupMap_surjective K)
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (G := A) (G' := C) (B := B) (S := (S : Subgroup A)) hl e.toMonoidHom
  have hp' : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    exact hp.ne (map_injective e.injective (he.trans (map_top_of_surjective _ e.surjective).symm))
  refine ⟨h,?_⟩
  exact (containing_action_of_source_case _ C h.sectionData h.clause_one
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) _ hl' hp').resolve_left
      (c.no_original_rankTwo_action a N hAN h.sectionData)
/-- The original prepared action has an A₇ actor or an original binary-three quotient. -/
theorem Context.original_seven_actor_or_binaryThree (c : Context D t v I)
    (a : ActionFacts c) :
    letI := c.reduced.normal
    Nonempty (((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7)) ∨ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨h,hs⟩ := c.original_binary_or_seven_action a
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  let e : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe a.classification.2.1).symm
  rcases hs.actor with hseven | ⟨d,hd,hlinear⟩
  · exact Or.inl ⟨e.trans hseven.some⟩
  · exact Or.inr (c.binary_three_quotient_of_binary_containing a hd (e.trans hlinear.some))


/-- The literal prepared action recognizes the original binary-three quotient,
without a moved-cover marking or full moved-span premise. -/
theorem Context.original_binary_three_quotient (c : Context D t v I)
    (a : ActionFacts c) : Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  rcases c.original_seven_actor_or_binaryThree a with hs | hb
  · exact c.binary_three_quotient_of_seven_actor a hs.some
  · exact hb

/-- Cubic component order alone supplies preparation and the same original quotient. -/
theorem Context.original_binary_three_quotient_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :=
  c.original_binary_three_quotient (c.actionFacts_of_three hd)

/-- The full original context leaves only the binary-three and Suzuki
quotients. This asserts actual quotient isomorphisms, not module coordinates. -/
theorem Context.original_component_alternatives (c : Context D t v I) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) ∨
      ∃ m : ℕ, 0 < m ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  by_cases hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)
  · exact Or.inl (c.original_binary_three_quotient_of_three hd)
  right
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  have hlinear {q : ℕ} (h : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 q) : False := by
    obtain ⟨F,_,_,_,⟨e⟩⟩ := h
    apply hd
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)
  cases Selection.ModuleChoice.component_quotient_model D hn with
  | linear_even _ _ h => exact (hlinear h).elim
  | linear_prime _ _ _ h => exact (hlinear h).elim
  | janko h =>
    apply False.elim
    apply hd
    rw [Nat.card_congr h.some.toEquiv,Janko1.card_model]
    norm_num
  | suzuki m hm h => exact ⟨m,by omega,h⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
