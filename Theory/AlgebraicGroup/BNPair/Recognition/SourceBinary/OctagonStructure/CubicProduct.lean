module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The internal perpendicular product and its exact Cartan kernels

A regular binary linear rank-one group is centerless, including over F₂.
Thus a commuting perpendicular conjugate gives an internal direct product.
An element of its intersection with the full Cartan has both factors in
that Cartan: normalization of the two opposite roots detects each factor.
The aligned rank-one pinning consequently gives literal unit-group product
coordinates on this intersection, of order (q − 1)².

The first panel kernel on this Cartan product is exactly the other Cartan
factor. Its intersection with the perpendicular conjugate panel kernel is
trivial. All products and kernels lie in the same marked quotient.

Source: Fong--Seitz I (6G), printed p.49, the paragraph beginning
“In addition to the commutator relations”. The original-factor and Chapter
12 applications supply commutation from the cubic-radical argument.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hK : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F))

include hK μ in
private theorem linear_rankOne_center : center (rankOne Q split i) = ⊥ := by
  let e := (rankOnePanelEquiv Q split i hK μ).trans μ
  apply eq_bot_iff.mpr
  intro z hz
  have hh := MulEquivClass.apply_mem_center e hz
  change e z ∈ center PSL(2,F) at hh
  rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot, mem_bot] at hh
  exact e.injective (hh.trans e.map_one.symm)

private theorem commuting_disjoint {Y : Type*} [Group Y] (A B : Subgroup Y)
    (hc : ⁅A,B⁆ = ⊥) (hz : center A = ⊥) : Disjoint A B := by
  apply disjoint_def.mpr
  intro x hxA hxB
  have hx : (⟨x,hxA⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc a.property x hxB).symm
  rw [hz] at hx
  exact congrArg Subtype.val hx

include hK μ in
/-- Centerfreeness makes the commuting product internal, including over F₂. -/
theorem linear_commuting_product (B : Subgroup (X ⧸ Q.D))
    (hc : ⁅rankOne Q split i,B⁆ = ⊥) :
    ∃ e : rankOne Q split i × B ≃* ↥(rankOne Q split i ⊔ B),
      ∀ a b, (e (a,b) : X ⧸ Q.D) = (a : X ⧸ Q.D)*(b : X ⧸ Q.D) :=
  exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (commuting_disjoint _ _ hc (linear_rankOne_center Q split i hK μ))
    (commutator_eq_bot_iff_le_centralizer.mp hc)

include hK μ in
private theorem linear_mem_cartan_of_root_normalizers {a : X ⧸ Q.D}
    (ha : a ∈ rankOne Q split i)
    (hU : a ∈ normalizer (simpleRoot Q split i : Set (X ⧸ Q.D)))
    (hO : a ∈ normalizer (rootAt Q split i (Q.simple i) : Set (X ⧸ Q.D))) :
    a ∈ Q.tits.B ⊓ Q.tits.N := by
  let s := UnitarySource.actorReflection Q split i
  have inB {x : X ⧸ Q.D} (hx : x ∈ rankOne Q split i)
      (hxU : x ∈ normalizer (simpleRoot Q split i : Set (X ⧸ Q.D))) :
      x ∈ Q.tits.B := by
    obtain ⟨g,hg⟩ := (alignedPinningHom_range Q split i hK μ s).symm ▸ hx
    rw [←hg] at hxU ⊢
    exact (alignedPinningHom_mem_borel_iff Q split i hK μ s g).mpr
      ((alignedPinningHom_borel_iff Q split i hK μ s g).mp hxU)
  apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split i
  refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split i ha,inB ha hU,?_⟩
  rw [borelConjugate_eq _ s.val s.class_eq]
  change (s.val : X ⧸ Q.D)*a*(s.val : X ⧸ Q.D)⁻¹ ∈ Q.tits.B
  apply inB
  · exact (rankOne Q split i).mul_mem
      ((rankOne Q split i).mul_mem s.mem_rankOne ha)
      ((rankOne Q split i).inv_mem s.mem_rankOne)
  · have hn := comap_normalizer_eq_of_surjective (simpleRoot Q split i)
      (f := (MulAut.conj (s.val : X ⧸ Q.D)).toMonoidHom)
      (MulAut.conj (s.val : X ⧸ Q.D)).surjective
    have he : (simpleRoot Q split i).comap (MulAut.conj (s.val : X ⧸ Q.D)).toMonoidHom =
        rootAt Q split i (Q.simple i) :=
      (rootAt_eq Q split i (Q.simple i) s.val s.class_eq).symm
    rw [he] at hn
    change a ∈ (normalizer (simpleRoot Q split i : Set (X ⧸ Q.D))).comap
      (MulAut.conj (s.val : X ⧸ Q.D)).toMonoidHom
    rwa [hn]

include hK μ in
private theorem linear_cartan_factor_of_product (B : Subgroup (X ⧸ Q.D))
    (hcomm : rankOne Q split i ≤ centralizer (B : Set (X ⧸ Q.D)))
    {a b : X ⧸ Q.D} (ha : a ∈ rankOne Q split i) (hb : b ∈ B)
    (hab : a*b ∈ Q.tits.B ⊓ Q.tits.N) : a ∈ Q.tits.B ⊓ Q.tits.N := by
  have hBR := le_centralizer_iff.mp hcomm
  have factor (U : Subgroup (X ⧸ Q.D)) (hUR : U ≤ rankOne Q split i)
      (hHU : Q.tits.B ⊓ Q.tits.N ≤ normalizer (U : Set (X ⧸ Q.D))) :
      a ∈ normalizer (U : Set (X ⧸ Q.D)) := by
    have hbU : b ∈ normalizer (U : Set (X ⧸ Q.D)) :=
      Subgroup.centralizer_le_normalizer _ (fun x hx => hBR hb x (hUR hx))
    simpa only [mul_inv_cancel_right] using
      (normalizer (U : Set (X ⧸ Q.D))).mul_mem (hHU hab)
        ((normalizer (U : Set (X ⧸ Q.D))).inv_mem hbU)
  exact linear_mem_cartan_of_root_normalizers Q split i hK μ ha
    (factor _ le_sup_left (torus_normalizes_simpleRoot Q split i))
    (factor _ le_sup_right (rootAt_torus_normalizes Q split i (Q.simple i)))

include hK μ in
/-- The Cartan intersection splits inside the actual commuting rank-one product. -/
theorem perpendicular_cartan_intersection (B : Subgroup (X ⧸ Q.D))
    (hc : ⁅rankOne Q split i,B⁆ = ⊥) :
    (Q.tits.B ⊓ Q.tits.N) ⊓ (rankOne Q split i ⊔ B) =
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) ⊔
      ((Q.tits.B ⊓ Q.tits.N) ⊓ B) := by
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp hc
  apply le_antisymm ?_ (sup_le (inf_le_inf_left _ le_sup_left)
    (inf_le_inf_left _ le_sup_right))
  intro x hx
  have hx' : x ∈ (rankOne Q split i : Set (X ⧸ Q.D)) * (B : Set (X ⧸ Q.D)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
    exact hx.2
  obtain ⟨a,ha,b,hb,rfl⟩ := hx'
  have haH := linear_cartan_factor_of_product Q split i hK μ B hcomm ha hb hx.1
  have hbH : b ∈ Q.tits.B ⊓ Q.tits.N := by
    simpa only [inv_mul_cancel_left] using
      (Q.tits.B ⊓ Q.tits.N).mul_mem ((Q.tits.B ⊓ Q.tits.N).inv_mem haH) hx.1
  exact mul_mem_sup ⟨haH,ha⟩ ⟨hbH,hb⟩

private theorem commuting_sup_centralizer {Y : Type*} [Group Y] (A B : Subgroup Y)
    (hc : ⁅A,B⁆ = ⊥) (hz : center A = ⊥) :
    (A ⊔ B) ⊓ centralizer (A : Set Y) = B := by
  have hAB := commutator_eq_bot_iff_le_centralizer.mp hc
  have hBA := le_centralizer_iff.mp hAB
  apply le_antisymm ?_ (le_inf le_sup_right hBA)
  intro x hx
  have hx' : x ∈ (A : Set Y)*(B : Set Y) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _
      (hAB.trans (Subgroup.centralizer_le_normalizer _))]
    exact hx.1
  obtain ⟨a,ha,b,hb,rfl⟩ := hx'
  have haC : a ∈ centralizer (A : Set Y) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (A : Set Y)).mul_mem hx.2
        ((centralizer (A : Set Y)).inv_mem (hBA hb))
  have haZ : (⟨a,ha⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (haC y y.property)
  have ha1 : a = 1 := congrArg Subtype.val (show (⟨a,ha⟩ : A) = 1 from mem_bot.mp (hz ▸ haZ))
  change a*b ∈ B
  rw [ha1,one_mul]
  exact hb

include hK μ in
/-- On the perpendicular Cartan product, the first panel kernel is exactly
    the Cartan factor belonging to the other rank-one group. -/
theorem perpendicular_linear_cartan_kernel (w : Weyl Q)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)⁆ = ⊥) :
    ((Q.tits.B ⊓ Q.tits.N) ⊓ (rankOne Q split i ⊔
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D))) ⊓
        embeddedPanelKernel Q i =
    (Q.tits.B ⊓ Q.tits.N) ⊓
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D) := by
  have hk := cartan_centralizer_rankOneRootGroup Q split i
  change (Q.tits.B ⊓ Q.tits.N) ⊓ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) =
    (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i at hk
  rw [inf_right_comm,←hk,inf_right_comm,inf_assoc,
    commuting_sup_centralizer _ _ hc (linear_rankOne_center Q split i hK μ)]

include hK μ in
/-- The two perpendicular panel kernels have trivial common intersection
    inside the constructed Cartan product. -/
theorem perpendicular_linear_cartan_joint_kernel (w : Weyl Q)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)⁆ = ⊥) :
    (((Q.tits.B ⊓ Q.tits.N) ⊓ (rankOne Q split i ⊔
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D))) ⊓
        embeddedPanelKernel Q i) ⊓
      rightConjugate (embeddedPanelKernel Q i) (representative w : X ⧸ Q.D) = ⊥ := by
  rw [perpendicular_linear_cartan_kernel Q split i hK μ w hc]
  apply eq_bot_iff.mpr
  intro x hx
  let n := representative w
  let y := (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹
  have hyR : y ∈ rankOne Q split i := hx.1.2
  have hyH : y ∈ Q.tits.B ⊓ Q.tits.N :=
    (mem_normalizer_iff.mp (torus_normalizes n) x).mp hx.1.1
  have hyK : y ∈ embeddedPanelKernel Q i := hx.2
  have hyC : y ∈ centralizer (rankOne Q split i : Set (X ⧸ Q.D)) :=
    ((cartan_centralizer_rankOneRootGroup Q split i).symm ▸
      (show y ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i from ⟨hyH,hyK⟩)).2
  have hyZ : (⟨y,hyR⟩ : rankOne Q split i) ∈ center (rankOne Q split i) := by
    apply mem_center_iff.mpr
    intro r
    exact Subtype.ext (hyC r r.property)
  have hy1 : y = 1 := congrArg Subtype.val
    (show (⟨y,hyR⟩ : rankOne Q split i) = 1 from
      mem_bot.mp (linear_rankOne_center Q split i hK μ ▸ hyZ))
  apply mem_bot.mpr
  apply (MulAut.conj (n : X ⧸ Q.D)).injective
  exact hy1.trans (map_one _).symm

include hK μ in
/-- Multiplication supplies the exact two Cartan factors of the perpendicular product. -/
theorem perpendicular_linear_cartan_product (w : Weyl Q)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)⁆ = ⊥) :
    ∃ e : Fˣ × Fˣ ≃*
      ↥((Q.tits.B ⊓ Q.tits.N) ⊓ (rankOne Q split i ⊔
        rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D))),
      ∀ a b, (e (a,b) : X ⧸ Q.D) =
        alignedTorus Q split i hK μ (UnitarySource.actorReflection Q split i) a *
        ((representative w : X ⧸ Q.D)⁻¹ *
          alignedTorus Q split i hK μ (UnitarySource.actorReflection Q split i) b *
          (representative w : X ⧸ Q.D)) := by
  let R := rankOne Q split i
  let R' := rightConjugate R (representative w : X ⧸ Q.D)
  let H := Q.tits.B ⊓ Q.tits.N
  let T := H ⊓ R
  let T' := H ⊓ R'
  have heq : rightConjugate T (representative w : X ⧸ Q.D) = T' := by
    rw [rightConjugate_inf,torus_conjugate]
  have hd : Disjoint T T' :=
    (commuting_disjoint R R' hc (linear_rankOne_center Q split i hK μ)).mono
      inf_le_right inf_le_right
  have hcc : T ≤ centralizer (T' : Set (X ⧸ Q.D)) :=
    inf_le_right.trans ((commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (centralizer_le (show (T' : Set (X ⧸ Q.D)) ⊆ R' from fun _ h => h.2)))
  obtain ⟨m,hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting T T' hd hcc
  let t := alignedCartanEquiv Q split i hK μ (UnitarySource.actorReflection Q split i)
  let t' : Fˣ ≃* T' := (t.trans (RootAction.conjugateEquiv T
    (representative w : X ⧸ Q.D)).symm).trans (MulEquiv.subgroupCongr heq)
  let e := (t.prodCongr t').trans (m.trans (MulEquiv.subgroupCongr
    (perpendicular_cartan_intersection Q split i hK μ R' hc).symm))
  refine ⟨e,?_⟩
  intro a b
  exact hm (t a) (t' b)

include hK μ in
theorem perpendicular_linear_cartan_card (w : Weyl Q)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)⁆ = ⊥) :
    Nat.card ↥((Q.tits.B ⊓ Q.tits.N) ⊓ (rankOne Q split i ⊔
        rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D))) =
      (Nat.card F - 1)^2 := by
  obtain ⟨e,_⟩ := perpendicular_linear_cartan_product Q split i hK μ w hc
  rw [←Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_units, pow_two]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
