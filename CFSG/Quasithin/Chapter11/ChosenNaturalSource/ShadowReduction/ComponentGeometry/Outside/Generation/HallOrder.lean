module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.LinearThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.SymplecticFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSeed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Containment

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.G2Action.Model

/-!
# The Hall-order step of the outside generation argument

In the equality row K=L₁, the E.2.2 Hall actor lies in the literal
centralizer of K/O₂(K). For the original SL₃, Sp₄ and G₂ flags, a vector
stabilizer in the model is perfect. Its image therefore lies in the
marked line residual. Lifting leaves only O₂(L), and the kernel theorem
for a two-group supplement proves that the odd actor intersects L
trivially. Source 11.0.4 now excludes every prime dividing q−1.

The point centralizer inside M preserves V by the proved TI property.
Thus the linear cubic case uses the proved seed-preserving version of
11.0.4, without unrestricted cubic containment. The final consumers
construct the actual full Hall actor from E.2.2 and supply its faithful
V-action, quotient-kernel placement, seed normalization and coprimality.

This proves the Hall-order step for all three equality rows; it does not
assert 11.4.4. The terminal natural-action calculation, the
strict-component reduction and the equal-carrier generation bound remain
with qt-d-1222-shadow-component-witness. The exact OddKernelNormalizer
premise is used only for faithfulness and remains with its existing
producer qt-d-1222-natural-odd-kernel-normalizer. Earlier geometry,
11.3.2, the linear fixed-space input and Kz=K retain the producers
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison. Final earlier-source discharge
belongs to qt-d-1222-shadow-components.

The local vector-stabilizer calculations use the same elementary proofs
as Closure.Nonabelian.PointModels.LinearThree and SymplecticFour, whose
perfect-stabilizer lemmas are private. Native symplectic calculations use
the attributed ATLAS port; see LICENSES/ATLAS.txt.
Source: Aschbacher--Smith, 11.0.3(4), 11.0.4 and 11.4.4,
printed pp.760 and778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- The point centralizer inside M preserves the original seed, by its TI property. -/
theorem point_intersection_normalizes_seed (hz : E.z ∈ V) (hz1 : E.z ≠ 1) :
    Mz E ≤ normalizer (V : Set G) := by
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (LocalGeometry.Preliminary.seed_ti D E.input b hb.1).resolve_left
  intro he
  apply hz1
  apply mem_bot.mp
  rw [← he]
  refine ⟨hz,E.z,hz,?_⟩
  have hc := mem_centralizer_singleton_iff.mp hb.2
  change b * E.z * b⁻¹ = E.z
  rw [hc,mul_inv_cancel_right]

private def modelPointFixer {F : BinaryField} (c : LocalGeometry.Coordinates D F)
    (w : c.Space) : Subgroup c.ModelGroup :=
    { carrier := {g | c.modelAction g w = w}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; change c.modelAction (a*b) w = w; rw [map_mul,Module.End.mul_apply,hb,ha]
      inv_mem' := by
        intro a ha
        change c.modelAction a⁻¹ w = w
        have hh := congrArg (c.modelAction a⁻¹) ha
        simpa only [← Module.End.mul_apply, ← map_mul,inv_mul_cancel,map_one,
          Module.End.one_apply] using hh.symm }

private theorem point_fixer_le_local_join_core
    {F : BinaryField} (c : LocalGeometry.Coordinates D F)
    (f : LocalGeometry.InvariantFlag c) (z : V)
    (hz : (c.projection z).toAdd ∈ f.space 0)
    (hperfect : Group.IsPerfect (modelPointFixer c (c.projection z).toAdd))
    (hz0 : (c.projection z).toAdd ≠ 0) :
    L ⊓ centralizer ({(z : G)} : Set G) ≤ f.Li 0 ⊔ L.pCoreIn 2 := by
  let w := (c.projection z).toAdd
  let P := modelPointFixer c w
  let : Group.IsPerfect P := hperfect
  have hP : P ≤ ((f.Li 0).subgroupOf L).map c.quotientMap := by
    change P ≤ ((LocalGeometry.localResidual L (c.preimage (f.space 0))).subgroupOf L).map c.quotientMap
    rw [Closure.Nonabelian.PointModels.model_residual_image]
    apply le_map_solvableResidual_of_isPerfect
    intro g hg x
    have hfix (v : c.Space) (hv : v ∈ f.space 0) : c.modelAction g v = v := by
      rw [eq_span_singleton_of_mem_of_finrank_eq_one (f.dimension 0) hz hz0] at hv
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul]
      exact congrArg (a • ·) hg
    change c.modelAction g x ∈ f.space 0 ↔ x ∈ f.space 0
    constructor
    · intro hx
      have he := hfix _ hx
      have hinj : Function.Injective (c.modelAction g) := by
        intro a b he
        have hh := congrArg (c.modelAction g⁻¹) he
        simpa only [← Module.End.mul_apply, ← map_mul,inv_mul_cancel,map_one,
          Module.End.one_apply] using hh
      exact (hinj he) ▸ hx
    · intro hx
      rw [hfix x hx]
      exact hx
  rintro l ⟨hl,hc⟩
  have he : V.normalizerMonoidHom (inclusion D.normalizes ⟨l,hl⟩) z = z := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
  have hm : c.quotientMap ⟨l,hl⟩ ∈ P := by
    change c.modelAction _ _ = _
    rw [← c.projection_component_conjugation,he]
  obtain ⟨u,hu,huq⟩ := hP hm
  have hk : (⟨l,hl⟩ : L) * u⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply c.groupEquiv.injective
    change c.quotientMap ((⟨l,hl⟩ : L) * u⁻¹) = c.groupEquiv 1
    rw [map_mul,map_inv,huq,mul_inv_cancel,map_one]
  have hh := (f.Li 0 ⊔ L.pCoreIn 2).mul_mem
    (mem_sup_right (mem_map_of_mem L.subtype hk)) (mem_sup_left hu)
  change l * (u : G)⁻¹ * (u : G) ∈ _ at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

omit [Finite G] in
/-- Inside a two-group supplement of a centerless core quotient, its literal
centralizer is a two-group. -/
theorem coreCentralizer_inf_join_isTwoGroup (A U : Subgroup G)
    (hU : IsPGroup 2 U) (hn : U ≤ normalizer (A : Set G))
    (hc : center (A ⧸ pCore 2 A) = ⊥) :
    IsPGroup 2 ((A ⊔ U) ⊓ Closure.coreQuotientCentralizer A : Subgroup G) := by
  let J := A ⊔ U
  have hle : J ⊓ Closure.coreQuotientCentralizer A ≤
      (pCoreJoinAction 2 hn).ker.map J.subtype := by
    rintro x ⟨hx,a,ha,hax⟩
    let x' : J := ⟨x,hx⟩
    refine ⟨x',?_,rfl⟩
    have he : inclusion (sup_le A.le_normalizer hn) x' = a := Subtype.ext hax.symm
    change Closure.coreQuotientAction A (inclusion (sup_le A.le_normalizer hn) x') = 1
    rw [he]
    exact ha
  exact ((pCoreJoinAction_kernel_isPGroup 2 hn hU hc).map J.subtype).to_le hle

private theorem odd_inf_seed_eq_bot
    (hTA : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G))
    (hc : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hpoint : L ⊓ Gz E ≤ E.L₁ ⊔ (T : Subgroup G))
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBz : B ≤ Gz E)
    (hBc : B ≤ Closure.coreQuotientCentralizer E.L₁) : B ⊓ L = ⊥ := by
  have hp := coreCentralizer_inf_join_isTwoGroup E.L₁ (T : Subgroup G) T.isPGroup' hTA hc
  have hle : B ⊓ L ≤ (E.L₁ ⊔ (T : Subgroup G)) ⊓ Closure.coreQuotientCentralizer E.L₁ := by
    intro b hb
    exact ⟨hpoint ⟨hb.2,hBz hb.1⟩,hBc hb.1⟩
  have hpB : IsPGroup 2 (B ⊓ L : Subgroup G) := hp.to_le hle
  have hodd : Odd (Nat.card (B ⊓ L : Subgroup G)) := ho.of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨k,hk⟩ := hpB.exists_card_eq
  apply Subgroup.card_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k) dvd_rfl hk.dvd


include D in
omit [Finite G] in
private theorem componentCore_le_sylow : L.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  apply hQ.trans
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

private theorem coprime_of_prime_elements_in_component
    (B : Subgroup G) (q : ℕ) (hBL : B ⊓ L = ⊥)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → ∀ b ∈ B, orderOf b = p → b ∈ L) :
    Nat.Coprime (Nat.card B) q := by
  apply Nat.coprime_of_dvd
  intro p hp hdB hdq
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) p hdB
  have hbo : orderOf (b : G) = p := (orderOf_injective B.subtype B.subtype_injective b).trans hb
  have hbl := hprime p hp hdq b b.property hbo
  have hb1 : (b : G) = 1 := mem_bot.mp (hBL ▸ (show (b : G) ∈ B ⊓ L from ⟨b.property,hbl⟩))
  have hh : p = 1 := hbo.symm.trans (hb1 ▸ orderOf_one)
  exact hp.ne_one hh

variable (S : D.NonbinaryNaturalInput)

/-- All split-torus primes are excluded from an odd point actor with trivial
intersection with L in the linear row. Cubics use the proved seed-preserving
version of 11.0.4, so unrestricted cubic containment is unnecessary. -/
theorem sl3_odd_point_coprime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBM : B ≤ E.M)
    (hBz : B ≤ Gz E) (hz : E.z ∈ V) (hz1 : E.z ≠ 1)
    (hBL : B ⊓ L = ⊥) : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  have hBV := (le_inf hBM hBz).trans (point_intersection_normalizes_seed E hz hz1)
  apply coprime_of_prime_elements_in_component B _ hBL
  intro p hp hd b hb hbo
  have hp2 : p ≠ 2 := by
    intro he
    have hh := B.orderOf_dvd_natCard hb
    rw [hbo,he] at hh
    exact ho.not_two_dvd_nat hh
  by_cases hp3 : p = 3
  · exact LocalGeometry.Preliminary.sl3_orderThree_mem_of_normalizes_seed D S m
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mp (hp3 ▸ hd))
      (hBM hb) (hBV hb) (hbo.trans hp3)
  · exact LocalGeometry.Preliminary.orderPrime_mem_component D S hp
      (Or.inr ⟨⟨m⟩,by have hh := hp.two_le; omega,hd⟩) (hBM hb) hbo

/-- The symplectic split-torus primes use the literal 11.0.4 residual. -/
theorem sp4_odd_point_coprime
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    (hBL : B ⊓ L = ⊥) : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  apply coprime_of_prime_elements_in_component B _ hBL
  intro p hp hd b hb hbo
  have hd2 : p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
    hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  exact LocalGeometry.Preliminary.orderPrime_mem_component D S hp
    (Or.inl ⟨Or.inl ⟨m⟩,hd2⟩) (hBM hb) hbo

namespace LocalModels
open Matrix Matrix.PSp4Three
variable {F : Type*} [Field F] [Finite F]
private theorem sl3_vector_perfect (hF : 4 ≤ Nat.card F)
    {u : Fin 3 → F} (hu : u ≠ 0) : Group.IsPerfect (MulAction.stabilizer SL(3,F) u) := by
  have he0 : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  obtain ⟨g, hg⟩ := SpecialLinearGroup.exists_mulVec_eq_three _ u he0 hu
  have he : MulAction.stabilizer SL(3,F) (![1,0,0] : Fin 3 → F) =
      PSL3.LinearThree.pointLocalSL F := by
    ext a
    rw [MulAction.mem_stabilizer_iff, PSL3.LinearThree.mem_pointLocalSL_iff]
    change a.val *ᵥ ![1,0,0] = ![1,0,0] ↔ _
    have hx (i : Fin 3) : (a.val *ᵥ (![1,0,0] : Fin 3 → F)) i = a.val i 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    constructor
    · intro h
      exact ⟨(hx 0).symm.trans (congrFun h 0),
        (hx 1).symm.trans (congrFun h 1), (hx 2).symm.trans (congrFun h 2)⟩
    · intro h
      ext i
      rw [hx]
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  have hp : Group.IsPerfect (MulAction.stabilizer SL(3,F) (![1,0,0] : Fin 3 → F)) := by
    rw [he]
    exact PSL3.LinearThree.pointLocalSL_isPerfect F hF
  let := hp
  have hg' : u = g • (![1,0,0] : Fin 3 → F) := hg.symm
  let e := MulAction.stabilizerEquivStabilizer hg'
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

variable [CharP F 2]
private theorem sp4_vector_perfect {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {u : Vector 2 F} (hu : u ≠ 0) : Group.IsPerfect (MulAction.stabilizer (Sp 2 F) u) := by
  have he0 : (e 0 : Vector 2 F) ≠ 0 := by
    intro he
    have hh := congrFun he (Sum.inl 0)
    simp [Matrix.PSp4Three.e] at hh
  obtain ⟨g, hg⟩ := Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive he0 hu
  have he : MulAction.stabilizer (Sp 2 F) (e 0 : Vector 2 F) =
      Theory.SpecificGroups.SymplecticFour.pointLocal := by
    ext a
    exact (Theory.SpecificGroups.SymplecticFour.mem_pointLocal_iff_fixed a).symm
  have hp : Group.IsPerfect (MulAction.stabilizer (Sp 2 F) (e 0 : Vector 2 F)) := by
    rw [he]
    exact Theory.SpecificGroups.SymplecticFour.pointLocal_perfect hF hn
  let := hp
  exact Group.IsPerfect.ofSurjective (f := (MulAction.stabilizerEquivStabilizer hg.symm).toMonoidHom)
    (MulAction.stabilizerEquivStabilizer hg.symm).surjective

end LocalModels

private theorem ofFlag_odd_inf_seed
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hmodel : ∀ w : c.Space, w ≠ 0 → Group.IsPerfect (modelPointFixer c w))
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBz : B ≤ Gz (ofFlag S f X z H))
    (hBc : B ≤ Closure.coreQuotientCentralizer (f.Li 0)) :
    B ⊓ L = ⊥ := by
  let E := ofFlag S f X z H
  let v : V := ⟨z,E.V₁_le h.point_mem⟩
  have hv0 : (c.projection v).toAdd ≠ 0 := by
    intro hz0
    have hv1 : v = 1 := Closure.Nonabelian.PointModels.projection_injective c hf
      (hz0.trans (map_one c.projection).symm)
    exact h.point_ne_one (congrArg Subtype.val hv1)
  have hpoint : L ⊓ Gz E ≤ E.L₁ ⊔ (T : Subgroup G) :=
    (point_fixer_le_local_join_core c f v ((c.mem_preimage _ v).mp h.point_mem)
      (hmodel _ hv0) hv0).trans (sup_le_sup_left (componentCore_le_sylow (D := D)) _)
  exact odd_inf_seed_eq_bot E (f.sylow_normalizes_Li 0)
    (ofFlag_first_quotient_center S f) hpoint B ho hBz hBc

private theorem ofFlag_odd_inf_component
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hmodel : ∀ w : c.Space, w ≠ 0 → Group.IsPerfect (modelPointFixer c w))
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBY : B ≤ Yz (ofFlag S f X z H)) :
    B ⊓ L = ⊥ := by
  apply ofFlag_odd_inf_seed S f X z H h hf hmodel B ho (hBY.trans inf_le_left)
  simpa only [hK,ofFlag_firstResidual] using hBY.trans inf_le_right

/-- The complete Hall-order calculation in the equality row of the original
linear flag, including the cubic prime and the full SL₃ center. -/
theorem ofFlag_sl3_equal_odd_kernel_coprime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBM : B ≤ normalizer (L : Set G))
    (hBY : B ≤ Yz (ofFlag S f X z H)) :
    Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  apply sl3_odd_point_coprime (ofFlag S f X z H) S m B ho hBM (hBY.trans inf_le_left)
    ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one
  apply ofFlag_odd_inf_component S f X z H h hK
    (LocalGeometry.Preliminary.sl3_centralizer_eq_bot D S m) _ B ho hBY
  intro w hw
  change Group.IsPerfect (MulAction.stabilizer SL(3,S.field.Carrier) (show Fin 3 → S.field.Carrier from w))
  exact LocalModels.sl3_vector_perfect (S.field.card_eq ▸
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) S.nonbinary)) hw

/-- The same literal calculation for a symplectic flag. Fixed-space vanishing
is the earlier 11.4.1(1) premise, not a condition on the Hall actor. -/
theorem ofFlag_sp4_equal_odd_kernel_coprime
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : LocalGeometry.InvariantFlag (.sp4 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBM : B ≤ normalizer (L : Set G))
    (hBY : B ≤ Yz (ofFlag S f X z H)) :
    Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  apply sp4_odd_point_coprime S m B hBM
  apply ofFlag_odd_inf_component S f X z H h hK hf _ B ho hBY
  intro w hw
  change Group.IsPerfect (MulAction.stabilizer (Matrix.symplecticGroup (Fin 2) S.field.Carrier)
    (show Matrix.PSp4Three.Vector 2 S.field.Carrier from w))
  exact LocalModels.sp4_vector_perfect S.field.card_eq S.nonbinary hw

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise

/-- The full constructed Hall actor on the original linear flag is faithful,
centralizes the component quotient, and has order coprime to q−1.
The exact OddKernelNormalizer premise is used only for faithfulness. -/
theorem ofFlag_sl3_equal_faithful_hall_order
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) (hn : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (n : ℕ),
      IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP =
          (normalizer (L : Set G)).subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) ∧
        d.witness.abelianGroup.map H.subtype ≤ Yz (ofFlag S f X z H) ∧
        d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ ∧
        d.witness.abelianGroup.map H.subtype ≤ normalizer (V : Set G) ∧
        Nat.Coprime (Nat.card (d.witness.abelianGroup.map H.subtype))
          (2 ^ S.field.degree - 1) := by
  obtain ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith⟩ :=
    equal_faithful_hall_in_point_kernel (ofFlag S f X z H) h he hK hcontrol hH hHz hn
  have hBM : d.witness.abelianGroup.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have ho : Odd (Nat.card (d.witness.abelianGroup.map H.subtype)) :=
    d.witness.odd.of_dvd_nat (card_map_dvd _ _)
  refine ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith,?_,
    ofFlag_sl3_equal_odd_kernel_coprime S m f X z H h hK _ ho hBM hY⟩
  exact (le_inf hBM (hY.trans inf_le_left)).trans
    (point_intersection_normalizes_seed (ofFlag S f X z H)
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one)

/-- The actual symplectic Hall consumer, retaining only the earlier
11.3.2 and linear fixed-space inputs, and the separately owned odd-kernel normalizer input. -/
theorem ofFlag_sp4_equal_faithful_hall_order
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : LocalGeometry.InvariantFlag (.sp4 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) (hn : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (n : ℕ),
      IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP =
          (normalizer (L : Set G)).subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) ∧
        d.witness.abelianGroup.map H.subtype ≤ Yz (ofFlag S f X z H) ∧
        d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ ∧
        d.witness.abelianGroup.map H.subtype ≤ normalizer (V : Set G) ∧
        Nat.Coprime (Nat.card (d.witness.abelianGroup.map H.subtype))
          (2 ^ S.field.degree - 1) := by
  have hf := (fixed_and_transitive D S (ofFlag S f X z H).point hlinear h1132).1
  obtain ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith⟩ :=
    equal_faithful_hall_in_point_kernel (ofFlag S f X z H) h he hK hcontrol hH hHz hn
  have hBM : d.witness.abelianGroup.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have ho : Odd (Nat.card (d.witness.abelianGroup.map H.subtype)) :=
    d.witness.odd.of_dvd_nat (card_map_dvd _ _)
  refine ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith,?_,
    ofFlag_sp4_equal_odd_kernel_coprime S m f X z H h hK hf _ ho hBM hY⟩
  exact (le_inf hBM (hY.trans inf_le_left)).trans
    (point_intersection_normalizes_seed (ofFlag S f X z H)
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one)



/-- The split-torus primes in the original exceptional normalizer lie in L. -/
theorem g2_odd_point_coprime
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    (hBL : B ⊓ L = ⊥) : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  apply coprime_of_prime_elements_in_component B _ hBL
  intro p hp hd b hb hbo
  have hd2 : p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
    hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  exact LocalGeometry.Preliminary.orderPrime_mem_component D S hp
    (Or.inl ⟨Or.inr ⟨m⟩,hd2⟩) (hBM hb) hbo

/-- The original exceptional flag gives the same Hall-order coprimality,
using its literal octonion quotient and retaining the central-cover kernel. -/
theorem ofFlag_g2_equal_odd_kernel_coprime
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (.g2 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (B : Subgroup G) (ho : Odd (Nat.card B)) (hBM : B ≤ normalizer (L : Set G))
    (hBY : B ≤ Yz (ofFlag S f X z H)) :
    Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  apply g2_odd_point_coprime S m B hBM
  apply ofFlag_odd_inf_component S f X z H h hK hf _ B ho hBY
  intro w hw
  exact G2Action.pointFixer_perfect (S.field.card_eq ▸
    (show (2:ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)) hw

/-- The full exceptional Hall actor is constructed from E.2.2. Its literal
quotient-kernel placement, seed normalization and order coprimality are proved;
the separately owned odd-kernel input is used only for faithfulness. -/
theorem ofFlag_g2_equal_faithful_hall_order
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (.g2 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) (hn : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (n : ℕ),
      IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP =
          (normalizer (L : Set G)).subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) ∧
        d.witness.abelianGroup.map H.subtype ≤ Yz (ofFlag S f X z H) ∧
        d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ ∧
        d.witness.abelianGroup.map H.subtype ≤ normalizer (V : Set G) ∧
        Nat.Coprime (Nat.card (d.witness.abelianGroup.map H.subtype))
          (2 ^ S.field.degree - 1) := by
  have hf := (fixed_and_transitive D S (ofFlag S f X z H).point hlinear h1132).1
  obtain ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith⟩ :=
    equal_faithful_hall_in_point_kernel (ofFlag S f X z H) h he hK hcontrol hH hHz hn
  have hBM : d.witness.abelianGroup.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have ho : Odd (Nat.card (d.witness.abelianGroup.map H.subtype)) :=
    d.witness.odd.of_dvd_nat (card_map_dvd _ _)
  refine ⟨hP,n,hg,hb,d,hm,hperm,hY,hfaith,?_,
    ofFlag_g2_equal_odd_kernel_coprime S m f X z H h hK hf _ ho hBM hY⟩
  exact (le_inf hBM (hY.trans inf_le_left)).trans
    (point_intersection_normalizes_seed (ofFlag S f X z H)
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one)

/-- The Hall-order calculation only needs the literal first-residual action
kernel. It therefore also applies when the containing component is strict. -/
theorem ofFlag_odd_point_section_coprime
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBM : B ≤ normalizer (L : Set G)) (hBz : B ≤ Gz (ofFlag S f X z H))
    (hBc : B ≤ Closure.coreQuotientCentralizer (f.Li 0)) :
    Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1) := by
  have hBL : B ⊓ L = ⊥ := by
    apply ofFlag_odd_inf_seed S f X z H h hf _ B ho hBz hBc
    intro w hw
    cases c with
    | sl3 m =>
      exact LocalModels.sl3_vector_perfect (S.field.card_eq ▸
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) S.nonbinary)) hw
    | sp4 m => exact LocalModels.sp4_vector_perfect S.field.card_eq S.nonbinary hw
    | g2 m =>
      exact G2Action.pointFixer_perfect (S.field.card_eq ▸
        (show (2:ℕ)^1 < 2^S.field.degree from
          Nat.pow_lt_pow_right (by decide) S.nonbinary)) hw
  cases c with
  | sl3 m =>
    exact sl3_odd_point_coprime (ofFlag S f X z H) S m B ho hBM hBz
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one hBL
  | sp4 m => exact sp4_odd_point_coprime S m B hBM hBL
  | g2 m => exact g2_odd_point_coprime S m B hBM hBL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
