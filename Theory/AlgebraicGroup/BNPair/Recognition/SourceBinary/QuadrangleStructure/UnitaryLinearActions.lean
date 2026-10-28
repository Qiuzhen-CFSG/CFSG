module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreField
public import Theory.GroupTheory.PGroup.FrattiniActionImage
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Both irreducible linear sections in the unitary-five quadrangle

The full SL2(q squared) actor moves the nonzero derived layer of a unitary
root by its source reflection. Its action on the elementary radical-derived
layer is therefore nontrivial. The minimum binary SL2 degree and the
q-to-the-fourth upper bound force equality and irreducibility.

The radical has order q to the eighth, so its Frattini quotient also has
order q to the fourth. Burnside's Frattini automorphism-kernel theorem and
perfectness of SL2(q squared) show that its quotient action is nontrivial;
the same degree theorem proves irreducibility. Adding the full Cartan
preserves irreducibility, supplying the exact CoreField actor action.
The minimum actor is SL2(4), so the fixed field q = 2 is included.

All actions are conjugation on literal sections in the same marked quotient.
The CFSG adapter supplies the full linear actor and section order from the
original DGS data. The full SU3 actor, its own section action, and later
compatible Hermitian realizations are separate remaining obligations.

Source: Fong--Seitz I (4B), (6A)(c), pp.19--22,37;
Burnside's basis theorem for finite p-groups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open BenderSuzuki.External BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

open Representation Representation.BinaryOffender
open scoped MatrixGroups
private theorem linear_action_card_lower {F A R : Type*}
    [Field F] [Finite F] [CharP F 2] [Group A] [Group R] [Finite R]
    [IsElementaryAbelian 2 R]
    (μ : A ≃* SL(2,F)) (φ : A →* MulAut R)
    (hnt : ∃ a, φ a ≠ 1) {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) : Nat.card F ^ 2 ≤ Nat.card R := by
  let ρ := (elementaryRepresentation (p := 2) φ).comp μ.symm.toMonoidHom
  have hntρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hnt
    refine ⟨μ a,fun he => ha ?_⟩
    ext v
    have hv := congrArg (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul v)) he
    change Additive.ofMul (φ (μ.symm (μ a)) v) = Additive.ofMul v at hv
    change φ a v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hl := Representation.SL2.fixedCodim_top_lower ρ hntρ hn hF
  have hd := fixedCodim_add_finrank ρ ⊤
  have hc : Nat.card R = 2 ^ Module.finrank (ZMod 2) (Additive R) := by
    change Nat.card (Additive R) = _
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R))
  rw [hc,hF,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)


/-- The full linear actor forces its elementary derived layer to have the
minimum possible order, and to be irreducible. -/
theorem unitary_linear_derived_irreducible
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (μ : rankOne Q split i ≃* SL(2,K))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    frattini (simpleRemainder Q split i) = _root_.commutator (simpleRemainder Q split i) ∧
    ∃ he : IsElementaryAbelian 2
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)),
      letI := he
      Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2) (remainderDerivedAction Q split i hVi)).IsIrreducible := by
  let ξ := (localGroupEquivOfCenterless Q split i hVi μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let τ := GTwoSource.simpleRootFieldEquiv Q split i hVi ξ
  let : IsElementaryAbelian 2 (Multiplicative K) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      apply Multiplicative.toAdd.injective
      change (2 : ℕ) • a.toAdd = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _) }
  have hAi := IsElementaryAbelian.of_surjective (p := 2) τ.toMonoidHom τ.surjective
  have hcAi := (GTwoSource.simpleRoot_card Q split i hVi ξ).trans hK
  have hcomm := unitary_opposite_commutator Q split J hn hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  obtain ⟨hphi,_,he,hu⟩ := unitary_linear_layers Q split J hn hE hfixed hJ hm i j hij hVi hVj ν hAi hcAi hcomm
  let := he
  have hnt := remainderDerivedAction_nontrivial Q split hm i j hij hVi s
    (simpleRoot_unitary_derived J hn hE hfixed hJ Q split j hVj ν).2.2
  have hK' : Nat.card K = 2^(2*n) := by rw [hK,←pow_mul]; congr 1; omega
  have hl := linear_action_card_lower μ (remainderDerivedAction Q split i hVi) hnt (by omega : 1 < 2*n) hK'
  have hpow : Nat.card K ^ 2 = (2^n)^4 := by rw [hK]; ring
  have hc := le_antisymm hu (hpow ▸ hl)
  exact ⟨hphi,he,hc,minimal_linear_action_irreducible μ (remainderDerivedAction Q split i hVi)
    hnt (by omega : 1 < 2*n) hK' (hc.trans hpow.symm)⟩

private theorem frattini_action_nontrivial {A V : Type*}
    [Group A] [Group V] [Finite V] [Group.IsPerfect A]
    (hV : IsPGroup 2 V) (φ : A →* MulAut V) (hnt : ∃ a, φ a ≠ 1) :
    ∃ a, ((Subgroup.quotientAut (frattini V)).comp φ) a ≠ 1 := by
  by_contra! hh
  have hz : ((Subgroup.quotientAut (frattini V)).comp φ) = 1 := MonoidHom.ext hh
  have hp : IsPGroup 2 ((Subgroup.quotientAut (frattini V)).comp φ).range := by
    rw [hz,MonoidHom.range_one]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hpφ := MonoidHom.isPGroup_range_of_frattini_range hV φ hp
  let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  let : Group.IsNilpotent φ.range := hpφ.isNilpotent
  have hsub : Subsingleton φ.range := by
    by_contra hh'
    let : Nontrivial φ.range := not_subsingleton_iff_nontrivial.mp hh'
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  obtain ⟨a,ha⟩ := hnt
  exact ha (congrArg Subtype.val (hsub.elim (φ.rangeRestrict a) 1))

/-- The actual full root actor acts on the literal Frattini quotient. -/
@[expose] def remainderFrattiniAction (i : Fin 2)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i →* MulAut ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  (Subgroup.quotientAut (frattini (simpleRemainder Q split i))).comp (remainderRankOneAction Q split i hVi)

@[simp] theorem remainderFrattiniAction_mk (i : Fin 2)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (r : rankOne Q split i) (v : simpleRemainder Q split i) :
    remainderFrattiniAction Q split i hVi r (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v) =
      QuotientGroup.mk' (frattini (simpleRemainder Q split i)) (remainderRankOneAction Q split i hVi r v) :=
  Subgroup.quotientAut_apply_mk _ _ _

/-- Both linear sections in the U5 branch have order q to the fourth;
the Frattini quotient is irreducible under the full SL2 actor. -/
theorem unitary_linear_frattini_irreducible
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (μ : rankOne Q split i ≃* SL(2,K))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hcardV : Nat.card (simpleRemainder Q split i) = (2^n)^8) :
    Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)).IsIrreducible := by
  obtain ⟨hphi,he,hcardD,_⟩ := unitary_linear_derived_irreducible Q split J hn hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν
  have hcardPhi : Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 := by
    rw [hphi,←card_map_of_injective (simpleRemainder Q split i).subtype_injective,map_subtype_commutator]
    exact hcardD
  have hcardF : Nat.card ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) = (2^n)^4 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini (simpleRemainder Q split i))
    rw [hcardV,hcardPhi] at hc
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) n) 4)
    exact hc.symm.trans (by ring)
  have hntD := remainderDerivedAction_nontrivial Q split hm i j hij hVi s
    (simpleRoot_unitary_derived J hn hE hfixed hJ Q split j hVj ν).2.2
  have hnt : ∃ r, remainderRankOneAction Q split i hVi r ≠ 1 := by
    obtain ⟨r,hr⟩ := hntD
    refine ⟨r,fun heq => hr ?_⟩
    ext v
    have hv := congrArg (fun f : MulAut (simpleRemainder Q split i) =>
      (f ⟨v,commutator_le_self _ v.property⟩ : X ⧸ Q.D)) heq
    exact hv
  have hq : 2 ≤ 2^n := by have := Nat.one_lt_two_pow (show n ≠ 0 by omega); omega
  let : Group.IsPerfect SL(2,K) := GorensteinWalter.sl2_isPerfect_of_card_gt_three K (by rw [hK]; nlinarith)
  let : Group.IsPerfect (rankOne Q split i) := Group.IsPerfect.ofSurjective (f := μ.symm.toMonoidHom) μ.symm.surjective
  have hntF := frattini_action_nontrivial (split.isTwo.to_le (show simpleRemainder Q split i ≤ split.U from inf_le_left))
    (remainderRankOneAction Q split i hVi) hnt
  refine ⟨hcardPhi,hcardF,?_⟩
  apply minimal_linear_action_irreducible μ (remainderFrattiniAction Q split i hVi) hntF (show 1 < 2*n by omega)
  · rw [hK,←pow_mul]; congr 1; omega
  · rw [hcardF,hK]; ring

private theorem irreducible_of_pullback {k A B V : Type*} [Field k]
    [Group A] [Group B] [AddCommGroup V] [Module k V]
    (ρ : Representation k B V) (f : A →* B) (hi : Representation.IsIrreducible (ρ.comp f)) :
    ρ.IsIrreducible := by
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let W' : Subrepresentation (ρ.comp f) := ⟨W.toSubmodule,fun a v hv => W.apply_mem_toSubmodule (f a) hv⟩
  rcases eq_bot_or_eq_top W' with hz | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun T : Subrepresentation (ρ.comp f) => T.toSubmodule) hz
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun T : Subrepresentation (ρ.comp f) => T.toSubmodule) ht

/-- The same literal action supplies the irreducibility required by CoreField:
adding the full Cartan preserves the irreducible linear-actor action. -/
theorem unitary_linear_coreActor_irreducible
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (μ : rankOne Q split i ≃* SL(2,K))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hcardV : Nat.card (simpleRemainder Q split i) = (2^n)^8) :
    (UnitarySource.coreActorRepresentation Q split i hVi).IsIrreducible := by
  have hi := (unitary_linear_frattini_irreducible Q split J hn hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν hcardV).2.2
  let f : rankOne Q split i →* UnitarySource.coreActor Q split i :=
    inclusion (show rankOne Q split i ≤ UnitarySource.coreActor Q split i from le_sup_right)
  apply irreducible_of_pullback (UnitarySource.coreActorRepresentation Q split i hVi) f
  convert hi using 1
  rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
