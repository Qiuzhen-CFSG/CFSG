module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Quasithin.Rank

/-!
# The selected SL₃ component modulo its intrinsic two-core

Apply the universal A.3.6 theorem in the actual quotient X/O₂(X), and
identify its C-component image with B/O₂(B). A surjection from B onto
SL₃(F) induces a surjection from this image onto PSL₃(F): the normal
two-core has solvable image, hence vanishes in the nonabelian simple target.

In either nonquasisimple A.3.6 alternative, F*(B) = F(B) is solvable and
the quotient is SL₂(p) for a prime p > 3. Killing that solvable subgroup
and then the SL₂ center would give a surjection PSL₂(p) → PSL₃(F).
Simplicity makes this an isomorphism. But the affine line-local subgroup
of PSL₃(F) contains the elementary translation plane F², of two-rank 2m,
whereas PSL₂(p) has two-rank two. Thus m > 1 excludes both alternatives.
No rank lifting through arbitrary quotients is used. The small-field
boundary is essential to this comparison: PSL₃(2) is isomorphic to PSL₂(7).

The source application takes B = K.subgroupOf (K ⊔ Tᵥ), as supplied by
Yz, and uses the canonical subgroup equivalence followed by the literal
componentPlusMap and the supplied SL₃ equivalence. Simple QTKE gives SQTK
for this actual overgroup inside C_G(v). The last theorem specializes to
the complete known-simple catalogue. The universal A.3.6 input remains
explicit, with its discharge owned by qt-a03-sqtk-structure and the final
centralizer-reduction assembly. No plus-kernel centrality or two-group
hypothesis is assumed. KernelControl can import this module without a cycle.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45, and the setup and SL₃ branch of 13.6.19, pp.929–931.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.IntrinsicComponent

private theorem solvable_normal_le_ker {A S : Type*} [Group A] [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (f : A →* S) (hf : Function.Surjective f)
    (N : Subgroup A) [N.Normal] [Group.IsSolvable N] : N ≤ f.ker := by
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  let : Group.IsSolvable (N.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  apply (Subgroup.map_eq_bot_iff N).mp
  rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isSolvable S
      (Group.isSolvable_of_surjective
        (f := ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).toMonoidHom)
        ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).surjective)).elim

private theorem injective_of_simple_surjective {A S : Type*} [Group A] [Group S]
    [IsSimpleGroup A] [Nontrivial S] (f : A →* S) (hf : Function.Surjective f) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨y, hy⟩ := exists_ne (1 : S)
    obtain ⟨x, rfl⟩ := hf y
    exact (hy (show x ∈ f.ker from h ▸ mem_top x)).elim

private theorem root_plane_rank (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    2 * m ≤ primeRank 2 PSL(3,F) := by
  let U := Multiplicative (Fin 2 → F)
  let : IsElementaryAbelian 2 U := by
    constructor
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    apply Multiplicative.toAdd.injective
    ext i
    change 2 • v.toAdd i = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
  let e := Matrix.PSL3.LinearThree.lineLocalEquivAffine F
  let f : U →* PSL(3,F) := (Matrix.PSL3.LinearThree.lineLocal F).subtype.comp
    (e.symm.toMonoidHom.comp SemidirectProduct.inl)
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.symm.injective.comp SemidirectProduct.inl_injective)
  let a : U ≃* f.range := MonoidHom.ofInjective hf
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  apply IsElementaryAbelian.primeRank_ge_of_card f.range
  rw [← Nat.card_congr a.toEquiv]
  change Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fin, hF, ← pow_mul, Nat.mul_comm m 2]

private theorem no_sl2_prime_surjection (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (f : SL(2, ZMod p) →* PSL(3,F)) (hf : Function.Surjective f) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let : IsSimpleGroup PSL(2, ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  let : CommGroup (center SL(2, ZMod p)) := IsMulCommutative.instCommGroup
  have hk := solvable_normal_le_ker f hf (center SL(2, ZMod p))
  let q : PSL(2, ZMod p) →* PSL(3,F) := QuotientGroup.lift _ f hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let e := MulEquiv.ofBijective q ⟨injective_of_simple_surjective q hq, hq⟩
  have hr := root_plane_rank F hF
  rw [← primeRank_equiv 2 e, Theory.PSL2.primeField_two_rank hlarge] at hr
  omega

private theorem no_sl2_quotient (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    {A : Type*} [Group A] [Finite A]
    (f : A →* PSL(3,F)) (hf : Function.Surjective f)
    (hfit : generalizedFitting A = fittingSubgroup A)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hsl : IsSL (A ⧸ generalizedFitting A) 2 p) : False := by
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let : Group.IsSolvable (generalizedFitting A) := by rw [hfit]; infer_instance
  have hk := solvable_normal_le_ker f hf (generalizedFitting A)
  let q := QuotientGroup.lift _ f hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  obtain ⟨k, _, _, hc, ⟨e⟩⟩ := hsl
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite k
  let c : k ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime k hp (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
  let a := e.trans (Atlas.fieldEquivSL 2 c)
  exact no_sl2_prime_surjection F hF hm hp hlarge
    (q.comp a.symm.toMonoidHom) (hq.comp a.symm.surjective)

private theorem classified_intrinsic (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    {X : Type*} [Group X] [Finite X] (B : Subgroup X)
    (h : A36Alternative B) (f : B →* PSL(3,F)) (hf : Function.Surjective f) :
    IsQuasisimple B := by
  cases h with
  | simple hc _ _ => exact hc.2
  | cover hc _ _ => exact hc.2
  | natural h =>
    obtain ⟨p, hp, hlarge, k, _, _, hc, _, e, _⟩ := h.2
    exact (no_sl2_quotient F hF hm f hf h.1 hp hlarge
      ⟨k, inferInstance, inferInstance, hc, ⟨e⟩⟩).elim
  | nilpotent h =>
    exact (no_sl2_quotient F hF hm f hf h.1 (by decide) (by decide) h.2.2.1).elim

universe u
/-- A C-component with a higher-field SL₃ image has quasisimple intrinsic
two-core quotient, conditional only on the universal earlier A.3.6 input. -/
theorem cComponent_twoCore_quasisimple_of_sl3
    {X : Type u} [Group X] [Finite X] {κ : GroupClass.{u}}
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hsq : IsSQTK κ X) (B : Subgroup X) (hB : B.IsCComponent)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (f : B →* SL(3,F)) (hf : Function.Surjective f) :
    IsQuasisimple (B ⧸ pCore 2 B) := by
  have hsqQ : IsSQTK κ (X ⧸ pCore 2 X) := by
    refine ⟨?_, hsq.isKGroup.quotient (pCore 2 X)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have ha := proposition_1_2_1_four_earlier_conclusion hA36 hsqQ hB
  let e := cComponentTwoCoreQuotientEquiv hB
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let g := (QuotientGroup.mk' (center SL(3,F))).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  let := pCore_isNilpotent (p := 2) (G := B)
  have hk := solvable_normal_le_ker g hg (pCore 2 B)
  let q := QuotientGroup.lift _ g hk
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ hg _
  let := classified_intrinsic F hF hm _ ha.1 (q.comp e.symm.toMonoidHom)
    (hq.comp e.symm.surjective)
  exact IsQuasisimple.of_mulEquiv e.symm

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree

/-- Apply the intrinsic deduction to the literal C-component in K ⊔ Tᵥ and
the given equivalence of its plus image with SL₃(F). -/
theorem source_intrinsic_quasisimple
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3,F)) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let D := K ⊔ Tv T v
  let B := K.subgroupOf D
  have hle : D ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hsq : IsSQTK κ D := (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup (D.subgroupOf (Gv v)))
  let a : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := e.toMonoidHom.comp ((componentPlusMap K L T z v hL hz).comp a.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    ((componentPlusMap_surjective K L T z v hL hz).comp a.surjective)
  let := cComponent_twoCore_quasisimple_of_sl3 hA36 hsq B hK.1.2.1 F hF hm f hf
  exact IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr (pCore 2 B) (pCore 2 K) a (pCore_map_iso 2 a))

/-- The source specialization retains the full known-simple K-group catalogue. -/
theorem source_intrinsic_quasisimple_knownSimple
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3,F)) :
    IsQuasisimple (K ⧸ pCore 2 K) :=
  source_intrinsic_quasisimple hG hA36 K L T z v hv hK hL hz F hF hm e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.IntrinsicComponent
