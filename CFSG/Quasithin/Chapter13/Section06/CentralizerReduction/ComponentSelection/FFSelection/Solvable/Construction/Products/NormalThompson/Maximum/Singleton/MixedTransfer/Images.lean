module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.Reduction
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.GeneralLinearNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton

/-!
# Sharp global maxima when the complementary action has no strong offenders

The native B.5.6(3) quotient splits into two invariant summands. The S₃
coordinate costs at least its elementary rank. If the other summand has no
strong offenders, its cost has the same lower bound. These costs add, so an
actual global maximum image fills its two coordinate projections and attains
equality in the offender inequality. The original residual commutator then
selects such a maximum meeting the chosen S₃ coordinate.

These statements select maxima in G_v and retain the literal star map. They
do not assert that restricting a maximum to the chosen full preimage preserves
its order. That further rank-transfer step remains with the mixed assembly.

Source: Aschbacher–Smith B.2.4, B.5.6(3), and 13.6.13, printed pp.75–76,
105 and 929. The private coordinate and splitting calculations extend those
in the sibling Double/ProjectionCodimension and Singleton/DoubleFactor modules.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Images
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem no_sl3 {F : Type*} [Field F]
    (e : SL(3,F) ≃* Equiv.Perm (Fin 3)) : False := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hx := h (mem_top (Equiv.swap (0 : Fin 3) 1))
  have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) ≠ 1 := by decide
  exact hn hx

private theorem natural_faithful (F : BinaryField) (d : ℕ)
    (e : ActionEquiv ρ (linearNatural F d)) : Function.Injective ρ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective d
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  change linearNatural F d (e.groupEquiv g) (e.linearEquiv v) =
    linearNatural F d (e.groupEquiv h) (e.linearEquiv v)
  rw [← e.intertwines, ← e.intertwines]
  exact congrArg e.linearEquiv (LinearMap.congr_fun he v)

private theorem factor_faithful {B : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ B U) (e : B ≃* Equiv.Perm (Fin 3)) :
    U.toSubmodule = moved ρ B ∧
      Function.Injective (((fixed ρ).quotientImage U).toRepresentation.comp B.subtype) := by
  cases h with
  | natural hm h =>
    refine ⟨hm, ?_⟩
    cases h with
    | linearTwo F h => exact natural_faithful _ F 2 h.some
    | symmetricFive h =>
      have hc := Nat.card_congr (h.some.groupEquiv.symm.trans e).toEquiv
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        Nat.factorial] at hc
    | linearThree F _ h => exact (no_sl3 (h.some.groupEquiv.symm.trans e)).elim
  | doubleNatural F _ _ h => exact (no_sl3 (h.some.groupEquiv.symm.trans e)).elim
  | exceptional _ h => exact (no_sl3 (h.natural.groupEquiv.symm.trans e)).elim

private theorem elementary_rank_le_one [Finite D] (e : D ≃* Equiv.Perm (Fin 3))
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : rank A ≤ 1 := by
  let := hA
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hc : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hSc : Nat.card (S : Subgroup D) = 2 := by
    rw [S.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3)) 2 = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hAc : Nat.card A ≤ 2 := (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hS)).trans_eq hSc
  exact (Nat.log_mono_right hAc).trans (by decide : Nat.log 2 2 ≤ 1)

private theorem rank_le_codim [Finite D] [FiniteDimensional (ZMod 2) V]
    (e : D ≃* Equiv.Perm (Fin 3)) (hf : Function.Injective ρ)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : rank A ≤ fixedCodim ρ A := by
  by_cases h : A = ⊥
  · simp only [h, Representation.BinaryOffender.rank_bot, Nat.zero_le]
  · exact (elementary_rank_le_one e A hA).trans
      (fixedCodim_pos_of_faithful ρ hf h)

private theorem other_fixes_quotient {B : Subgroup D} {U W : Subrepresentation ρ}
    (hW : moved ρ B ≤ W.toSubmodule)
    (hd : Disjoint ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage W).toSubmodule)
    (b : B) (w : ((fixed ρ).quotientImage U).toSubmodule) :
    ((fixed ρ).quotientImage U).toRepresentation (b : D) w = w := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hd
  · exact ((fixed ρ).quotientImage U).toSubmodule.sub_mem
      (((fixed ρ).quotientImage U).apply_mem_toSubmodule b w.property) w.property
  · obtain ⟨v, hv⟩ := (fixed ρ).toSubmodule.mkQ_surjective (w : V ⧸ (fixed ρ).toSubmodule)
    change (fixed ρ).quotientRepresentation b w.val - w.val ∈
      W.toSubmodule.map (fixed ρ).toSubmodule.mkQ
    rw [← hv, Subrepresentation.quotientRepresentation_mk]
    refine ⟨ρ b v - v, ?_, map_sub _ _ _⟩
    apply hW
    exact Submodule.subset_span ⟨b, b.property, v, Submodule.mem_top, rfl⟩

private theorem codim_sum [FiniteDimensional (ZMod 2) V]
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule)
    (A : Subgroup D) :
    fixedCodim U.toRepresentation A + fixedCodim W.toRepresentation A = fixedCodim ρ A := by
  let e := U.toSubmodule.prodEquivOfIsCompl W.toSubmodule hc
  have he := fixedCodim_map_equivariant (U.toRepresentation.prod W.toRepresentation) ρ
    (MonoidHom.id D) e (fun g x => by
      change ρ g x.1.val + ρ g x.2.val = ρ g (x.1.val + x.2.val)
      exact (map_add _ _ _).symm) A
  simpa only [Subgroup.map_id, fixedCodim_prod] using he

private theorem rank_le_codim_of_not_strong [Finite D]
    (h : ¬ IsStrongFFModule ρ) (A : Subgroup D) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ fixedCodim ρ A := by
  by_cases ha : A = ⊥
  · simp only [ha, Representation.BinaryOffender.rank_bot, Nat.zero_le]
  · by_contra! hh
    exact h ⟨A, ⟨ha, hA⟩, hh⟩

private theorem factor_moved_le {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : moved ρ A ≤ U.toSubmodule := by
  cases h with
  | natural hm _ => exact hm.ge
  | doubleNatural _ _ hm _ => exact hm.ge
  | exceptional hm _ => exact hm

/-- A native S₃ coordinate and a complement with no strong offenders
force the additive projection bound, retaining every native module clause. -/
theorem projection_rank_le_fixedCodim [Finite D] [FiniteDimensional (ZMod 2) V]
    (c : SourceTwoFactorCase ρ) (e₁ : c.first ≃* Equiv.Perm (Fin 3))
    (hns : ¬ IsStrongFFModule
      (((fixed ρ).quotientImage c.secondSpace).toRepresentation.comp c.second.subtype))
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) :
    rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤ fixedCodim ρ A := by
  let U := (fixed ρ).quotientImage c.firstSpace
  let W := (fixed ρ).quotientImage c.secondSpace
  have h₁ := factor_faithful ρ c.firstCase e₁
  have hx₁ : ∀ (g : D) (w : U.toSubmodule),
      U.toRepresentation g w = U.toRepresentation (c.product.fst g : D) w := by
    intro g w
    have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
      (c.product.equiv.apply_symm_apply g).symm.trans (c.product.apply_eq _ _)
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    rw [other_fixes_quotient ρ (factor_moved_le ρ c.secondCase) c.decomposition.disjoint]
  have hx₂ : ∀ (g : D) (w : W.toSubmodule),
      W.toRepresentation g w = W.toRepresentation (c.product.snd g : D) w := by
    intro g w
    have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
      (c.product.equiv.apply_symm_apply g).symm.trans (c.product.apply_eq _ _)
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    exact other_fixes_quotient ρ h₁.1.ge c.decomposition.disjoint.symm _ _
  have hb₁ := rank_le_codim (U.toRepresentation.comp c.first.subtype) e₁ h₁.2
    (A.map c.product.fst) (hA.map c.product.fst)
  have hb₂ := rank_le_codim_of_not_strong (W.toRepresentation.comp c.second.subtype) hns
    (A.map c.product.snd) (hA.map c.product.snd)
  have he₁ := fixedCodim_map_equivariant U.toRepresentation
    (U.toRepresentation.comp c.first.subtype) c.product.fst (LinearEquiv.refl _ _) hx₁ A
  have he₂ := fixedCodim_map_equivariant W.toRepresentation
    (W.toRepresentation.comp c.second.subtype) c.product.snd (LinearEquiv.refl _ _) hx₂ A
  rw [← he₁] at hb₁
  rw [← he₂] at hb₂
  have hs := codim_sum (fixed ρ).quotientRepresentation U W c.decomposition A
  have hq := fixedCodim_quotient_add_subrepresentation_le ρ (fixed ρ) A
  omega

private theorem elementary_card_pow_rank {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : Nat.card A = 2 ^ rank A := by
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow Nat.one_lt_two]

private theorem offender_splits_of_projection_bound
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {F K : Subgroup D} (h : InternalProduct F K)
    (A : Subgroup D) (hA : IsOffender ρ A)
    (hbound : rank (A.map h.fst) + rank (A.map h.snd) ≤ fixedCodim ρ A) :
    A = (A ⊓ F) ⊔ (A ⊓ K) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let R := ((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom
  have hAR : A ≤ R := by
    intro a ha
    exact ⟨h.equiv.symm a, ⟨mem_map_of_mem h.fst ha, mem_map_of_mem h.snd ha⟩,
      h.equiv.apply_symm_apply a⟩
  have heq : A = R := by
    apply eq_of_le_of_card_ge hAR
    change Nat.card (((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom) ≤ _
    rw [card_map_of_injective h.equiv.injective,
      Nat.card_congr (Subgroup.prodEquiv (A.map h.fst) (A.map h.snd)).toEquiv, Nat.card_prod,
      elementary_card_pow_rank _ (hA.1.2.map h.fst),
      elementary_card_pow_rank _ (hA.1.2.map h.snd),
      elementary_card_pow_rank _ hA.1.2, ← pow_add]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (hbound.trans hA.2)
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro a ha
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, hxy⟩ := heq ▸ ha
  have hxA : (x : D) ∈ A := by
    rw [heq]
    exact ⟨(x, 1), ⟨hx, one_mem _⟩, by
      change h.equiv (x, 1) = (x : D)
      simp only [h.apply_eq, OneMemClass.coe_one, mul_one]⟩
  have hyA : (y : D) ∈ A := by
    rw [heq]
    exact ⟨(1, y), ⟨one_mem _, hy⟩, by
      change h.equiv (1, y) = (y : D)
      simp only [h.apply_eq, OneMemClass.coe_one, one_mul]⟩
  change h.equiv (x,y) = a at hxy
  rw [← hxy, h.apply_eq]
  exact ((A ⊓ F) ⊔ (A ⊓ K)).mul_mem
    ((le_sup_left : A ⊓ F ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hxA, x.property⟩)
    ((le_sup_right : A ⊓ K ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hyA, y.property⟩)


private theorem factors_centralize {D Y : Type*} [Group D] [Group Y]
    {F K : Subgroup D} (h : InternalProduct F K) (f : D →* Y) :
    F.map f ≤ centralizer (K.map f : Set Y) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg f
  have hc := congrArg h.equiv
    (show (1, (⟨b, hb⟩ : K)) * ((⟨a, ha⟩ : F), 1) =
      ((⟨a, ha⟩ : F), 1) * (1, (⟨b, hb⟩ : K)) by simp)
  rw [map_mul, map_mul] at hc
  simpa only [h.apply_eq, OneMemClass.coe_one, one_mul, mul_one] using hc


/-- With the coordinate bound, an offender is sharp and fills the product
of its two projections. Both conclusions are needed by rank replacement. -/
theorem offender_split_and_sharp [Finite D] [FiniteDimensional (ZMod 2) V]
    (c : SourceTwoFactorCase ρ) (e : c.first ≃* Equiv.Perm (Fin 3))
    (hns : ¬ IsStrongFFModule
      (((fixed ρ).quotientImage c.secondSpace).toRepresentation.comp c.second.subtype))
    (A : Subgroup D) (hA : IsOffender ρ A) :
    A = (A ⊓ c.first) ⊔ (A ⊓ c.second) ∧ fixedCodim ρ A = rank A := by
  have hb := projection_rank_le_fixedCodim ρ c e hns A hA.1.2
  refine ⟨offender_splits_of_projection_bound ρ c.product A hA hb, le_antisymm hA.2 ?_⟩
  apply le_trans _ hb
  have hi : Function.Injective (fun a : A =>
      ((⟨c.product.fst a, mem_map_of_mem _ a.property⟩ : A.map c.product.fst),
       (⟨c.product.snd a, mem_map_of_mem _ a.property⟩ : A.map c.product.snd))) := by
    intro a b hab
    apply Subtype.ext
    apply c.product.equiv.symm.injective
    exact Prod.ext (congrArg (fun x => x.1.val) hab) (congrArg (fun x => x.2.val) hab)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_prod, elementary_card_pow_rank _ hA.1.2,
    elementary_card_pow_rank _ (hA.1.2.map c.product.fst),
    elementary_card_pow_rank _ (hA.1.2.map c.product.snd), ← pow_add] at hc
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hc

private def swapProduct {D : Type*} [Group D]
    {A B : Subgroup D} (h : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans h.equiv
  apply_eq b a := by
    change h.equiv (a, b) = (b : D) * a
    have hc := congrArg h.equiv (show (a, (1 : B)) * (1, b) = (1, b) * (a, 1) by simp)
    rw [map_mul, map_mul, h.apply_eq, h.apply_eq] at hc
    simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hc

private def swapCase (c : SourceTwoFactorCase ρ) : SourceTwoFactorCase ρ where
  first := c.second
  second := c.first
  product := swapProduct c.product
  firstSpace := c.secondSpace
  secondSpace := c.firstSpace
  decomposition := c.decomposition.symm
  firstCase := c.secondCase
  secondCase := c.firstCase

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Images

open Stellmacher
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open NormalThompson.Maximum.Singleton.MixedTransfer.Images
variable {G : Type*} [Group G] [Finite G]

/-- In the branch without strong complementary offenders, every nontrivial
global maximum image is split and sharp for the original star action. -/
theorem minimalSolvable_twoFactor_first_split_sharp_of_nonstrong_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hns : ¬ IsStrongFFModule
      (((fixed (FFFactors.offenderRepresentation (starRepresentation z v))).quotientImage
        c.secondSpace).toRepresentation.comp c.second.subtype))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ≠ ⊥) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    E.map (starMk z v) = (E.map (starMk z v) ⊓ c.first.map I.subtype) ⊔
      (E.map (starMk z v) ⊓ c.second.map I.subtype) ∧
      fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
        rank (E.map (starMk z v)) := by
  intro I
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) =
      JGstar z v := starImage_intrinsic_thompson z v ⊤ (Gv v)
        (by rw [← MonoidHom.range_eq_map, range_subtype])
  have hEI : E.map (starMk z v) ≤ I := by
    apply (map_mono (le_sSup hE)).trans
    change (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) ≤ I
    rw [hmap]
    exact (minimalSolvable_global_thompson L T z v hz S hS hX).1
  have hEP : E ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) :=
    ⟨map_le_iff_le_comap.mp hEI, hE.2.1, fun A _ hA => hE.2.2 A le_top hA⟩
  have hoff := (NormalThompson.Maximum.Double.maxElementary_star_isOffender
    z v hz I E hEP hne).subgroupOf (starRepresentation z v) hEI
  obtain ⟨hs, hsharp⟩ := offender_split_and_sharp _ c e hns _ hoff
  have hh := congrArg (Subgroup.map I.subtype) hs
  refine ⟨?_, ?_⟩
  · simpa only [Subgroup.map_sup, Subgroup.map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hEI] using hh
  · have hd := fixedCodim_map_equivariant
      (FFFactors.offenderRepresentation (starRepresentation z v)) (starRepresentation z v)
      I.subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) ((E.map (starMk z v)).subgroupOf I)
    rw [map_subgroupOf_eq_of_le hEI] at hd
    rw [hd] at hsharp
    rw [← rank_map_injective I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hEI] at hsharp
    exact hsharp

/-- Choose an actual global maximum meeting the selected first factor and
satisfying the sharp B.2.4 equality. This does not assert maximum order in
the smaller full preimage. -/
theorem minimalSolvable_twoFactor_first_global_maximum_sharp_of_nonstrong_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hns : ¬ IsStrongFFModule
      (((fixed (FFFactors.offenderRepresentation (starRepresentation z v))).quotientImage
        c.secondSpace).toRepresentation.comp c.second.subtype))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.first.map I.subtype ≠ ⊥ ∧
      fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
        rank (E.map (starMk z v)) := by
  intro I
  obtain ⟨E, hE, hmove⟩ := minimalSolvable_exists_global_maximum_moving L T z v hz S hS hX
  have hne : E.map (starMk z v) ≠ ⊥ := by
    intro hb
    exact hmove (by rw [hb, commutator_bot_right])
  obtain ⟨hs, hsharp⟩ := minimalSolvable_twoFactor_first_split_sharp_of_nonstrong_complement
    L T z v hz S hS hX c e hns E hE hne
  refine ⟨E, hE, ?_, hsharp⟩
  intro hzero
  have hEK : E.map (starMk z v) ≤ c.second.map I.subtype := by
    rw [hs, hzero, bot_sup_eq]
    exact inf_le_right
  have hXH : X ≤ c.first.map I.subtype := by
    rw [← minimalSolvable_selected_residual L T z v hz S hS hX c.first hF]
    exact map_subtype_le _
  have hc := factors_centralize c.product I.subtype
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hXH.trans (hc.trans (centralizer_le hEK)))

/-- The symmetric global-maximum selection for the second coordinate,
with every quotient-action clause carried through the exchanged case. -/
theorem minimalSolvable_twoFactor_second_global_maximum_sharp_of_nonstrong_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hns : ¬ IsStrongFFModule
      (((fixed (FFFactors.offenderRepresentation (starRepresentation z v))).quotientImage
        c.firstSpace).toRepresentation.comp c.first.subtype))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.second.map I.subtype ≠ ⊥ ∧
      fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
        rank (E.map (starMk z v)) := by
  exact minimalSolvable_twoFactor_first_global_maximum_sharp_of_nonstrong_complement
    L T z v hz S hS hX (swapCase _ c) e hns hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
