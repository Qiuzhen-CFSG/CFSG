module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton
public import Theory.Representation.BinaryPlaneNormalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.Reduction
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Maximum transfer from the native hyperplane fixed-space estimate

For B.5.6(5), let I be the actual offender actor and H its selected S₃
factor. The fixed subrepresentation is C = C_{U_v}(H). The selected
moved plane splits off C. If the rank of the first coordinate projection
is at most its fixed codimension on C, the two coordinate ranks together
are at most the fixed codimension on U_v. An actual global maximum's
image is an offender, so cardinal counting forces it to fill its two
coordinate projections. A maximum moving the selected residual therefore
meets H nontrivially.

The same fixed-space estimate pays for restricting the maximum to the
FULL preimage of H: an explicit carrier equivalence identifies C with
`singletonFixed`, and commuting elements inject into its actual fixed
space. Thus adjoining C after restriction does not lower the order.
The existing singleton replacement theorem supplies the required witness.

The SL₃(2) bound on C remains an explicit premise. In particular this
module does not replace the source's hyperplane extension by a split
natural action, or assert that arbitrary quotient offenders split.
The module bound and final source assembly remain to be discharged.

The private coordinate cardinal calculation follows the checked singleton
DoubleFactor proof, specialized here through the native HyperplaneCase.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.4, printed pp.75–76; B.5.6(5), p.105; and 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer

/-- The actual fixed subrepresentation of the second native factor. -/
noncomputable def fixedPart {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) D V}
    (c : HyperplaneCase ρ) : Subrepresentation ρ := by
  let : c.second.Normal := c.product.second_normal
  exact fixedSubrepresentationOfNormal ρ c.second

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

section ModuleBounds
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
open CFSG.Quasithin.ChapterB.QuasisimpleSource

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

private theorem rank_le_codim (ρ : Representation (ZMod 2) D V) [Finite D] [FiniteDimensional (ZMod 2) V]
    (e : D ≃* Equiv.Perm (Fin 3)) (hf : Function.Injective ρ)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : rank A ≤ fixedCodim ρ A := by
  by_cases h : A = ⊥
  · simp only [h, Representation.BinaryOffender.rank_bot, Nat.zero_le]
  · exact (elementary_rank_le_one e A hA).trans
      (fixedCodim_pos_of_faithful ρ hf h)

private theorem codim_sum (ρ : Representation (ZMod 2) D V) [FiniteDimensional (ZMod 2) V]
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule)
    (A : Subgroup D) :
    fixedCodim U.toRepresentation A + fixedCodim W.toRepresentation A = fixedCodim ρ A := by
  let e := U.toSubmodule.prodEquivOfIsCompl W.toSubmodule hc
  have he := fixedCodim_map_equivariant (U.toRepresentation.prod W.toRepresentation) ρ
    (MonoidHom.id D) e (fun g x => by
      change ρ g x.1.val + ρ g x.2.val = ρ g (x.1.val + x.2.val)
      exact (map_add _ _ _).symm) A
  simpa only [Subgroup.map_id, fixedCodim_prod] using he


private theorem moved_coinvariants (ρ : Representation (ZMod 2) D V) (B : Subgroup D) :
    moved ρ B = Coinvariants.ker (ρ.comp B.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨g, hg, v, _, rfl⟩
    exact ⟨(⟨g, hg⟩, v), rfl⟩
  · rintro ⟨⟨g, v⟩, rfl⟩
    exact ⟨g, g.property, v, Submodule.mem_top, rfl⟩

/-- Once the complementary fixed-space bound is known, the selected S₃ plane
pays for the second projection. The native moved-space decomposition is used;
no decomposition of the quotient by the global fixed space is substituted. -/
theorem projection_bound_of_fixedPart_bound [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (c : HyperplaneCase ρ) (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A)
    (hfixed : rank (A.map c.product.fst) ≤ fixedCodim (fixedPart c).toRepresentation A) :
    rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤ fixedCodim ρ A := by
  let W := c.secondSpace
  let C := fixedPart c
  have hs : IsCompl W.toSubmodule C.toSubmodule := by
    change IsCompl c.secondSpace.toSubmodule (Representation.invariants (ρ.comp c.second.subtype))
    rw [c.secondSpace_eq, moved_coinvariants]
    apply BinaryPlaneNormalizer.symmetric_three_split (ρ.comp c.second.subtype)
      (hf.comp c.second.subtype_injective) e
    rwa [moved_coinvariants] at hd
  have hWf : Function.Injective (W.toRepresentation.comp c.second.subtype) := by
    intro a b hab
    apply c.second.subtype_injective
    apply hf
    ext v
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W.toSubmodule ⊔ C.toSubmodule from hs.sup_eq_top ▸ Submodule.mem_top)
    have hwab : ρ a w = ρ b w :=
      congrArg Subtype.val (LinearMap.congr_fun hab ⟨w, hw⟩)
    change ρ (a : D) (w + t) = ρ (b : D) (w + t)
    rw [map_add, map_add, hwab]
    exact congrArg (fun r => ρ (b : D) w + r) ((ht a).trans (ht b).symm)
  have hfirst (a : c.first) (w : W.toSubmodule) : W.toRepresentation a w = w := by
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp c.disjoint
    · exact Submodule.subset_span ⟨a, a.property, w, Submodule.mem_top, rfl⟩
    · rw [← c.secondSpace_eq]
      exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule a w.property) w.property
  have hx : ∀ (g : D) (w : W.toSubmodule),
      W.toRepresentation g w = W.toRepresentation (c.product.snd g : D) w := by
    intro g w
    have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
      (c.product.equiv.apply_symm_apply g).symm.trans (c.product.apply_eq _ _)
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    exact hfirst _ _
  have hb := rank_le_codim (W.toRepresentation.comp c.second.subtype) e hWf
    (A.map c.product.snd) (hA.map c.product.snd)
  have he := fixedCodim_map_equivariant W.toRepresentation
    (W.toRepresentation.comp c.second.subtype) c.product.snd (LinearEquiv.refl _ _) hx A
  rw [← he] at hb
  have hsum := codim_sum ρ W C hs A
  change rank (A.map c.product.fst) ≤ fixedCodim C.toRepresentation A at hfixed
  omega
end ModuleBounds

variable {G : Type*} [Group G] [Finite G]

private noncomputable def fixedCarrierEquiv (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    (fixedPart c).toSubmodule ≃
      singletonFixed z v (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype) where
  toFun w := ⟨⟨w.val.toMul, Uv_le_Gv z v hz w.val.toMul.property⟩,
    w.val.toMul.property, by
      intro a ha
      obtain ⟨b, hb, he⟩ := ha
      have hh := w.property (⟨b, hb⟩ : c.second)
      have heq := congrArg (fun t : Additive (Uv z v) => (t.toMul : G)) hh
      change ((starRepresentation z v (b : Gstar z v) w.val).toMul : G) = _ at heq
      change (b : Gstar z v) = starMk z v a at he
      rw [he, starRepresentation_mk_apply] at heq
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp heq)⟩
  invFun w := ⟨Additive.ofMul ⟨w.val, w.property.1⟩, by
    intro a
    obtain ⟨b, hb⟩ := starMk_surjective z v (a.val : Gstar z v)
    have hbm : b ∈ (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype).comap (starMk z v) := by
      change starMk z v b ∈ c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype
      rw [hb]
      exact mem_map_of_mem _ a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((starRepresentation z v (a.val : Gstar z v)
      (Additive.ofMul ⟨w.val, w.property.1⟩)).toMul : G) = _
    rw [← hb, starRepresentation_mk_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val (w.property.2 b hbm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixedCodim_card_bound (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (E : Subgroup (Gv v)) (hE : IsElementaryAbelian 2 E) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let A := (E.map (starMk z v)).subgroupOf I
    let C := singletonFixed z v (c.second.map I.subtype)
    2 ^ fixedCodim (fixedPart c).toRepresentation A ≤ E.relIndex C := by
  intro I A C
  let : IsElementaryAbelian 2 E := hE
  let e := fixedCarrierEquiv z v hz c
  let f : (E ⊓ C : Subgroup (Gv v)) → fixedSpace (fixedPart c).toRepresentation A :=
    fun x => ⟨e.symm ⟨x.val, x.property.2⟩, by
      intro a
      obtain ⟨b, hb, he⟩ := a.property
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((starRepresentation z v (a.val : Gstar z v)
        (e.symm ⟨x.val, x.property.2⟩).val).toMul : G) = _
      change starMk z v b = (a.val : Gstar z v) at he
      rw [← he, starRepresentation_mk_apply]
      apply mul_inv_eq_iff_eq_mul.mpr
      exact congrArg Subtype.val (show b * x.val = x.val * b from
        congrArg Subtype.val (mul_comm (⟨b, hb⟩ : E) ⟨x.val, x.property.1⟩))⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := e.symm.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun t : C => (t : Gv v)) hh)
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedPart c).toSubmodule := by
    rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hfix : Nat.card (fixedSpace (fixedPart c).toRepresentation A) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace (fixedPart c).toRepresentation A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix] at hle
  have hcount : Nat.card (E ⊓ C : Subgroup (Gv v)) * E.relIndex C = Nat.card C := by
    simpa only [relIndex_bot_left, inf_relIndex_right] using
      relIndex_mul_relIndex (⊥ : Subgroup (Gv v)) (E ⊓ C) C bot_le inf_le_right
  rw [hc, ← fixedCodim_add_finrank (fixedPart c).toRepresentation A, pow_add] at hcount
  have hm := Nat.mul_le_mul_right (E.relIndex C) hle
  rw [hcount, mul_comm (2 ^ fixedCodim _ _)] at hm
  exact Nat.le_of_mul_le_mul_left hm (by positivity)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]
open NormalThompson.Maximum.Singleton.HyperplaneTransfer

private theorem hyperplane_maximum_image_le_actor
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    E.map (starMk z v) ≤ FFFactors.offenderActor (starRepresentation z v) := by
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) =
      JGstar z v := starImage_intrinsic_thompson z v ⊤ (Gv v)
        (by rw [← MonoidHom.range_eq_map, range_subtype])
  exact (map_mono (le_sSup hE)).trans
    (hmap ▸ (minimalSolvable_global_thompson L T z v hz S hS hX).1)

/-- The native hyperplane product's additive codimension estimate makes an
actual global maximum meet its selected second coordinate. -/
theorem minimalSolvable_hyperplane_global_maximum_intersection_of_projection_bound
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hbound : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsElementaryAbelian 2 A →
      rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤
        fixedCodim (FFFactors.offenderRepresentation (starRepresentation z v)) A) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.second.map I.subtype ≠ ⊥ := by
  intro I
  obtain ⟨E, hE, hmove⟩ := minimalSolvable_exists_global_maximum_moving L T z v hz S hS hX
  have hEI : E.map (starMk z v) ≤ I :=
    hyperplane_maximum_image_le_actor L T z v hz S hS hX E hE
  have he : E.map (starMk z v) ≠ ⊥ := by
    intro he
    exact hmove (by rw [he, commutator_bot_right])
  have hEP : E ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) :=
    ⟨map_le_iff_le_comap.mp hEI, hE.2.1, fun A _ hA => hE.2.2 A le_top hA⟩
  have hoff := (NormalThompson.Maximum.Double.maxElementary_star_isOffender
    z v hz I E hEP he).subgroupOf (starRepresentation z v) hEI
  have hs := offender_splits_of_projection_bound _ c.product _ hoff (hbound _ hoff.1.2)
  have hh := congrArg (Subgroup.map I.subtype) hs
  have hsplit : E.map (starMk z v) =
      (E.map (starMk z v) ⊓ c.first.map I.subtype) ⊔
      (E.map (starMk z v) ⊓ c.second.map I.subtype) := by
    simpa only [Subgroup.map_sup, Subgroup.map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hEI] using hh
  refine ⟨E, hE, ?_⟩
  intro hzero
  have hEF : E.map (starMk z v) ≤ c.first.map I.subtype := by
    rw [hsplit, hzero, sup_bot_eq]
    exact inf_le_right
  obtain ⟨_, hF⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  have hXH : X ≤ c.second.map I.subtype := by
    rw [← minimalSolvable_selected_residual L T z v hz S hS hX c.second hF]
    exact map_subtype_le _
  have hc := factors_centralize c.product I.subtype
  exact hmove (commutator_eq_bot_iff_le_centralizer.mpr
    (hXH.trans ((le_centralizer_iff.mp hc).trans (centralizer_le hEF))))

/-- The two representation estimates suffice for the literal maximum witness
in the FULL preimage. This is a conditional transfer, not the discharge of
the hyperplane module estimates or the source theorem. -/
theorem minimalSolvable_hyperplane_maximum_of_codimension_bounds
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (hbound : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsElementaryAbelian 2 A →
      rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤
        fixedCodim (FFFactors.offenderRepresentation (starRepresentation z v)) A)
    (hfixed : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsElementaryAbelian 2 A →
      rank (A.map c.product.fst) ≤ fixedCodim (fixedPart c).toRepresentation A) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  intro I H
  let : H.Normal := minimalSolvable_hyperplane_normal L T z v hz S hS hfix hX c
  obtain ⟨E, hE, hne⟩ :=
    minimalSolvable_hyperplane_global_maximum_intersection_of_projection_bound
      L T z v hz S hS hX c hbound
  have hEI : E.map (starMk z v) ≤ I :=
    hyperplane_maximum_image_le_actor L T z v hz S hS hX E hE
  let A := (E.map (starMk z v)).subgroupOf I
  have hEA : IsElementaryAbelian 2 A := by
    let : IsElementaryAbelian 2 E := hE.2.1
    let : IsElementaryAbelian 2 (E.map (starMk z v)) := IsElementaryAbelian.map _
    exact IsElementaryAbelian.subgroupOf hEI
  have hi : H.relIndex (E.map (starMk z v)) = c.second.relIndex A := by
    rw [← map_subgroupOf_eq_of_le hEI]
    exact relIndex_map_map_of_injective _ _ I.subtype_injective
  apply star_maximum_of_singleton_index_bound z v hz H E hE hne
  rw [relIndex_comap, hi, ← c.product.ker_fst, relIndex_ker,
    elementary_card_pow_rank _ (hEA.map c.product.fst)]
  exact (Nat.pow_le_pow_right Nat.zero_lt_two (hfixed A hEA)).trans
    (fixedCodim_card_bound z v hz c E hE.2.1)


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
