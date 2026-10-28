module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Baumann
public import Stellmacher.SectionThree.OmegaNormalClosureElementary
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PCoreOvergroup
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The internal module for the E.2.3 application

For H = YT the module to which E.2.3 is applied is
U = <Omega_1(Z(T))^H>. It need not be the whole of V(M): restriction to H
does not in general preserve two-reducedness. The source centralizer equality
C_G(Omega_1(Z(T))) = T identifies C_H(U) with the actual two-core of H.
Characteristic two places U in the elementary omega-center of that core.
Finally Y = [Y,J(T)] excludes centralization of U by J(T), since otherwise
the nontrivial two-perfect group Y would be a two-group.

These are application prerequisites, not clauses (4)--(6) of 15.4.12.
The factor actions and maximal reduced-module decomposition still require
the complete E.2.3 conclusion and the small binary module calculation.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
E.2.3, printed pp.216--217 (PDF pp.227--228), and the application in
15.4.12, printed pp.1160--1161. In E.2.3 the tilde quotient uses O^2(H),
the two-residual, and not O_2(H).
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
variable {G : Type*} [Group G]

/-- The genuine inputs preceding clauses (4)--(6). No module decomposition,
quotient action, or permutation of factors is included. -/
structure Input [Finite G] (K : GroupClass) (T : Sylow 2 G) (M X : Subgroup G) (s : ℕ) : Prop where
  ambient : IsSimpleQTKE K G
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  solvable : Group.IsSolvable M
  center_centralizer : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T
  thompson_moved : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥
  member : X ∈ Y (T : Subgroup G)
  member_le : X ≤ M
  normal : (X.subgroupOf M).Normal
  parameter : s = 1 ∨ s = 2
  quotient_elementary : IsElementaryAbelian 3 (X ⧸ pCore 2 X)
  quotient_card : Nat.card (X ⧸ pCore 2 X) = 3 ^ s
  moved_rank : Group.rank ↥(⁅localV T M, X⁆ : Subgroup G) = 2 * s

/-- The internal normal closure, with no implicit change of acting group. -/
abbrev internalModule (T H : Subgroup G) : Subgroup H :=
  normalClosure ((omegaOneCenterAmbient T).subgroupOf H : Set H)

/-- The source fixed summand E_Y in ambient coordinates. -/
noncomputable def fixedSummand (T X : Subgroup G) : Subgroup G :=
  omegaOneCenterAmbient ((X ⊔ T).pCoreIn 2) ⊓ centralizer (X : Set G)

/-- The normal closure lies in its specified overgroup. -/
theorem localV_le (T H : Subgroup G) : localV T H ≤ H := map_subtype_le _

/-- Relative normality of the literal normal closure. -/
theorem localV_normalized (T H : Subgroup G) :
    H ≤ normalizer (localV T H : Set G) := by
  have hh := (internalModule T H).le_normalizer_map H.subtype
  simpa only [internalModule, localV, normalizer_eq_top,
    ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Centralizers agree internally as well as after embedding in G. -/
theorem internal_centralizer (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    centralizer (internalModule T H : Set H) = pCore 2 H := by
  apply map_injective H.subtype_injective
  rw [map_centralizer_subtype]
  exact localV_centralizer T H hTH hC

private theorem core_le_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : H.pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
    pCoreIn_le_sylow H (T.subtype hTH)

private theorem omega_le_core (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : HasCharacteristicTwo H) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ H.pCoreIn 2 := by
  intro z hz
  obtain ⟨hzT, _, hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzC : (⟨z, hTH hzT⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
    intro q hq
    exact Subtype.ext (hzc q (core_le_sylow T H hTH ⟨q, hq, rfl⟩))
  exact mem_map.mpr ⟨⟨z, hTH hzT⟩, hH hzC, rfl⟩

/-- Characteristic two places the chosen internal module in the omega-center
of the actual two-core of its acting group. -/
theorem internalModule_le_core_omega (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : HasCharacteristicTwo H) :
    internalModule T H ≤ omegaOneCenterAmbient (pCore 2 H) := by
  have hn : ((H.pCoreIn 2).subgroupOf H).Normal := by
    change (((pCore 2 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hh := SectionThree.omegaOneCenter_normalClosure_le_containerOmega
    (T : Subgroup G) H (H.pCoreIn 2) (pCoreIn_le 2 H)
    (core_le_sylow T H hTH) hn (omega_le_core T H hTH hH)
  simpa only [internalModule, pCoreIn, subgroupOf,
    comap_map_eq_self_of_injective H.subtype_injective] using hh

/-- In particular the internal module is elementary abelian. -/
theorem internalModule_elementary (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : HasCharacteristicTwo H) :
    IsElementaryAbelian 2 (internalModule T H) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hle := internalModule_le_core_omega T H hTH hH
  refine { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
    (show (x : H) * (y : H) = (y : H) * (x : H) from ?_)⟩⟩, exponent_dvd_p := ?_ }
  · exact congrArg Subtype.val
      (mul_comm (⟨x, hle x.property⟩ : omegaOneCenterAmbient (pCore 2 H))
        ⟨y, hle y.property⟩)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := omegaOneCenterAmbient (pCore 2 H)) (x : H) (hle x.property))

/-- The ambient V(H) is elementary abelian as well. -/
theorem localV_elementary (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : HasCharacteristicTwo H) :
    IsElementaryAbelian 2 (localV T H) := by
  let : IsElementaryAbelian 2 (internalModule T H) := internalModule_elementary T H hTH hH
  exact IsElementaryAbelian.map H.subtype

/-- The ambient V(H) belongs to the given Sylow subgroup. -/
theorem localV_le_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : HasCharacteristicTwo H) :
    localV T H ≤ (T : Subgroup G) := by
  apply le_trans (map_mono (internalModule_le_core_omega T H hTH hH))
  apply le_trans (map_mono (show omegaOneCenterAmbient (pCore 2 H) ≤ pCore 2 H from
    fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
  exact core_le_sylow T H hTH

/-- Enlarging the group acting on the fixed seed enlarges its normal closure. -/
theorem localV_mono (T : Subgroup G) {H M : Subgroup G} (hHM : H ≤ M) :
    localV T H ≤ localV T M := by
  have hn : ((localV T M).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (hHM.trans (localV_normalized T M))
  have hh : internalModule T H ≤ (localV T M).subgroupOf H := by
    apply normalClosure_le_normal
    intro z hz
    exact mem_map.mpr ⟨⟨z, hHM z.property⟩, le_normalClosure hz, rfl⟩
  exact (map_mono hh).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

/-- The embedded two-residual of YT is Y itself. -/
theorem member_residual_join (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G)) :
    (pResidual 2 ↥(X ⊔ (T : Subgroup G))).map (X ⊔ (T : Subgroup G)).subtype = X := by
  let A := X.subgroupOf (X ⊔ (T : Subgroup G))
  let B := (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G))
  let eA : X ≃* A := (subgroupOfEquivOfLe le_sup_left).symm
  have hA : IsPPerfect 2 A := (YFamily.perfect hX).of_surjective eA.toMonoidHom eA.surjective
  have hB : IsPGroup 2 B := T.isPGroup'.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  let : A.Normal := YFamily.normal_in_join hX
  have hgen : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  rw [pResidual_eq_of_isPPerfect_sup A B hA hB hgen,
    map_subgroupOf_eq_of_le le_sup_left]

/-- The family identity forces a nontrivial Thompson action on U, the
internal normal closure in YT; this premise is not borrowed from V(M). -/
theorem member_thompson_not_centralizes [Finite G] (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localV T (X ⊔ (T : Subgroup G)) : Set G) := by
  intro hj
  have hJH : elementaryAbelianMaxJ (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) := by
    rw [← ChapterB.thompsonJ_zero]
    exact (ChapterB.thompsonJ_le _ 0).trans le_sup_right
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← localV_centralizer T _ le_sup_right hC]
    exact le_inf hJH hj
  have hn : X ≤ normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_left.trans ((X ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 ↥(X ⊔ (T : Subgroup G)))))
  have hXQ : X ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
    conv_lhs => rw [← YFamily.commutator_eq hX]
    exact (commutator_mono le_rfl hJQ).trans (le_normalizer_iff_commutator_le_right.mp hn)
  have hp : IsPGroup 2 X := (isPGroup_pCoreIn 2 _).of_injective (inclusion hXQ)
    (inclusion_injective hXQ)
  have hbot : (⊥ : Subgroup X) = ⊤ := (YFamily.perfect hX) ⊥ inferInstance
    (hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥))
  apply YFamily.ne_bot hX
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : (⟨x, hx⟩ : X) ∈ (⊥ : Subgroup X) := hbot ▸ mem_top _
  exact congrArg Subtype.val (mem_bot.mp hx')

/-- The specified internal module has trivial two-core in its faithful
quotient. This is the literal reducedness condition of B.2.11. -/
theorem internalModule_reduced [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    pCore 2 (H ⧸ centralizer (internalModule T H : Set H)) = ⊥ := by
  let q := QuotientGroup.mk' (centralizer (internalModule T H : Set H))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', internal_centralizer T H hTH hC]
    exact pCore_isPGroup
  apply comap_injective (QuotientGroup.mk'_surjective _)
  rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk]
  change pCore 2 H = q.ker
  rw [QuotientGroup.ker_mk', internal_centralizer T H hTH hC]

/-- Remove the trivial Frattini quotient in the elementary branch of Xi.
Invariance is still expressed through the literal preimage in X and its
original embedding in G. -/
theorem member_quotient_irreducible [Finite G] (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (he : IsElementaryAbelian 3 (X ⧸ pCore 2 X)) :
    ∀ A : Subgroup (X ⧸ pCore 2 X),
      (T : Subgroup G) ≤ normalizer
        ((A.comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype : Set G) →
      A = ⊥ ∨ A = ⊤ := by
  rcases hX.1 with hx | hx
  · let : IsElementaryAbelian 3 (X ⧸ pCore 2 X) := he
    let : Fact (IsPGroup 3 (X ⧸ pCore 2 X)) := ⟨IsElementaryAbelian.isPGroup 3 _⟩
    let := conjMulDistribMulActionOfLeNormalizer (T : Subgroup G) X hx.invariant
    let q := QuotientGroup.mk' (frattini (X ⧸ pCore 2 X))
    have hq : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff q).mp
      rw [QuotientGroup.ker_mk', frattini_eq_bot_of_isElementaryAbelian (p := 3)]
    intro A hn
    have hstable : ∀ (t : (T : Subgroup G)) a,
        a ∈ A.map q → Chapter1.xiFrattiniAction (T : Subgroup G) X hx.invariant t a ∈ A.map q := by
      rintro t _ ⟨a, ha, rfl⟩
      induction a using QuotientGroup.induction_on with | H x =>
        simp only [q, Chapter1.xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
        apply mem_map.mpr
        refine ⟨_, ?_, rfl⟩
        have hxA : (x : G) ∈ (A.comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype :=
          mem_map.mpr ⟨x, ha, rfl⟩
        have htA := (mem_normalizer_iff.mp (hn t.property) (x : G)).mp hxA
        obtain ⟨z, hz, heq⟩ := htA
        change quotientAut (pCore 2 X) (MulDistribMulAction.toMulAut (T : Subgroup G) X t)
          (QuotientGroup.mk' (pCore 2 X) x) ∈ A
        rw [quotientAut_apply_mk]
        have heq' : z = MulDistribMulAction.toMulAut (T : Subgroup G) X t x :=
          Subtype.ext heq
        change QuotientGroup.mk' (pCore 2 X) z ∈ A at hz
        rw [heq'] at hz
        exact hz
    rcases hx.irreducible (A.map q) hstable with ha | ha
    · exact Or.inl ((A.map_eq_bot_iff_of_injective hq).mp ha)
    · right
      apply map_injective hq
      rw [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
      exact ha
  · exact LocalSetup.quotient_irreducible_of_prime_core_index (T : Subgroup G) X hx.2.2.2.1

/-- Both source families exclude a two-group member. -/
theorem member_core_ne_top (T : Subgroup G) {X : Subgroup G}
    (hX : X ∈ Y T) : pCore 2 X ≠ ⊤ := by
  rcases hX.1 with hx | hx
  · intro hc
    obtain ⟨p, hp, _, hq⟩ := hx.odd_quotient
    have hcard := Chapter1.XiOddQuotient.one_lt_card hp hq
    have hc' : Nat.card (X ⧸ pCore 2 X) = 1 := (pCore 2 X).index_eq_one.mpr hc
    exact (ne_of_gt hcard) hc'
  · exact Xi.core_ne_top hx

/-- Every specified member with the clause (3) elementary quotient gives the
actual minimal parabolic YT required by E.2.3. -/
theorem member_minimalParabolic [Finite G] (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (he : IsElementaryAbelian 3 (X ⧸ pCore 2 X)) :
    ChapterB.IsMinimalParabolicOver T (X ⊔ (T : Subgroup G)) := by
  apply LocalSetup.minimalParabolic_join_of_quotient_irreducible T X
    (YFamily.invariant hX) (member_core_ne_top _ hX) (member_quotient_irreducible T hX he)
  simpa only [ChapterB.thompsonJ_zero] using hX.2

/-- Minimal parabolicity in the internal group H = YT, with the actual
restricted Sylow subgroup. -/
theorem member_internal_minimalParabolic [Finite G] (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (he : IsElementaryAbelian 3 (X ⧸ pCore 2 X)) :
    ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ X ⊔ T from le_sup_right))
      ⊤ := by
  let H := X ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hcov := LocalSetup.sylow_covBy_join_of_quotient_irreducible T X
    (YFamily.invariant hX) (member_core_ne_top _ hX) (member_quotient_irreducible T hX he)
  have hPmap : (P : Subgroup H).map H.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hcov' : (P : Subgroup H) ⋖ ⊤ := by
    refine ⟨(map_lt_map_iff_of_injective H.subtype_injective).mp ?_, ?_⟩
    · rw [hPmap, htop]
      exact hcov.lt
    · intro A hPA hAtop
      apply hcov.2
        (show (T : Subgroup G) < A.map H.subtype from ?_)
        (show A.map H.subtype < H from ?_)
      · rw [← hPmap]
        exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hPA
      · exact lt_of_lt_of_eq
          ((map_lt_map_iff_of_injective H.subtype_injective).mpr hAtop) htop
  apply (ChapterB.isMinimalParabolicOver_top_iff P).mpr
  refine ⟨⟨(P : Subgroup H), ⟨hcov'.isCoatom, le_rfl⟩, ?_⟩, ?_⟩
  · intro A hA
    exact (hcov'.eq_or_eq hA.2 le_top).resolve_right hA.1.ne_top
  · intro hn
    have hN : ((T : Subgroup G).subgroupOf H).Normal := by
      simpa only [P, Sylow.coe_subtype] using hn
    exact (ChapterB.isMinimalParabolicOver_iff T H).mp (member_minimalParabolic T hX he) |>.2 hN

/-- Thompson noncentralization expressed entirely in H, as in E.2.3. -/
theorem member_internal_thompson_not_centralizes [Finite G] (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Y (T : Subgroup G))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    ¬ elementaryAbelianMaxJ
        (T.subtype (show (T : Subgroup G) ≤ X ⊔ T from le_sup_right) : Subgroup ↥(X ⊔ (T : Subgroup G))) ≤
      centralizer (internalModule T (X ⊔ (T : Subgroup G)) : Set ↥(X ⊔ (T : Subgroup G))) := by
  let H := X ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  intro hj
  apply member_thompson_not_centralizes T hX hC
  have hh := map_mono (f := H.subtype) hj
  rw [hmap, map_centralizer_subtype] at hh
  exact hh.trans inf_le_right

/-- The fixed denominator in the source tilde-module is the centralizer of
the residual Y, with the original subgroup embedding retained. -/
theorem residual_fixed_map (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G)) :
    (internalModule T (X ⊔ (T : Subgroup G)) ⊓
      centralizer (pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G) : Set ↥(X ⊔ (T : Subgroup G)))).map
        (X ⊔ (T : Subgroup G)).subtype =
      localV T (X ⊔ (T : Subgroup G)) ⊓ centralizer (X : Set G) := by
  rw [map_inf _ _ _ (X ⊔ (T : Subgroup G)).subtype_injective,
    map_centralizer_subtype, member_residual_join T hX]
  change localV T (X ⊔ (T : Subgroup G)) ⊓
    ((X ⊔ (T : Subgroup G)) ⊓ centralizer (X : Set G)) = _
  rw [← inf_assoc, inf_eq_left.mpr (localV_le _ _)]

/-- Characteristic two passes from M to the actual overgroup YT of T. -/
theorem Input.join_characteristic [Finite G] {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    HasCharacteristicTwo (X ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := X ⊔ (T : Subgroup G)
  have hHM : H ≤ M := sup_le h.member_le h.sylow_le
  have hTM : (T.subtype h.sylow_le : Subgroup M) ≤ H.subgroupOf M := by
    rw [T.coe_subtype]
    exact fun _ hx => (show (T : Subgroup G) ≤ H from le_sup_right) hx
  have hchar := centralizer_pCore_le_of_sylow_le (T.subtype h.sylow_le)
    (H.subgroupOf M) hTM (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  exact HasCharacteristicTwo.of_equiv (subgroupOfEquivOfLe hHM) hchar

/-- The SQTK hypothesis is inherited from the genuine maximal two-local. -/
theorem Input.join_sqtk [Finite G] {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    IsSQTK K (X ⊔ (T : Subgroup G) : Subgroup G) := by
  have hHM : X ⊔ (T : Subgroup G) ≤ M := sup_le h.member_le h.sylow_le
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHM)).mp
    ((h.ambient.twoLocal_sqtk h.maximal.1).subgroup _)

/-- This is the generalized Fitting subgroup, with its component layer,
not just the ordinary Fitting subgroup. -/
theorem Input.join_generalizedFitting [Finite G] {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    Theory.GroupTheory.generalizedFitting (X ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G) :=
  LocalSetup.generalizedFitting_eq_twoCore_of_mem_He
    (Chapter1.mem_He_iff.mpr h.join_characteristic)

/-- All local hypotheses needed to invoke the universal E.2.3 theorem on
the genuine internal module. This records hypotheses, not its conclusions. -/
structure E23Application [Finite G] (K : GroupClass) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) : Prop where
  sqtk : IsSQTK K H
  parabolic : ChapterB.IsMinimalParabolicOver (T.subtype hTH) ⊤
  fitting : Theory.GroupTheory.generalizedFitting H = pCore 2 H
  elementary : IsElementaryAbelian 2 (internalModule T H)
  reduced : pCore 2 (H ⧸ centralizer (internalModule T H : Set H)) = ⊥
  thompson : ¬ elementaryAbelianMaxJ (T.subtype hTH : Subgroup H) ≤
    centralizer (internalModule T H : Set H)

/-- The actual application discharges every E.2.3 hypothesis from the
prior15.4.11 inputs and clause (3); no clause (4)--(6) is assumed. -/
theorem Input.e23Application [Finite G] {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    E23Application K T (X ⊔ (T : Subgroup G)) le_sup_right := by
  exact ⟨h.join_sqtk, member_internal_minimalParabolic T h.member h.quotient_elementary,
    h.join_generalizedFitting, internalModule_elementary T _ le_sup_right h.join_characteristic,
    internalModule_reduced T _ le_sup_right h.center_centralizer,
    member_internal_thompson_not_centralizes T h.member h.center_centralizer⟩

private theorem normal_member_quotient_kernel (M : Subgroup G)
    (A : Subgroup M) [A.Normal] :
    ((quotientMap M).subgroupMap A).ker = pCore 2 A := by
  have hk : IsPGroup 2 ((quotientMap M).subgroupMap A).ker := by
    rw [ker_subgroupMap]
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 M)).ker).subgroupOf A)
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hkle : ((quotientMap M).subgroupMap A).ker ≤ pCore 2 A :=
    le_sSup ⟨inferInstance, hk⟩
  apply le_antisymm hkle
  have hc : (pCore 2 A).map A.subtype ≤ pCore 2 M :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map A.subtype⟩
  intro x hx
  change (quotientMap M).subgroupMap A x = 1
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff (N := pCore 2 M) (x := (x : M))).mpr
    (hc ⟨x, hx, rfl⟩)

/-- The intrinsic odd quotient of a relatively normal member is identified
with its image under the original M projection, on every element. This works
for both E_3 and E_9, without choosing any abstract quotient coordinates. -/
theorem member_quotient_compatible {M X : Subgroup G} (hXM : X ≤ M)
    (hn : (X.subgroupOf M).Normal) :
    ∃ e : (X ⧸ pCore 2 X) ≃* image M X,
      ∀ x : X, (e (QuotientGroup.mk' (pCore 2 X) x) : CoreQuotient M) =
        quotientMap M (inclusion hXM x) := by
  let A := X.subgroupOf M
  let : A.Normal := hn
  let eA : X ≃* A := (subgroupOfEquivOfLe hXM).symm
  let f := (quotientMap M).subgroupMap A
  have hk : f.ker = pCore 2 A := normal_member_quotient_kernel M A
  let e : (X ⧸ pCore 2 X) ≃* image M X :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f ((quotientMap M).subgroupMap_surjective A)))
  exact ⟨e, fun _ => rfl⟩

/-- Applying the compatibility theorem to the specified source member keeps
clause (3)'s elementary group and its order in the fixed M quotient. -/
theorem Input.image_structure [Finite G] {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    IsElementaryAbelian 3 (image M X) ∧ Nat.card (image M X) = 3 ^ s := by
  obtain ⟨e, _⟩ := member_quotient_compatible h.member_le h.normal
  let : IsElementaryAbelian 3 (X ⧸ pCore 2 X) := h.quotient_elementary
  exact ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
    (Nat.card_congr e.toEquiv).symm.trans h.quotient_card⟩

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
