module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.SubgroupCenterImageBound
/-!
# Small actions and the two-core of normalized local A₈ sections in J₄

A perfect covering group of A₈ retains its simple quotient in every nontrivial
image. Automorphisms of an elementary abelian two-group of order at most eight
have order at most 168, so every such action is trivial.

For a local linear-four section normalized by a full Sylow subgroup of J₄,
a trivial two-core of the join would make the section itself A₈. The Sylow
order is 2²¹, exceeding the automorphism order 40320, so its action kernel meets
the Sylow center. That center has order two and therefore centralizes the
section. Sylow conjugacy then puts the original local section inside the
literal involution centralizer, contradicting the proved max2 exclusion.
The centralizer obstruction is also exported for the small normal-closure
branch of the same source argument.

Source: Aschbacher–Smith, A.3.12(17), printed pp.47–48, and the normalized
binary-four overcomponent exclusion used in 15.3.32(3). The concrete centralizer
and Sylow orders retain the ATLAS provenance of their imported model proofs.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

private theorem four_equiv_eight {Q : Type*} [Group Q]
    (h : ClassicalGroup.IsPSL Q 4 2) : Nonempty (Q ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 4 eF).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩

private theorem small_aut_card (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E ≤ 8) : Nat.card (MulAut E) ≤ 168 := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 4 ≤ n by omega)
    rw [← hn] at hpow
    norm_num at hpow
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

/-- A perfect binary linear-four covering group has no nontrivial action on
an elementary abelian two-group of order at most eight. -/
theorem small_elementary_action_eq_one {A : Type*} {E : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2)
    (hE : Nat.card E ≤ 8) (f : A →* MulAut E) : f = 1 := by
  obtain ⟨e⟩ := four_equiv_eight hA
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  let q := QuotientGroup.mk' (pCore 2 A)
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 A)).ker
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := A)
    infer_instance
  have hc : Nat.card (A ⧸ pCore 2 A) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  apply Theory.GroupTheory.hom_eq_one_of_no_simple_section q (QuotientGroup.mk'_surjective _) ?_ f
  intro U g hg
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 := U.card_le_card_group
  have h3 := small_aut_card E hE
  omega

/-- The same action conclusion for the actual local C-component; relative
perfectness supplies the covering-group hypothesis. -/
theorem local_small_elementary_action_eq_one {G : Type*} [Group G] [Finite G]
    (A S : Subgroup G) (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 8) (f : A →* MulAut E) : f = 1 := by
  let C := A.subgroupOf (A ⊔ S)
  let : Group.IsPerfect C := hlocal.perfect
  let e : C ≃* A := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact small_elementary_action_eq_one hA hE f

private theorem four_aut_card {A : Type*} [Group A]
    (hA : ClassicalGroup.IsPSL A 4 2) : Nat.card (MulAut A) = 40320 := by
  obtain ⟨e⟩ := four_equiv_eight hA
  let f := MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr f.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]


set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

open Janko4.OuterReduction.OddIndex
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

private noncomputable def max2EquivCentralizer :
    sourceSubgroup ≃* centralizer ({Janko4.a} : Set Janko4.Model) :=
  sourceSubgroupEquivLocal.trans
    (((MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv).trans
      ((MonoidHom.ofInjective centralizerToModel_injective).trans
        (MulEquiv.subgroupCongr centralizerToModel_range)))

private noncomputable def centralizerConjEquiv {G : Type*} [Group G]
    (e : MulAut G) (a : G) : centralizer ({e a} : Set G) ≃* centralizer ({a} : Set G) where
  toFun x := ⟨e.symm x, by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using (mem_centralizer_singleton_iff.mp x.property)⟩
  invFun x := ⟨e x, by
    rw [mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (e.apply_symm_apply x)
  right_inv x := Subtype.ext (e.symm_apply_apply x)
  map_mul' x y := Subtype.ext (e.symm.map_mul x y)

/-- A source local linear-four component cannot centralize the full center
of an ambient Sylow two-subgroup of J₄. -/
theorem not_center_sylow_le_centralizer (A : Subgroup Janko4.Model)
    (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S) :
    ¬ (center S).map S.toSubgroup.subtype ≤ centralizer (A : Set Janko4.Model) := by
  classical
  intro hc
  let P : Sylow 2 (centralizer ({Janko4.a} : Set Janko4.Model)) := default
  obtain ⟨T, hT⟩ := centralizer_sylow_is_ambient P
  have hz : Janko4.a ∈ (center T).map T.toSubgroup.subtype := by
    rw [hT, centralizer_sylow_center]
    exact mem_zpowers _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Janko4.Model T S
  let e := MulAut.conj g
  have hmap : T.toSubgroup.map e.toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  have hea : e Janko4.a ∈ (center S).map S.toSubgroup.subtype := by
    have hh := map_subgroup_center_le e.toMonoidHom T.toSubgroup
      (mem_map_of_mem e.toMonoidHom hz)
    rwa [hmap] at hh
  let M := centralizer ({e Janko4.a} : Set Janko4.Model)
  have hAM : A ≤ M := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hc hea x hx)
  have hSM : S.toSubgroup ≤ M := by
    obtain ⟨z, hz, hez⟩ := hea
    intro x hx
    rw [mem_centralizer_singleton_iff]
    rw [← hez]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)
  let f : M ≃* sourceSubgroup := (centralizerConjEquiv e Janko4.a).trans max2EquivCentralizer.symm
  obtain ⟨B, R, hB, hR⟩ := exists_local_four_in_model A M S hA hlocal hAM hSM f
  exact max2LocalExclusion B R hB hR

/-- Normalization by the full Sylow forces a nontrivial two-core in the
actual join. -/
theorem normalized_join_twoCore_ne_bot (A : Subgroup Janko4.Model)
    (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    (hn : S.toSubgroup ≤ normalizer (A : Set Janko4.Model)) :
    pCore 2 ↥(A ⊔ S.toSubgroup) ≠ ⊥ := by
  intro hbot
  let B := A ⊔ S.toSubgroup
  let C := A.subgroupOf B
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hC : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : C.Normal).isSubnormal, hbot,
      MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective
  let eC : C ≃* A := subgroupOfEquivOfLe le_sup_left
  have hcore : pCore 2 A = ⊥ := by
    rw [← pCore_map_iso 2 eC, hC, Subgroup.map_bot]
  have hA' : ClassicalGroup.IsPSL A 4 2 := by
    change ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2 at hA
    exact hA.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm
  let f : S →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hker : f.ker ≠ ⊥ := by
    intro he
    have hcard := Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp he)
    rw [ambient_sylow_card S, four_aut_card hA'] at hcard
    norm_num at hcard
  have hmeet := center_inf_ne_bot_of_normal S.isPGroup' f.ker hker
  have hZ : center S ≤ f.ker := by
    have hc : Nat.card ↥(center S ⊓ f.ker) = 2 := by
      have hd := card_dvd_of_le (show center S ⊓ f.ker ≤ center S from inf_le_left)
      rw [Janko4.sylow_center_card_two S] at hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
      · exact (hmeet ((eq_bot_iff_card _).mpr hh)).elim
      · exact hh
    have he : center S ⊓ f.ker = center S :=
      eq_of_le_of_card_ge inf_le_left (by rw [hc, Janko4.sylow_center_card_two S])
    exact he ▸ inf_le_right
  apply not_center_sylow_le_centralizer A S hA hlocal
  rintro x ⟨z, hz, rfl⟩
  have hzker : (Subgroup.inclusion hn z) ∈ A.normalizerMonoidHom.ker := hZ hz
  rw [normalizerMonoidHom_ker] at hzker
  exact hzker

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
