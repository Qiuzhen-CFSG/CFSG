module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.CentralModule
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The faithful central FF-module of a binary MS group

Write N = O₂(J) and V = Ω₁Z(N), with V embedded in J by the actual subtype
maps. Simplicity of L/O₂(L), transported through its specified SL₃(2)
isomorphism and the canonical SL₃(2)–PSL₃(2) comparison, shows that C_J(V)
meets L in O₂(L). Its image in Aut(L/O₂(L)) therefore centralizes every inner
automorphism and is trivial. Thus C_J(V) = N, and conjugation descends to a
faithful binary representation of J/N on Additive V.

If the elementary Thompson subgroup J(R) lay in N, maximum elementary orders
would agree and J(R) would equal J(N). Characteristicity in N would make this
nontrivial characteristic subgroup of R normal in J, contradicting (MS3).
A maximum elementary subgroup E of R outside N consequently exists. The
commuting elementary product V C_E(V) and maximality give the offender bound;
the fixed space is identified with the actual subgroup V ∩ C_J(E).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–32,
printed pp.135–136, and the maximum-elementary arguments of B.2, pp.74–76.
This construction supplies the faithful FF-module; the further module
classification and commutator-core bound are separate arguments.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Stellmacher
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

omit [Finite J] in
/-- The two-core centralizes its omega center in the ambient group. -/
theorem twoCore_le_centralModule_centralizer :
    pCore 2 J ≤ centralizer (centralModule J : Set J) := by
  intro n hn v hv
  exact ((mem_centralModule J v).mp hv).2.2 n hn |>.symm

include h

/-- The component centralizer, on the intrinsic carrier L, is exactly O₂(L). -/
theorem Input.component_centralModule_centralizer :
    (centralizer (centralModule J : Set J)).subgroupOf L = pCore 2 L := by
  let := centralModule_normal J
  let C := (centralizer (centralModule J : Set J)).subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  have hNC : pCore 2 L ≤ C := by
    intro n hn
    have hnJ : (n : J) ∈ pCore 2 J := by
      exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hn)).1
    exact twoCore_le_centralModule_centralizer hnJ
  let : IsSimpleGroup (Matrix.PSL3Two.PSL) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (h.quotientEquiv.trans Matrix.PSL3Two.equiv).isSimpleGroup
  have hnorm : (C.map q).Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with hc | hc
  · apply le_antisymm _ hNC
    have := (Subgroup.map_eq_bot_iff C).mp hc
    simpa only [q, QuotientGroup.ker_mk'] using this
  · have hCt : C = ⊤ := by
      have he := congrArg (fun K => K.comap q) hc
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_eq_left.mpr hNC,
        comap_top] using he
    exact (h.component_not_centralizes (subgroupOf_eq_top.mp hCt)).elim

/-- The full ambient centralizer of Ω₁Z(O₂(J)) is exactly O₂(J). -/
theorem Input.centralModule_centralizer :
    centralizer (centralModule J : Set J) = pCore 2 J := by
  let := centralModule_normal J
  let := h.component_normal
  let C := centralizer (centralModule J : Set J)
  have hCL : C ⊓ L ≤ pCore 2 J := by
    intro x hx
    have hxL : (⟨x, hx.2⟩ : L) ∈ pCore 2 L :=
      h.component_centralModule_centralizer ▸ hx.1
    exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hxL)).1
  have hk : ⁅C, L⁆ ≤ h.quotientAction.ker := by
    rw [h.quotientAction_kernel]
    exact (commutator_le_inf C L).trans hCL
  have hi : L.map h.quotientAction = MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    apply le_antisymm
    · rintro a ⟨l, hl, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩,
        (h.quotientAction_component ⟨l, hl⟩).symm⟩
    · rintro a ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
      exact ⟨l, l.property, h.quotientAction_component l⟩
  have hcomm : ⁅C.map h.quotientAction, MulAut.innerSubgroup (L ⧸ pCore 2 L)⁆ = ⊥ := by
    rw [← hi, ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hk
  have hzero : C.map h.quotientAction = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (MulAut.centralizer_innerSubgroup_eq_bot h.quotient_center).le
  have hle := (Subgroup.map_eq_bot_iff C).mp hzero
  rw [h.quotientAction_kernel] at hle
  exact le_antisymm hle twoCore_le_centralModule_centralizer

/-- (MS3) forces the elementary Thompson subgroup of R outside the two-core. -/
theorem Input.thompson_not_le_core :
    ¬ elementaryAbelianMaxJ R ≤ pCore 2 J := by
  intro hle
  have hNR := h.radical.twoCore_le
  have heqOrder : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder (pCore 2 J) :=
    le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hNR).1
  have heqJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 J) :=
    le_antisymm ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).2 heqOrder)
      ((elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hNR).2 heqOrder.symm)
  have hmap (S : Subgroup J) :
      (elementaryAbelianMaxJ (⊤ : Subgroup S)).map S.subtype = elementaryAbelianMaxJ S := by
    rw [← elementaryAbelianMaxJ_map_injective _ S.subtype_injective,
      ← MonoidHom.range_eq_map, S.range_subtype]
  let C : Subgroup R := elementaryAbelianMaxJ ⊤
  let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hn : (C.map R.subtype).Normal := by
    change ((elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype).Normal
    rw [hmap, heqJ, ← hmap (pCore 2 J)]
    let : (elementaryAbelianMaxJ (⊤ : Subgroup (pCore 2 J))).Characteristic :=
      elementaryAbelianMaxJ_top_characteristic
    infer_instance
  have hC : C = ⊥ := h.characteristic.eq_bot_of_normal C hn
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr h.radical_ne_bot
  let D : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  have hD : D ≠ ⊥ := omega_center_ne_bot h.radical.isPGroup
  have hDe : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 (omega₁ (center R) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center R)
    exact IsElementaryAbelian.map (center R).subtype
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup R)
  have hAC : A ≤ C := le_sSup hA
  have hAbot : A = ⊥ := le_bot_iff.mp (hC ▸ hAC)
  have hcard := hA.2.2 D le_top hDe
  rw [hAbot, card_bot] at hcard
  exact hD (eq_bot_of_card_le D hcard)

/-- A maximum elementary subgroup of R acts nontrivially on the central module. -/
theorem Input.exists_maxElementary_not_le_core :
    ∃ E ∈ elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J := by
  classical
  by_contra! hall
  exact h.thompson_not_le_core (sSup_le hall)

attribute [local instance] centralModule_normal centralModule_elementary

private theorem Input.reducedQuotient_kernel :
    (QuotientGroup.mk' (pCore 2 J)).ker = centralizer (centralModule J : Set J) :=
  (QuotientGroup.ker_mk' _).trans h.centralModule_centralizer.symm

/-- Ambient conjugation on V, descended along the actual projection J → J/O₂(J). -/
noncomputable def Input.reducedConjugation : (J ⧸ pCore 2 J) →* MulAut (centralModule J) :=
  Representation.NormalElementaryQuotient.conjugationAut (centralModule J)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) h.reducedQuotient_kernel

/-- A quotient representative acts by its literal conjugation inside J. -/
theorem Input.reducedConjugation_apply (j : J) (v : centralModule J) :
    (h.reducedConjugation (QuotientGroup.mk' (pCore 2 J) j) v : J) = j * (v : J) * j⁻¹ :=
  Representation.NormalElementaryQuotient.conjugationAut_apply _ _ _ _ j v

/-- The binary representation on the additive group of the actual central module. -/
noncomputable def Input.reducedRepresentation :
    Representation (ZMod 2) (J ⧸ pCore 2 J) (Additive (centralModule J)) :=
  Representation.NormalElementaryQuotient.representation (centralModule J)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) h.reducedQuotient_kernel

/-- The linear action retains the ambient conjugation formula. -/
theorem Input.reducedRepresentation_apply (j : J) (v : Additive (centralModule J)) :
    ((h.reducedRepresentation (QuotientGroup.mk' (pCore 2 J) j) v).toMul : J) =
      j * (v.toMul : J) * j⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply _ _ _ _ j v

/-- The linear and multiplicative interfaces describe the same action. -/
theorem Input.reducedRepresentation_eq_conjugation
    (a : J ⧸ pCore 2 J) (v : Additive (centralModule J)) :
    (h.reducedRepresentation a v).toMul = h.reducedConjugation a v.toMul := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) a
  apply Subtype.ext
  exact (h.reducedRepresentation_apply j v).trans
    (h.reducedConjugation_apply j v.toMul).symm

/-- Removing the actual two-core kernel gives a faithful representation. -/
theorem Input.reducedRepresentation_injective : Function.Injective h.reducedRepresentation :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

/-- The descended multiplicative action is faithful as well. -/
theorem Input.reducedConjugation_injective : Function.Injective h.reducedConjugation := by
  intro a b hab
  apply h.reducedRepresentation_injective
  ext v
  apply Additive.toMul.injective
  rw [h.reducedRepresentation_eq_conjugation, h.reducedRepresentation_eq_conjugation, hab]

/-- Fixed vectors of the quotient image of E are precisely the elements centralizing E. -/
theorem Input.mem_reducedFixedSpace (E : Subgroup J) (v : Additive (centralModule J)) :
    v ∈ Representation.BinaryOffender.fixedSpace h.reducedRepresentation
      (E.map (QuotientGroup.mk' (pCore 2 J))) ↔
        (v.toMul : J) ∈ centralizer (E : Set J) :=
  Representation.NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ E v

/-- A carrier equivalence identifies the fixed space with V ∩ C_J(E). -/
noncomputable def Input.reducedFixedSpaceEquiv (E : Subgroup J) :
    Representation.BinaryOffender.fixedSpace h.reducedRepresentation
      (E.map (QuotientGroup.mk' (pCore 2 J))) ≃
        (centralModule J ⊓ centralizer (E : Set J) : Subgroup J) :=
  Representation.NormalElementaryQuotient.fixedSpaceEquiv _ _ _ _ E

/-- A genuine maximum elementary subgroup outside O₂(J) supplies an offender
and the source cardinal inequality on the actual quotient and fixed subgroup. -/
theorem Input.exists_reducedOffender :
    ∃ E ∈ elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J ∧
      Representation.BinaryOffender.IsOffender h.reducedRepresentation
        (E.map (QuotientGroup.mk' (pCore 2 J))) ∧
      Nat.card (centralModule J) ≤ Nat.card (E.map (QuotientGroup.mk' (pCore 2 J))) *
        Nat.card (centralModule J ⊓ centralizer (E : Set J) : Subgroup J) := by
  obtain ⟨E, hE, hEN⟩ := h.exists_maxElementary_not_le_core
  have hVR : centralModule J ≤ R := by
    intro v hv
    exact h.radical.twoCore_le ((mem_centralModule J v).mp hv).1
  refine ⟨E, hE, hEN, ?_, ?_⟩
  · exact Representation.NormalElementaryQuotient.maxElementary_isOffender _ _ _
      h.reducedQuotient_kernel R E hVR hE (by simpa only [QuotientGroup.ker_mk'] using hEN)
  · simpa only [Nat.mul_comm] using maxElementary_card_le_fixed_mul_image R (centralModule J)
      E hVR hE (QuotientGroup.mk' (pCore 2 J)) h.reducedQuotient_kernel

/-- The faithful central representation of J/O₂(J) is an FF-module. -/
theorem Input.reducedRepresentation_isFFModule :
    Representation.BinaryOffender.IsFFModule h.reducedRepresentation := by
  obtain ⟨E, _, _, hE, _⟩ := h.exists_reducedOffender
  exact ⟨E.map (QuotientGroup.mk' (pCore 2 J)), hE⟩

end CFSG.Quasithin.ChapterC.BinaryMS
