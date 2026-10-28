module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFourAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryExceptionalSix
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixThompson
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.TripleSixFixed
public import Theory.Representation.SpecialLinearRestriction
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups.CentralCover

/-!
# Excluding the triple-six star component on the doubled orbit

Compare the complete B.5 catalogue with the actual star group of order
1080. Only the faithful three-dimensional F₄ action remains. Ratio one
puts the original Thompson image in the component, so its cubic center
lies in the marked intersection by the original normalizer control.

The original moving residual has noncentral star image: centrality would
pass through the two-core quotient to the original reduced action and
contradict its Sylow commutator. A proper Sylow overgroup in A₆ has order
eight or twenty-four. The former makes this two-perfect residual central;
the latter, with the retained cubic center, makes the marked intersection's
order divisible by nine. Its literal paired-plane action maps to S₃, so
the kernel contains a cubic element. The actual residual sixteen embeds
in the B.5 central quotient and is fixed by this cubic. Perfectness gives
determinant one on F₄³, where a nonidentity odd actor fixes at most four
vectors, a contradiction.

The Chapter12 companion discharges every premise on the original selected
orbit, both full quotient maps and its original Sylow. No whole-component
block recognition or vanishing cubic center is assumed.
Source: Aschbacher--Smith, the elimination after 7.7.10, printed p.709,
C.2.7(3)(c), pp.145--147, B.4.2(8)/B.5.1, pp.86,99--103, and K.1.3,
p.453, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTripleSix
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine ChapterC.C27Source

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem two_power_bound {k : ℕ} (h : 2 ^ k ∣ 1080) : k ≤ 3 := by
  by_contra hk
  have hd : 16 ∣ 1080 := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans h
  norm_num at hd

private theorem no_linearTwo {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = 1080 := (Nat.card_congr e.toEquiv).symm.trans hE
  rw [GorensteinWalter.sl2_card_formula,F.card_eq] at hc
  have hd : F.degree ≤ 3 := two_power_bound (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  interval_cases he : F.degree <;> norm_num [he] at hc

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq,h]
    simp)

private theorem no_linearThree {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 1080 := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hh := Nat.card_congr (Atlas.fieldEquivSL 3 (fieldTwoEquiv F he)).toEquiv
  rw [hc,binary_card] at hh
  norm_num [Fin.prod_univ_succ] at hh

private theorem no_symplectic {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_g2 {E : Type*} [Group E] (hE : Nat.card E = 1080)
    (F : BinaryField) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_binaryLinear {E : Type*} [Group E] (hE : Nat.card E = 1080)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;>
    norm_num [Fin.prod_univ_succ] at hc

private theorem no_other_alternating {E : Type*} [Group E] (hE : Nat.card E = 1080)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hn with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hc <;> norm_num [Nat.factorial] at hc


universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

private theorem irreducible_tripleSix
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (hc : Nat.card C = 1080) :
    J = C ∧ Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ C) ∧
      quadraticRatio ρ = 1 := by
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F _ _ a _ => exact (no_symplectic hc F a.groupEquiv).elim
  | symplecticTwo a _ =>
    exact (no_other_alternating hc (Or.inr (Or.inl rfl))
      (ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv a).groupEquiv).elim
  | g2 F _ _ a _ _ => exact (no_g2 hc F a.groupEquiv).elim
  | g2Two a _ _ =>
    have hh := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
    norm_num at hh
  | symmetric n hn a _ _ =>
    exact (no_other_alternating hc (hn.imp_right (fun hh => Or.inr (Or.inl hh))) a.subgroupEquiv).elim
  | alternatingSix _ a _ _ =>
    exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ a _ _ _ =>
    exact (no_other_alternating hc (Or.inr (Or.inr (Or.inl rfl))) a).elim
  | tripleSix hg a hr => exact ⟨hg,⟨a⟩,hr⟩
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ =>
    exact (no_other_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.groupEquiv).elim
  | symmetricEight _ a _ =>
    exact (no_other_alternating hc (Or.inr (Or.inr (Or.inr rfl))) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

/-- The full source catalogue retains the actual faithful triple-six action. -/
theorem source_tripleSix
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : Nat.card C = 1080) :
    Function.Injective c.sectionData.action ∧
      offenderSubgroup c.sectionData.action = C ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction c.sectionData.action C) ∧
      quadraticRatio c.sectionData.action = 1 := by
  cases c.clause_one with
  | irreducible _ hf _ hs _ => exact ⟨hf,irreducible_tripleSix _ hs hc⟩
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn => exact (no_binaryLinear hc hd hn.some.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn => exact (no_binaryLinear hc hd hn.some.groupEquiv).elim


/-- An odd actor in the faithful triple-six section fixes at most four vectors. -/
theorem tripleSix_odd_fixed_card [Group.IsPerfect C]
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ C)
    (hf : Function.Injective (ρ.comp C.subtype)) (x : C)
    (hx : Odd (orderOf x)) (hne : x ≠ 1)
    {X : Type*} [Finite X] (j : X → V) (hj : Function.Injective j)
    (hfix : ∀ v, ρ x (j v) = j v) : Nat.card X ≤ 4 := by
  let op (g : C) : Module.End BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier) :=
    { toFun := fun w => a.coordinates (ρ g (a.coordinates.symm w))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro b w
        simpa only [LinearEquiv.apply_symm_apply,RingHom.id_apply] using
          a.scalar_linear g b (a.coordinates.symm w) }
  let τ : Representation BinaryField.four.Carrier C (Fin 3 → BinaryField.four.Carrier) :=
    { toFun := op
      map_one' := by
        apply LinearMap.ext
        intro w
        change a.coordinates (ρ (1 : D) (a.coordinates.symm w)) = w
        rw [map_one,Module.End.one_apply,LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro w
        change a.coordinates (ρ ((g*h : C) : D) (a.coordinates.symm w)) =
          a.coordinates (ρ g (a.coordinates.symm (a.coordinates (ρ h (a.coordinates.symm w)))))
        rw [Subgroup.coe_mul,map_mul,Module.End.mul_apply,LinearEquiv.symm_apply_apply] }
  have hτ : Function.Injective τ := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    change ρ (g : D) v = ρ (h : D) v
    apply a.coordinates.injective
    have hh := LinearMap.congr_fun he (a.coordinates v)
    change a.coordinates (ρ g (a.coordinates.symm (a.coordinates v))) =
      a.coordinates (ρ h (a.coordinates.symm (a.coordinates v))) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  obtain ⟨f,e,hf',he⟩ := exists_specialLinear_restriction τ hτ
    (det_eq_one_of_perfect τ) (d := 3) (by simp)
  let i : X → {w : Fin 3 → BinaryField.four.Carrier // (f x).toLin' w = w} :=
    fun v => ⟨e (a.coordinates (j v)),by
      have hh := he x (a.coordinates (j v))
      have ha : τ x (a.coordinates (j v)) = a.coordinates (j v) := by
        change a.coordinates (ρ x (a.coordinates.symm (a.coordinates (j v)))) = _
        rw [LinearEquiv.symm_apply_apply,hfix]
      rw [ha] at hh
      exact hh.symm⟩
  have hi : Function.Injective i := fun v w hh =>
    hj (a.coordinates.injective (e.injective (congrArg Subtype.val hh)))
  exact (Nat.card_le_card_of_injective i hi).trans
    (DoubledBinaryExceptionalSix.odd_linear_fixed_card (by rw [BinaryField.four.card_eq]; rfl) (f x)
      (by rwa [orderOf_injective f hf']) (fun hh => hne (hf' (hh.trans f.map_one.symm))))

section Star
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

/-- The cubic center is retained in the original marked intersection. -/
theorem star_center_le_intersection
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (hCJ : starImage K Q K ≤ offenderSubgroup (starRepresentation K Q))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp (offenderSubgroup (starRepresentation K Q)).subtype)
      ((starImage K Q K).subgroupOf (offenderSubgroup (starRepresentation K Q))))
    (hc : Nat.card (starImage K Q K) = 1080) :
    center (starImage K Q K) ≤ (starM K Q M).subgroupOf (starImage K Q K) := by
  have hc' : Nat.card ((starImage K Q K).subgroupOf
      (offenderSubgroup (starRepresentation K Q))) = 1080 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv,hc]
  obtain ⟨_,hgen,_,hr⟩ := source_tripleSix _ c hc'
  have hJ := ratio_one_component_eq_offender h hCJ c.sectionData hgen hr
  have hinner := (star_thompson_le_offenderSubgroup_from_source h).trans hJ.le
  intro x hx
  apply (star_thompson_intersection_from_source h).1
  refine ⟨x.property,Subgroup.centralizer_le_normalizer _ ?_⟩
  intro j hj
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨j,hinner hj⟩)

/-- The original S₃ action forbids a cubic in its kernel on the triple-six row. -/
theorem kernel_prime_to_three
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 16) (hker : (toStarImage K Q).ker = pCore 2 K)
    (hc : Nat.card (starImage K Q K) = 1080)
    (π : M.subgroupOf K →* Equiv.Perm (Fin 3))
    (hk : ∀ x : π.ker, (x.val.val : G) ∈ centralizer (X : Set G)) :
    ¬ 3 ∣ Nat.card π.ker := by
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  let J := offenderSubgroup (starRepresentation K Q)
  let C := (starImage K Q K).subgroupOf J
  have hc' : Nat.card C = 1080 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv,hc]
  obtain ⟨hf,_,⟨a⟩,_⟩ := source_tripleSix _ c hc'
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hqs := (star_fitting_quasisimple (source_join_input h)).2
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCJ).symm
  let : Group.IsPerfect C := inferInstance
  obtain ⟨j,hj,hfix⟩ := DoubledBinaryStarSix.star_section_embedding W A X hWX hAK hX hdis hCJ c.sectionData
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 3 hd
  let k : K := x.val.val
  let y : C := (subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)
  have hy : orderOf y = 3 := by
    change orderOf ((subgroupOfEquivOfLe hCJ).symm.toMonoidHom (toStarImage K Q k)) = 3
    rw [orderOf_injective (subgroupOfEquivOfLe hCJ).symm.toMonoidHom
      (subgroupOfEquivOfLe hCJ).symm.injective]
    rw [(toStarImage K Q).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (hker ▸ pCore_isPGroup) k]
    · simpa only [k,Subgroup.orderOf_coe] using hx
    · simpa only [k,Subgroup.orderOf_coe,hx] using (by decide : Nat.Coprime 2 3)
  have hb := tripleSix_odd_fixed_card _ a (hf.comp Subtype.val_injective) y
    (by rw [hy]; decide) (by intro hh; rw [hh,orderOf_one] at hy; omega)
    j hj (hfix k (hk x))
  rw [Nat.card_congr Additive.toMul,hcard] at hb
  omega
end Star

private theorem nine_dvd_marked
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (hz : Nat.card (center E) = 3) (e : (E ⧸ center E) ≃* alternatingGroup (Fin 6))
    (B : Subgroup E) (S : Sylow 2 E) (hSB : (S : Subgroup E) ≤ B)
    (hB : B ≠ ⊤) (hZB : center E ≤ B)
    (A : Subgroup E) (hA : IsPPerfect 2 A) (hAB : A ≤ B)
    (hnot : ¬ A ≤ center E) : 9 ∣ Nat.card B := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Y := B.map q
  let P := S.mapSurjective hq
  have hPY : (P : Subgroup (alternatingGroup (Fin 6))) ≤ Y := map_mono hSB
  have hY : Y ≠ ⊤ := by
    intro ht
    apply hB
    apply top_unique
    apply perfect_le_of_map_le_of_central_kernel q hk.le (⊤ : Subgroup E) B
    change _ ≤ Y
    rw [ht]
    exact le_top
  rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour P Y hPY hY with h8 | h24
  · have hp : IsPGroup 2 Y := IsPGroup.of_card (n := 3) h8
    let r : A →* Y := (q.comp A.subtype).codRestrict Y
      (fun a => mem_map_of_mem q (hAB a.property))
    have hr := hA.hom_eq_one_of_isPGroup hp r
    apply (hnot ?_).elim
    intro a ha
    have he := congrArg Subtype.val (DFunLike.congr_fun hr (⟨a,ha⟩ : A))
    change q a = 1 at he
    exact hk ▸ he
  · let r := q.subgroupMap B
    have hkr : Nat.card r.ker = 3 := by
      rw [ker_subgroupMap,hk,Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv,hz]
    have h := r.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective B),card_top,hkr,h24] at h
    rw [←h]
    decide

section Star
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

omit [Finite G] in
/-- The original reduced action detects a noncentral residual in the star group.
The two quotient maps retain their full kernels. -/
theorem residual_not_central_in_star
    (h : Input KnownSimple.IsKnownSimple H Q M K) [(K.subgroupOf H).Normal]
    (hker : (toStarImage K Q).ker = pCore 2 K)
    {E : Type*} [Group E] (q : H →* E) (hq : Function.Surjective q)
    (hz : pCore 2 E = ⊥) (A : Subgroup G) (hAK : A ≤ K) (B : Subgroup E)
    (hmove : ¬ ⁅(A.subgroupOf H).map q,B ⊓ (K.subgroupOf H).map q⁆ ≤
      ((A.subgroupOf H).map q).pCoreIn 2) :
    ¬ (A.subgroupOf K).map (toStarImage K Q) ≤ center (starImage K Q K) := by
  intro hc
  let r : K →* E := q.comp (inclusion h.component.1)
  have hk : (toStarImage K Q).ker ≤ r.ker := by
    rw [hker]
    let e := (subgroupOfEquivOfLe h.component.1).symm
    have hn : ((pCore 2 (K.subgroupOf H)).map (K.subgroupOf H).subtype).Normal := inferInstance
    have hl : ((pCore 2 (K.subgroupOf H)).map (K.subgroupOf H).subtype).map q ≤ pCore 2 E :=
      le_sSup ⟨hn.map q hq,(pCore_isPGroup.map _).map q⟩
    rw [hz,map_map] at hl
    have hkill := (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hl)
    intro k hk
    have he : e k ∈ pCore 2 (K.subgroupOf H) := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hk
    exact hkill he
  let f := (toStarImage K Q).liftOfSurjective (toStarImage_surjective K Q) ⟨r,hk⟩
  have hf (k : K) : f (toStarImage K Q k) = r k := by simp [f]
  have hcentral : (A.subgroupOf H).map q ≤ centralizer ((K.subgroupOf H).map q : Set E) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨k,hk,rfl⟩
    let a' : K := ⟨a,hAK ha⟩
    let k' : K := ⟨k,hk⟩
    have hh := congrArg f (mem_center_iff.mp (hc (mem_map_of_mem (toStarImage K Q) (show a' ∈ A.subgroupOf K from ha)))
      (toStarImage K Q k'))
    change f (toStarImage K Q k' * toStarImage K Q a') =
      f (toStarImage K Q a' * toStarImage K Q k') at hh
    have hka : inclusion h.component.1 k' = k := by
      apply Subtype.ext
      exact coe_inclusion _ _
    have haa : inclusion h.component.1 a' = a := by
      apply Subtype.ext
      exact coe_inclusion _ _
    simpa only [map_mul,hf,r,MonoidHom.comp_apply,hka,haa] using hh
  apply hmove
  have he := commutator_eq_bot_iff_le_centralizer.mpr hcentral
  exact (commutator_mono le_rfl inf_le_right).trans (he.le.trans bot_le)

/-- The surviving triple-six group is impossible on the original paired orbit.
Its cubic center forces a factor nine in the marked intersection, while the
literal orbit action has image in S₃ and a kernel prime to three. -/
theorem no_tripleSix_star
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hAM : A ≤ M) (hp : IsPPerfect 2 A)
    (hX : X = ⁅W,A⁆) (hdis : Disjoint X (centralizer (A : Set G)))
    [IsElementaryAbelian 2 X] (hcard : Nat.card X = 16)
    (hker : (toStarImage K Q).ker = pCore 2 K)
    (S : Sylow 2 K) (hSM : (S : Subgroup K).map K.subtype ≤ M)
    (hnot : ¬ (A.subgroupOf K).map (toStarImage K Q) ≤ center (starImage K Q K))
    (π : M.subgroupOf K →* Equiv.Perm (Fin 3))
    (hk : ∀ x : π.ker, (x.val.val : G) ∈ centralizer (X : Set G))
    (ce : center (starImage K Q K) ≃* Multiplicative (ZMod 3))
    (qe : (starImage K Q K ⧸ center (starImage K Q K)) ≃* alternatingGroup (Fin 6)) : False := by
  have hc : Nat.card (starImage K Q K) = 1080 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (starImage K Q K)),
      Nat.card_congr qe.toEquiv,Nat.card_congr ce.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hthree := kernel_prime_to_three h W A X hWX hAK hX hdis hcard hker hc π hk
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  have hz := star_center_le_intersection h hCJ c hc
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let : IsQuasisimple (starImage K Q K) := (star_fitting_quasisimple (source_join_input h)).2
  let B := (M.subgroupOf K).map (toStarImage K Q)
  let P := S.mapSurjective (toStarImage_surjective K Q)
  have hPB : (P : Subgroup (starImage K Q K)) ≤ B := by
    apply map_mono
    intro k hk
    exact hSM (mem_map_of_mem K.subtype hk)
  have hB : B ≠ ⊤ := by
    intro ht
    have he := congrArg (map (starImage K Q K).subtype) ht
    dsimp only [B] at he
    rw [DoubledBinaryStarIntersection.intersection_star_map,
      map_subgroupOf_eq_of_le (starM_le K Q M),←MonoidHom.range_eq_map,range_subtype] at he
    exact (star_thompson_intersection_from_source h).2.ne he
  have hA : IsPPerfect 2 ((A.subgroupOf K).map (toStarImage K Q)) := by
    have hA' := hp.of_surjective (subgroupOfEquivOfLe hAK).symm.toMonoidHom
      (subgroupOfEquivOfLe hAK).symm.surjective
    exact hA'.of_surjective ((toStarImage K Q).subgroupMap _) ((toStarImage K Q).subgroupMap_surjective _)
  have h9 : 9 ∣ Nat.card B := nine_dvd_marked
    (by rw [Nat.card_congr ce.toEquiv]; simp) qe B P hPB hB
    (by simpa only [B,DoubledBinaryStarIntersection.intersection_star_map] using hz)
    ((A.subgroupOf K).map (toStarImage K Q)) hA
    (map_mono (comap_mono hAM)) hnot
  have hd : 9 ∣ Nat.card (M.subgroupOf K) := h9.trans (card_map_dvd _ _)
  rw [←π.ker.card_mul_index,index_ker] at hd
  have hcop : Nat.Coprime 9 (Nat.card π.ker) :=
    (Nat.prime_three.coprime_pow_of_not_dvd (m := 2) hthree).symm
  have h9r := hcop.dvd_of_dvd_mul_left hd
  have h6 := π.range.card_subgroup_dvd_card
  rw [Nat.card_perm,Nat.card_fin] at h6
  have hh := h9r.trans h6
  norm_num [Nat.factorial] at hh
end Star


/-- The surviving full quotient and its actual two-copy moved action, on one
fixed B.5 section. This packages the conclusion without expanding its nested
quotient actions in the chosen-module statement. -/
@[expose] def BinaryThreeConclusion
    {G : Type*} [Group G] {K Q : Subgroup G} {J : Subgroup (StarQuotient K Q)}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp J.subtype) ((starImage K Q K).subgroupOf J)) : Prop :=
  Nonempty (starImage K Q K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    (starImage K Q K).subgroupOf J = ⊤ ∧
    ∃ F : BinaryField, F.degree = 1 ∧
      IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) F 3 2

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTripleSix
