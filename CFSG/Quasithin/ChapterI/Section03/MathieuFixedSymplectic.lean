module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedRemainingModels
public import Theory.SpecificGroups.SymplecticFour.FixedComponents
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# No involution-fixed M₂₂ cover in binary symplectic four-space

The complete involution normal forms give three cases. An inner fixed group
lies in a parabolic: perfectness kills its determinant character, and the
SL₂ quotient has cyclic Sylow three-subgroups, excluding an M₂₂ section.
The solvable kernel then excludes the full quasisimple cover. A field fixed
component is the simple derived group over the half field; its order at the
binary endpoint and its two-rank otherwise exclude M₂₂. A graph fixed group
is Suzuki and has order prime to three.

The Theorem B comparison combines this with the existing linear and small
endpoint exclusions. Its actual consumer is the original cubic residual in
MathieuGeneration.HallFaithfulness.RefinedAmbientModels; no central cover,
quotient map or source-module premise is replaced.
Source: Aschbacher--Smith 4.2.13, printed p.612, Theorem B, p.33, and the
symplectic involution rows 16.1.4, pp.1170--1171. The model proofs and their
source references are retained in the imported symplectic modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu Theory.SpecificGroups.SymplecticFour
open InvolutionTypes InvolutionCentralizers DiagramAutomorphisms
open DiagramAutomorphisms.FieldFixedResidual

private theorem no_sl2_section {F : Type*} [Field F] [Finite F] [CharP F 2]
    (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (f : U →* M22) (hf : Function.Surjective f) : False := by
  let P : Sylow 3 U := Sylow.nonempty.some
  let : IsCyclic P := Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide)
    (U.subtype.comp (P : Subgroup U).subtype)
    (U.subtype_injective.comp (P : Subgroup U).subtype_injective)
  let Q := P.mapSurjective hf
  let : IsCyclic Q := isCyclic_of_surjective (f.subgroupMap (P : Subgroup U))
    (f.subgroupMap_surjective _)
  have hr := Q.primeRank_le_one_of_isCyclic inferInstance
  rw [m22_primeRank_three] at hr
  omega

private theorem cover_sl2_hom_eq_one {F B : Type*}
    [Field F] [Finite F] [CharP F 2] [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22) (f : B →* Matrix.SpecialLinearGroup (Fin 2) F) :
    f = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hk : q.ker = center B :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsSolvable q.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  exact hom_eq_one_of_no_simple_section q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) no_sl2_section f

private theorem no_local_cover {F B Q : Type*}
    [Field F] [Finite F] [CharP F 2] [Group B] [Finite B] [IsQuasisimple B]
    [Group Q]
    (e : (B ⧸ center B) ≃* M22)
    (p : Q →* Matrix.SpecialLinearGroup (Fin 2) F) [Group.IsSolvable p.ker]
    (f : B →* Q) (hf : Function.Injective f) : False := by
  have hh := cover_sl2_hom_eq_one e (p.comp f)
  let j := f.codRestrict p.ker (fun b => DFunLike.congr_fun hh b)
  have hj : Function.Injective j := fun x y he => hf (congrArg Subtype.val he)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective hj
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isSolvable B inferInstance

private def lift_to_local {F B : Type*} [Field F] [Group B] [Group.IsPerfect B]
    (W : Submodule F (Vector F)) (f : B →* stabilizer W) : B →* determinantKernel W where
  toFun x := ⟨(f x).val, ⟨f x,
    Abelianization.commutator_subset_ker ((determinantCharacter W).comp f)
      Group.IsPerfect.mem_commutator,rfl⟩⟩
  map_one' := Subtype.ext (congrArg (fun z : stabilizer W => (z : Sp F)) f.map_one)
  map_mul' x y := Subtype.ext (congrArg (fun z : stabilizer W => (z : Sp F)) (f.map_mul x y))

private theorem lift_to_local_injective {F B : Type*} [Field F] [Group B] [Group.IsPerfect B]
    (W : Submodule F (Vector F)) (f : B →* stabilizer W) (hf : Function.Injective f) :
    Function.Injective (lift_to_local W f) := by
  intro x y h
  exact hf (Subtype.ext (congrArg (fun z : determinantKernel W => (z : Sp F)) h))

private theorem no_parabolic_cover {F B : Type*}
    [Field F] [Finite F] [CharP F 2] [Group B] [Finite B] [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22)
    (P : Subgroup (Sp F)) (hP : IsParabolic P) (f : B →* P) (hf : Function.Injective f) : False := by
  obtain ⟨g,hp | hp⟩ := hP
  · let d : P ≃* pointParabolic (F := F) :=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap pointParabolic).symm
    let j := d.toMonoidHom.comp f
    let : IsElementaryAbelian 2 (pointQuotient (F := F)).ker := pointRadical_elementaryAbelian
    exact no_local_cover e pointQuotient (lift_to_local (point F) j)
      (lift_to_local_injective _ j (d.injective.comp hf))
  · let d : P ≃* planeParabolic (F := F) :=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap planeParabolic).symm
    let j := d.toMonoidHom.comp f
    let : IsElementaryAbelian 2 (Plane.quotientMap (F := F)).ker := Plane.radical_elementaryAbelian
    exact no_local_cover e Plane.quotientMap (lift_to_local (plane F) j)
      (lift_to_local_injective _ j (d.injective.comp hf))

private theorem map_component_fixed {F : Type*} [Field F]
    (e : MulAut (Sp F)) (a b : MulAut (Sp F)) (he : MulAut.congr e a = b)
    (B : Subgroup (Sp F)) (hB : IsComponentIn B a.fixedSubgroup) :
    IsComponentIn (B.map e.toMonoidHom) b.fixedSubgroup := by
  have hfix : a.fixedSubgroup.map e.toMonoidHom = b.fixedSubgroup := by
    ext x
    rw [mem_map_equiv,MulAut.mem_fixedSubgroup,MulAut.mem_fixedSubgroup]
    rw [←e.injective.eq_iff]
    have hx := congrArg (fun d : MulAut (Sp F) => d x) he
    change e (a (e.symm x)) = b x at hx
    rw [hx,e.apply_symm_apply]
  exact hfix ▸ hB.map e

private theorem conj_marking {F : Type*} [Field F]
    (a b : MulAut (Sp F)) (h : IsConj a b) : ∃ e : MulAut (Sp F), MulAut.congr e a = b := by
  obtain ⟨e,he⟩ := isConj_iff.mp h
  refine ⟨e,?_⟩
  apply MulEquiv.ext
  intro x
  exact congrArg (fun d : MulAut (Sp F) => d x) he

private def central_quotient_equiv {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private def simple_cover_equiv {B : Type*} [Group B] [IsSimpleGroup B] [Group.IsPerfect B]
    (e : (B ⧸ center B) ≃* M22) : B ≃* M22 :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_perfect (G := B))).trans
    QuotientGroup.quotientBot).symm.trans e

private theorem no_field_component {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m))
    (B : Subgroup (Sp F)) (hB : IsComponentIn B (representative (F := F) m).fixedSubgroup)
    (eB : (B ⧸ center B) ≃* M22) : False := by
  have hb := FieldComponent.component_eq_embedded hm hF B hB
  let K := halfField (F := F) m
  have hK : Nat.card K = 2 ^ m := card_halfField hm hF
  let ed : commutator (Sp K) ≃* B :=
    ((commutator (Sp K)).equivMapOfInjective (coefficientInclusion K)
      (coefficientInclusion_injective K)).trans (MulEquiv.subgroupCongr hb.symm)
  let : IsSimpleGroup (commutator (Sp K)) := FieldComponent.derived_isSimple hm hK
  let : IsSimpleGroup B := ed.symm.isSimpleGroup
  let := hB.quasisimple
  let em : commutator (Sp K) ≃* M22 := ed.trans (simple_cover_equiv eB)
  by_cases hm1 : m = 1
  · have hK2 : Nat.card K = 2 := by simpa only [hm1,pow_one] using hK
    have hc := Nat.card_congr ((Binary.derivedEquivAlternatingSix hK2).symm.trans em).toEquiv
    rw [nat_card_alternatingGroup,m22_order] at hc
    norm_num [Nat.factorial] at hc
  · have hr := EvenTwoRank.derived_rank hK (by omega : 2 ≤ m)
    rw [primeRank_equiv 2 em] at hr
    have hu := m22_twoRank_le_four
    omega

private theorem no_sp_fixed {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ¬ HasMathieuFixedComponent (Sp F) := by
  rintro ⟨a,ha,B,hB,⟨b⟩⟩
  let := hB.quasisimple
  rcases InvolutionNormalForms.involution_normalForms hF hn a ha with
    ⟨g,hg,he⟩ | ⟨heven,hconj⟩ | ⟨hodd,hconj⟩
  · obtain ⟨P,hP,_,_,hc⟩ := involution_centralizer_parabolic g hg
    have hle : B ≤ P := hB.1.trans (by rw [he,MulAut.fixedSubgroup_conj]; exact hc)
    exact no_parabolic_cover b P hP (inclusion hle) (inclusion_injective hle)
  · obtain ⟨e,he⟩ := conj_marking a _ hconj
    have hmul : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
    have hm : 1 ≤ n / 2 := by omega
    have hcard : Nat.card F = 2 ^ (2 * (n / 2)) := by rw [hmul]; exact hF
    have hb := map_component_fixed e a _ he B hB
    exact no_field_component hm hcard _ hb ((central_quotient_equiv (e.subgroupMap B)).symm.trans b)
  · obtain ⟨m,hm⟩ := hodd
    have hnm : n = 2 * m + 1 := hm
    have hmpos : 0 < m := by omega
    obtain ⟨e,he⟩ := conj_marking a _ hconj
    let B' := B.map e.toMonoidHom
    have hb : IsComponentIn B' (GraphFieldFixedResidual.graphFieldAut (F := F) m).fixedSubgroup := by
      have hh := map_component_fixed e a _ he B hB
      change IsComponentIn B' (ExceptionalGraph.graphAut ^ (2 * m + 1)).fixedSubgroup
      rw [hnm] at hh
      exact hh
    let d := GraphFieldFixedResidual.fixedEquivOfBinaryModel m (hnm ▸ hF)
      (GraphFieldFixedResidual.fixedSuzukiEquiv m)
    have hd : Nat.card M22 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
      rw [← Nat.card_congr b.toEquiv]
      exact (card_quotient_dvd_card _).trans
        ((Nat.card_congr (e.subgroupMap B).toEquiv).dvd.trans
          ((card_dvd_of_le hb.1).trans (Nat.card_congr d.toEquiv).dvd))
    have h3 : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (by rw [m22_order]; decide : 3 ∣ Nat.card M22).trans hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hmpos h3

/-- No binary symplectic-four involution fixes a component covering M₂₂. -/
theorem HasMathieuFixedComponent.not_binary_symplectic
    {S : Type*} [Group S] (h : HasMathieuFixedComponent S)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp S 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact no_sp_fixed hn hF (h.of_mulEquiv (e.trans EvenProjective.equiv.symm))

open ChapterA.Section02 ClassificationModels

/-- The binary unitary and exceptional rows after excluding PSp₄. -/
@[expose] def RemainingMathieuUnitaryExceptionalModel (S : Type*) [Group S] : Prop :=
  (∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSU S 4 (2 ^ n)) ∨
  ClassicalGroup.IsPSU S 5 4 ∨
  (∃ n, 2 ≤ n ∧ IsG2At S (2 ^ n)) ∨
  (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (S ≃* ReeF4.Model m))

/-- The remaining full-cover fixed-component models: odd Lie families,
binary unitary or exceptional families, and McL. -/
@[expose] def RemainingMathieuFixedModel (S : Type*) [Group S] : Prop :=
  RemainingMathieuLargeOddModel S ∨ RemainingMathieuUnitaryExceptionalModel S ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Apply the full binary symplectic exclusion to the existing Theorem B
comparison, preserving all field parameters and model isomorphisms. -/
theorem HasMathieuFixedComponent.fixed_model_rows
    {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuFixedModel S := by
  rcases h.remaining_rows hm with ho | hr | hmcl
  · exact Or.inl ho
  · rcases hr with hu4 | hu5 | ⟨n,hn,hsp⟩ | hg | ht | hr
    · exact Or.inr (Or.inl (Or.inl hu4))
    · exact Or.inr (Or.inl (Or.inr (Or.inl hu5)))
    · exact (h.not_binary_symplectic hn hsp).elim
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hg))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
  · exact Or.inr (Or.inr hmcl)

end CFSG.Quasithin.ChapterI.MathieuPumpup
