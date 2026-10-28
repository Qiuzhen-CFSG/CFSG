module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.SylowSource.Coordinates
public import Theory.SpecificGroups.PSL3Four.SylowCosetRecognition

/-!
# The intrinsic Sylow calculations in the original projective marking

The component factor maps onto the full marked Borel, and its two-core maps
onto the marked Sylow subgroup. Transporting the two actual cubic-factor signs
through these maps identifies graph and square-field actions. Simultaneous
inner conjugation aligns the Sylow and Borel for the matrix calculation;
outer-coset invariance returns the conclusion to the original marking.
Together with the proved centralizer bound, this constructs the source Sylow
lift for every compatible natural-coordinate choice.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open Subgroup LocalCover LocalCover.SourceBorel SylowNormalizer
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- Conjugation by an actual Sylow actor preserves the marked Sylow image and
transports the component-factor sign through the literal projective map. -/
theorem source_marked_component_sign {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (t : G) (htS : t ∈ d.S) (neg : Bool)
    (hsign : ∀ x ∈ componentPart d.Yplus L,
      t*x*t⁻¹*(if neg then x else x⁻¹) ∈ d.Y.pCoreIn 2) :
    ∃ (P : Sylow 2 PSL(3,r.marking.F)) (htL : t ∈ normalizer (L : Set G)),
      (d.S.subgroupOf L).map (projectiveMap r.marking) = P ∧
      ((componentPart d.Yplus L).subgroupOf L).map (projectiveMap r.marking) =
        normalizer (P : Set PSL(3,r.marking.F)) ∧
      (P : Subgroup PSL(3,r.marking.F)).map (markedAction r.marking ⟨t,htL⟩).toMonoidHom = P ∧
      ∀ x ∈ normalizer (P : Set PSL(3,r.marking.F)),
        markedAction r.marking ⟨t,htL⟩ x * (if neg then x else x⁻¹) ∈ P := by
  obtain ⟨P,hP,hB⟩ := source_component_projective_borel s h r
  have hSL : d.S ≤ normalizer (L : Set G) :=
    le_sup_right.trans (h.outside.1.2.trans (h.normalizes_component s.earlier))
  let tN : normalizer (L : Set G) := ⟨t,hSL htS⟩
  let β := L.normalizerMonoidHom tN
  let α := markedAction r.marking tN
  have hβ (l : L) (hl : (l : G) ∈ d.S) : (β l : G) ∈ d.S :=
    d.S.mul_mem (d.S.mul_mem htS hl) (d.S.inv_mem htS)
  refine ⟨P,hSL htS,hP,hB,?_,?_⟩
  · apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [← hP] at hx ⊢
      obtain ⟨l,hl,rfl⟩ := hx
      change markedAction r.marking tN (projectiveMap r.marking l) ∈ _
      rw [markedAction_apply]
      exact ⟨β l,hβ l hl,rfl⟩
    · rw [card_map_of_injective α.injective]
  · intro x hx
    rw [←hB] at hx
    obtain ⟨l,hl,rfl⟩ := hx
    have hr := hsign l hl
    rw [r.cover.residual_core] at hr
    change markedAction r.marking tN (projectiveMap r.marking l) * (if neg then projectiveMap r.marking l else (projectiveMap r.marking l)⁻¹) ∈ (P : Subgroup PSL(3,r.marking.F))
    rw [←hP,markedAction_apply]
    cases neg with
    | false =>
      exact ⟨β l*l⁻¹,hr.1,by simp only [map_mul,map_inv]; rfl⟩
    | true =>
      exact ⟨β l*l,hr.1,by simp only [map_mul]; rfl⟩

/-- The opposite-factor sign survives the actual Aut/Inn projection and the
chosen diagonal cubic remains nontrivial of order three there. -/
theorem source_marked_opposite_sign {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (t : G) (_htS : t ∈ d.S)
    (htL : t ∈ normalizer (L : Set G))
    (hsign : ∀ x ∈ planeResidual d.M d.Y r.cover.borel.W₂,
      t*x*t⁻¹*x ∈ d.Y.pCoreIn 2) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 3) r.marking.F,
      let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))
      (q (Matrix.PSL3.OuterSolvable.linearConj r.marking.F b))^3=1 ∧
      q (Matrix.PSL3.OuterSolvable.linearConj r.marking.F b)≠1 ∧
      q (markedAction r.marking ⟨t,htL⟩) *
        q (Matrix.PSL3.OuterSolvable.linearConj r.marking.F b) *
        (q (markedAction r.marking ⟨t,htL⟩))⁻¹ *
        q (Matrix.PSL3.OuterSolvable.linearConj r.marking.F b)=1 := by
  obtain ⟨z,hz,hzdiag⟩ := r.cover.opposite_diagonal
  obtain ⟨hz3,b,hbout,hbreal⟩ := hzdiag
  have hYL : d.Y ≤ normalizer (L : Set G) :=
    r.cover.plus ▸ le_sup_left.trans (h.outside.1.2.trans (h.normalizes_component s.earlier))
  have hzY : z ∈ d.Y := ((planeResidual_le _ _ _).trans inf_le_left) hz
  let zN : normalizer (L : Set G) := ⟨z,hYL hzY⟩
  let tN : normalizer (L : Set G) := ⟨t,htL⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))
  let f := q.comp (markedAction r.marking)
  have he : markedAction r.marking zN=Matrix.PSL3.OuterSolvable.linearConj r.marking.F b :=
    markedAction_eq_of_realizes r.marking zN hbreal
  refine ⟨b,?_,?_,?_⟩
  · rw [←he,←map_pow]
    have hzN3 : zN^3=1 := Subtype.ext (by
      exact (orderOf_eq_prime_iff.mp hz3).1)
    rw [←map_pow,hzN3,map_one,map_one]
  · exact fun hzero => hbout ((QuotientGroup.eq_one_iff _).mp hzero)
  · have hr := hsign z hz
    rw [r.cover.residual_core] at hr
    let l : L := ⟨t*z*t⁻¹*z,hr.2⟩
    have hl : f (inclusion L.le_normalizer l)=1 := by
      change q (markedAction r.marking (inclusion L.le_normalizer l))=1
      rw [markedAction_on_component]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨_,rfl⟩
    have hNl : inclusion L.le_normalizer l=tN*zN*tN⁻¹*zN := Subtype.ext rfl
    rw [hNl,map_mul,map_mul,map_mul,map_inv] at hl
    simpa only [f,MonoidHom.comp_apply,he] using hl

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open Subgroup LocalCover LocalCover.SourceBorel SylowNormalizer
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3Four.SylowCosetRecognition
variable {G : Type*} [Group G] [Finite G]

/-- The two literal cubic-factor signs recognize the required coset in the
original projective marking. -/
theorem source_marked_coset_of_signs {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (t : G) (htS : t ∈ d.S) (neg : Bool)
    (hA : ∀ x ∈ componentPart d.Yplus L,
      t*x*t⁻¹*(if neg then x else x⁻¹) ∈ d.Y.pCoreIn 2)
    (hD : ∀ x ∈ planeResidual d.M d.Y r.cover.borel.W₂,
      t*x*t⁻¹*x ∈ d.Y.pCoreIn 2) :
    if neg then r.marking.Field t else r.marking.Graph t := by
  classical
  let F := r.marking.F
  let := Fintype.ofFinite F
  have hc : ringChar F=2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [←Nat.card_eq_fintype_card,r.marking.card])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨P,htL,hP,hB,hαP,hA'⟩ := source_marked_component_sign s h r t htS neg hA
  obtain ⟨b,hb3,hbout,hD'⟩ := source_marked_opposite_sign s h r t htS htL hD
  let α := markedAction r.marking ⟨t,htL⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  obtain ⟨g,hgU,hgB⟩ := BorelQuotient.sylow_normalizer_conjugate F
    (n:=2) (by decide) r.marking.card P
  let e : MulAut PSL(3,F) := MulAut.conj g
  let β : MulAut PSL(3,F) := e⁻¹*α*e
  have hmem (x : PSL(3,F)) : e x ∈ P ↔ x ∈ unipotent F := by
    change e x ∈ (P : Subgroup PSL(3,F)) ↔ x ∈ unipotent F
    rw [←hgU]
    constructor
    · rintro ⟨y,hy,he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have heβ (x : PSL(3,F)) : e (β x)=α (e x) := by
    change e (e.symm (α (e x)))=α (e x)
    exact e.apply_symm_apply _
  have hβU : (unipotent F).map β.toMonoidHom=unipotent F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      apply (hmem _).mp
      change e (β x) ∈ (P : Subgroup PSL(3,F))
      rw [heβ]
      change markedAction r.marking ⟨t,htL⟩ (e x) ∈ (P : Subgroup PSL(3,F))
      rw [←hαP]
      exact mem_map_of_mem _ ((hmem x).mpr hx)
    · rw [card_map_of_injective β.injective]
  have hβA : ∀ x ∈ Matrix.PSL3.LinearThree.borel F,
      β x*(if neg then x else x⁻¹) ∈ unipotent F := by
    intro x hx
    have hxP : e x ∈ normalizer (P : Set PSL(3,F)) :=
      hgB ▸ mem_map_of_mem e.toMonoidHom hx
    have hh := hA' _ hxP
    apply (hmem _).mp
    cases neg <;> simpa only [Bool.false_eq_true,↓reduceIte,map_mul,map_inv,heβ] using hh
  have hqe : q e=1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  have hqβ : q β=q α := by
    change q (e⁻¹*α*e)=q α
    rw [map_mul,map_mul,map_inv,hqe,inv_one,one_mul,mul_one]
  have hcover := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F
    (n:=2) (by decide) r.marking.card
    (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)
  obtain ⟨m,σ,hform | hform⟩ := ResidualLinear.standard_opposition_factorization β
    (hcover.symm ▸ mem_top β)
  all_goals
    have hactor : ∃ ε : Bool, β=projectiveActor F m σ ε := by
      first | exact ⟨false,by simpa [projectiveActor] using hform⟩ | exact ⟨true,hform⟩
    obtain ⟨ε,hactor⟩ := hactor
    rw [hactor] at hβU hβA hqβ
    have hD'' : q (projectiveActor F m σ ε)*q (linearConj F b)*
        (q (projectiveActor F m σ ε))⁻¹*q (linearConj F b)=1 := by
      rw [hqβ]
      exact hD'
    cases neg with
    | false =>
      obtain ⟨a,ha⟩ := graph_of_factor_signs F m σ ε hβU hβA b hb3 hbout hD''
      obtain ⟨c,hc⟩ := linear_coset_of_outer_eq F α (projectiveActor F m σ ε)
        (graph F) hqβ.symm a ha
      exact ⟨c,hc ▸ markedAction_realizes r.marking ⟨t,htL⟩⟩
    | true =>
      obtain ⟨hσ,a,ha⟩ := field_of_factor_signs F r.marking.card m σ ε hβU hβA b hb3 hbout hD''
      obtain ⟨c,hc⟩ := linear_coset_of_outer_eq F α (projectiveActor F m σ ε)
        (fieldAction F σ) hqβ.symm a ha
      exact ⟨σ,c,hσ,hc ▸ markedAction_realizes r.marking ⟨t,htL⟩⟩

/-- All three intrinsic Sylow calculations follow from the original local
source inputs in the selected marking and arbitrary compatible natural coordinates. -/
theorem source_sylow_calculations {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) : SylowCalculations d I L r := by
  refine ⟨source_sylow_centralizer_bound s h r,?_,?_⟩
  · intro a hYSM hplane c t ht
    refine source_marked_coset_of_signs s h r t ?_ false ?_ ?_
    · exact (c.s_preimage t).mpr (by rw [ht]; exact Or.inr (Or.inl rfl))
    · exact source_first_fixes_component_modulo s h r a hYSM hplane c t ht
    · exact source_first_inverts_opposite_modulo s h r a hYSM c t ht
  · intro a hYSM hplane c t ht
    refine source_marked_coset_of_signs s h r t ?_ true ?_ ?_
    · exact (c.s_preimage t).mpr (by rw [ht]; exact Or.inr (Or.inr (Or.inl rfl)))
    · intro x hx
      exact c.inverts_modulo t ht x
        (r.cover.plus ▸ ((map_subtype_le _).trans inf_le_left) hx)
    · intro x hx
      exact c.inverts_modulo t ht x (((planeResidual_le _ _ _).trans inf_le_left) hx)


/-- The source inputs supply the actual Sylow lift with no remaining intrinsic
calculation premises. -/
theorem source_sylow_result {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) : Nonempty (SylowResult d I L r) :=
  sylow_result s h r (source_sylow_calculations s h r)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
