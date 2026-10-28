module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalDihedral
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs
public import Theory.Representation.BinaryOffender.SectionLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs

/-!
# Terminal model exclusions from the proved Sylow action

Fixed-space generation and a faithful Sylow action detect the two-residual.
For Sz(2), order twenty then kills the action kernel; simplicity handles
all larger Suzuki groups. Their quadratic square bound excludes them from
the terminal index comparison.

For the larger unitary groups, quotient by the global fixed space. Perfectness
preserves a nontrivial action and kills new fixed vectors, while fixed
codimension cannot increase. The minimum-degree square bound therefore
applies without full faithfulness or residual fixed-space vanishing on the
original section. A quadratic actor faithful on its containing Sylow is
itself elementary. The actual source model catalogue consequently reduces
to the linear and field-two unitary rows.

`TerminalSmallModels` applies these bounds to the literal terminal V_t/Z_t
module and its original L_t/Q_t action, including the source model transport.
Source: DGS, *Groups and Graphs* (1985), (7.5), pp.130--131; the Chapter 5
quadratic bounds and the fixed-space-generation correction to (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem residual_detected' (σ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (hg : GeneratedByFixedSpace σ T)
    (hd : Disjoint σ.ker (T : Subgroup D)) (hne : (T : Subgroup D) ≠ ⊥) :
    ¬ pResidual 2 D ≤ σ.ker := by
  intro hk
  have hR : fixedSpace σ (pResidual 2 D) = ⊤ := by
    apply top_unique
    intro w _ a
    change σ a w = w
    rw [show σ a = 1 from hk a.property]
    rfl
  have hfix : fixedSpace σ ⊤ = fixedSpace σ T := by
    have he := σ.invariants_comp_sup (pResidual 2 D) (T : Subgroup D)
    change fixedSpace σ (pResidual 2 D ⊔ (T : Subgroup D)) =
      fixedSpace σ (pResidual 2 D) ⊓ fixedSpace σ T at he
    rwa [pResidual_sup_sylow_eq_top T,hR,top_inf_eq] at he
  have hspan : (⨆ g : D, (fixedSpace σ T).map (σ g)) ≤ fixedSpace σ ⊤ := by
    apply iSup_le
    rintro g _ ⟨v,hv,rfl⟩
    have hv' : v ∈ fixedSpace σ ⊤ := hfix.symm ▸ hv
    rw [show σ g v = v from hv' ⟨g,mem_top _⟩]
    exact hv'
  have htop : fixedSpace σ ⊤ = ⊤ := top_unique (hg ▸ hspan)
  apply hne
  apply bot_unique
  intro t ht
  have htk : t ∈ σ.ker := by
    apply LinearMap.ext
    intro w
    exact (show w ∈ fixedSpace σ ⊤ from htop.symm ▸ Submodule.mem_top) ⟨t,mem_top _⟩
  exact hd.le_bot ⟨htk,ht⟩

private theorem prime_times_two_power_faithful
    {r n : ℕ} (hr : r.Prime) (hc : Nat.card D = 2^n*r)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hne : (T : Subgroup D) ≠ ⊥) : Function.Injective σ := by
  apply σ.ker_eq_bot_iff.mp
  by_cases hdiv : r ∣ Nat.card σ.ker
  · have hi : σ.ker.index ∣ 2^n := by
      apply Nat.dvd_of_mul_dvd_mul_right hr.pos
      have hm := Nat.mul_dvd_mul_right hdiv σ.ker.index
      rw [σ.ker.card_mul_index,hc,mul_comm r σ.ker.index] at hm
      exact hm
    exact (residual_detected' σ T hg hd hne
      ((pResidual_le_iff_isPGroup_quotient 2 σ.ker).mpr
        (IsPGroup.of_card_dvd_pow (σ.ker.index_eq_card ▸ hi)))).elim
  · have hcard : Nat.card σ.ker ∣ 2^n :=
      ((hr.coprime_iff_not_dvd.mpr hdiv).symm).dvd_of_dvd_mul_right
        (hc ▸ σ.ker.card_subgroup_dvd_card)
    have hp : IsPGroup 2 σ.ker := IsPGroup.of_card_dvd_pow hcard
    exact bot_unique (fun x hx => hd.le_bot ⟨hx,hp.le_sylow_of_normal T hx⟩)

/-- Fixed-space generation upgrades faithful Sylow action for every Suzuki model. -/
theorem suzuki_fixed_generated_sylow_faithful
    (m : ℕ) (σ : Representation (ZMod 2) (SuzukiMatrixGroup m) W)
    (T : Sylow 2 (SuzukiMatrixGroup m))
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup (SuzukiMatrixGroup m)))
    (hne : (T : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥) : Function.Injective σ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact prime_times_two_power_faithful (by decide : Nat.Prime 5)
      (show Nat.card (SuzukiMatrixGroup 0) = 2^2*5 from suzukiZero_card) σ T hg hd hne
  · let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    apply σ.ker_eq_bot_iff.mp
    rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact hk
    · exact (residual_detected' σ T hg hd hne (hk ▸ le_top)).elim

omit [Finite D] in
private theorem quotient_nontrivial_of_perfect [Group.IsPerfect D]
    (ρ : Representation (ZMod 2) D W) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ g, globalFixedQuotient ρ g ≠ 1 := by
  by_contra! he
  have hc : subspaceCommutator ρ ⊤ ⊤ ≤ fixedSpace ρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact (Submodule.Quotient.eq _).mp
      (LinearMap.congr_fun (he g) ((fixedSpace ρ ⊤).mkQ v))
  have hf := le_fixedSpace_of_commutator_le_fixedSpace ρ (⊤ : Subgroup D) ⊤
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hc
  obtain ⟨g,hg⟩ := hnt
  apply hg
  ext v
  exact hf Submodule.mem_top ⟨g,mem_top g⟩

variable [Finite W]
local instance (C : Submodule (ZMod 2) W) : Finite (W ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

omit [Finite D] in
private theorem index_central_quotient_le (ρ : Representation (ZMod 2) D W)
    (A : Subgroup D) :
    Nat.card ((W ⧸ fixedSpace ρ ⊤) ⧸ fixedSpace (globalFixedQuotient ρ) A) ≤
      Nat.card (W ⧸ fixedSpace ρ A) := by
  have hd := fixedCodim_quotient_add_subrepresentation_le ρ (globalFixedSubrepresentation ρ) A
  change fixedCodim (globalFixedQuotient ρ) A + _ ≤ fixedCodim ρ A at hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := (W ⧸ fixedSpace ρ ⊤) ⧸ fixedSpace (globalFixedQuotient ρ) A),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ fixedSpace ρ A)]
  exact Nat.pow_le_pow_right (by simp only [Nat.card_zmod]; decide : 1 ≤ Nat.card (ZMod 2)) (show fixedCodim (globalFixedQuotient ρ) A ≤ fixedCodim ρ A by omega)

/-- The large special-unitary square bound needs only a nontrivial action. -/
theorem su3_nontrivial_elementary_square_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 A] :
    Nat.card A ^ 2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  let : Group.IsPerfect J.specialSubgroup := SU3.BinaryDegree.isPerfect_specialSubgroup J hn hc hconj
  exact (su3_elementary_square_bound J hn hc hconj (globalFixedQuotient ρ)
    (quotient_nontrivial_of_perfect ρ hnt) (globalFixedQuotient_fixed_eq_bot ρ) A).trans
      (index_central_quotient_le ρ A)

/-- The same square bound retains the projective unitary carrier. -/
theorem psu3_nontrivial_elementary_square_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (hnt : ∃ g, ρ g ≠ 1) (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    [IsElementaryAbelian 2 A] :
    Nat.card A ^ 2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  let : Group.IsPerfect J.specialSubgroup := SU3.BinaryDegree.isPerfect_specialSubgroup J hn hc hconj
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective J.specialToProjective_surjective
  exact (psu3_elementary_square_bound J hn hc hconj (globalFixedQuotient ρ)
    (quotient_nontrivial_of_perfect ρ hnt) (globalFixedQuotient_fixed_eq_bot ρ) A).trans
      (index_central_quotient_le ρ A)

omit [Finite D] [Finite W] in
private theorem faithful_transport {H : Type*} [Group H] (e : D ≃* H)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hd : Disjoint σ.ker (T : Subgroup D)) :
    Disjoint (σ.comp e.symm.toMonoidHom).ker
      ((T : Subgroup D).map e.toMonoidHom) := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro _ ⟨hk,x,hx,rfl⟩
  have hxk : x ∈ σ.ker := by simpa using hk
  have hx1 := mem_bot.mp (hd.le_bot ⟨hxk,hx⟩)
  simp only [hx1,map_one,mem_bot]

omit [Finite D] [Finite W] in
private theorem fixed_transport {H : Type*} [Group H] (e : D ≃* H)
    (σ : Representation (ZMod 2) D W) (A : Subgroup D) :
    fixedSpace (σ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) = fixedSpace σ A := by
  rw [fixedSpace_comp_map,map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D := by ext x; simp
  rw [he,map_id]

omit [Finite D] [Finite W] in
private theorem quadratic_transport {H : Type*} [Group H] (e : D ≃* H)
    (σ : Representation (ZMod 2) D W) (A : Subgroup D) (hq : IsQuadratic σ A) :
    IsQuadratic (σ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
  simpa using hq a ha b hb w

omit [Finite D] [Finite W] in
private theorem elementary_actor (σ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (A : Subgroup D) (hAT : A ≤ T)
    (hd : Disjoint σ.ker (T : Subgroup D)) (hq : IsQuadratic σ A) :
    IsElementaryAbelian 2 A := by
  have hf : Function.Injective (σ.comp A.subtype) := by
    apply (σ.comp A.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨ha,hAT a.property⟩))
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    elementary_of_faithful_quadratic (σ.comp A.subtype) hf ⊤
      (fun a _ b _ w => hq a a.property b b.property w)
  exact IsElementaryAbelian.of_surjective (topEquiv (G := A)).toMonoidHom
    (topEquiv (G := A)).surjective

omit [Finite D] [Finite W] in
private theorem nontrivial_action (σ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (A : Subgroup D) (hAT : A ≤ T) (hA : 1 < Nat.card A)
    (hd : Disjoint σ.ker (T : Subgroup D)) : ∃ g, σ g ≠ 1 := by
  have hne : A ≠ ⊥ := by intro he; simp [he] at hA
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  exact ⟨a,fun hk => ha1 (mem_bot.mp (hd.le_bot ⟨hk,hAT ha⟩))⟩

/-- The terminal actor and index bound leave only linear or field-two unitary models. -/
theorem terminal_action_model_alternatives (hm : IsRankOneModel D)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) :
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL D 2 (2^n)) ∨
      IsSU D 3 2 ∨ ClassicalGroup.IsPSU D 3 2 := by
  let : IsElementaryAbelian 2 A := elementary_actor σ T A hAT hd hq
  have hnt := nontrivial_action σ T A hAT hA hd
  cases hm with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | dihedral he =>
    obtain ⟨e⟩ := he
    exact (dihedral_fixed_generated_index_obstruction e σ T A hAT hA hg hd hb).elim
  | suzuki m he =>
    obtain ⟨e⟩ := he
    let ρ := σ.comp e.symm.toMonoidHom
    let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
    have hgen : GeneratedByFixedSpace ρ S :=
      generatedByFixedSpace_of_equivariant_surjection σ ρ e.toMonoidHom LinearMap.id
        Function.surjective_id (by intro g w; simp [ρ]) T hg
    have hdis := faithful_transport e σ T hd
    have hne : (S : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥ := by
      intro hs
      have ha : A.map e.toMonoidHom = ⊥ := bot_unique ((map_mono hAT).trans hs.le)
      have hc := card_map_of_injective (K := A) (f := e.toMonoidHom) e.injective
      rw [ha,card_bot] at hc
      omega
    have hf := suzuki_fixed_generated_sylow_faithful m ρ S hgen hdis hne
    have hh := suzuki_all_square_bound m ρ hf S (A.map e.toMonoidHom)
      (map_mono hAT) (quadratic_transport e σ A hq)
    rw [card_map_of_injective e.injective,fixed_transport] at hh
    nlinarith
  | special_unitary n hn he =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := he
      let := hF
      let := hfin
      let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
      have hnt' : ∃ g, (σ.comp e.symm.toMonoidHom) g ≠ 1 := by
        obtain ⟨g,hg⟩ := hnt
        exact ⟨e g,by simpa using hg⟩
      have hh := su3_nontrivial_elementary_square_bound J hn2 hcard hconj
        (σ.comp e.symm.toMonoidHom) hnt' (A.map e.toMonoidHom)
      rw [card_map_of_injective e.injective,fixed_transport] at hh
      nlinarith
    · exact Or.inr (Or.inl (by simpa only [show n = 1 by omega,pow_one] using he))
  | projective_unitary n hn he =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := he
      let := hF
      let := hfin
      let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
      have hnt' : ∃ g, (σ.comp e.symm.toMonoidHom) g ≠ 1 := by
        obtain ⟨g,hg⟩ := hnt
        exact ⟨e g,by simpa using hg⟩
      have hh := psu3_nontrivial_elementary_square_bound J hn2 hcard hconj
        (σ.comp e.symm.toMonoidHom) hnt' (A.map e.toMonoidHom)
      rw [card_map_of_injective e.injective,fixed_transport] at hh
      nlinarith
    · exact Or.inr (Or.inr (by simpa only [show n = 1 by omega,pow_one] using he))

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
