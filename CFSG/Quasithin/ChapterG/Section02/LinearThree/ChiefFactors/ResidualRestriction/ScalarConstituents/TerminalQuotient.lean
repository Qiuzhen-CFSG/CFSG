module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Source
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Terminal
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
/-!
# The genuine larger-field terminal quotient

For a field of order 2^n with n > 1, every ambient-normal two-section of
GL₂(F) is trivial. Intersect the upper endpoint with SL₂(F). The canonical
SL₂/PSL₂ comparison and simplicity make this intersection trivial or all
of SL₂. In the second case perfectness kills its image in the two-group
section. In either case the determinant leaves only an odd-order image.
The assertion concerns ambient-normal endpoints, not arbitrary sections.

The aligned source projection has a two-group kernel. Conditional on the
independently produced identification of the parabolic block kernel with
its two-core, it therefore identifies the literal L₁/O₂(L₁) with GL₂(F).
The representative equation retains the actual lower-right block map.
The final corollary supplies precisely the terminal chief-factor premise
of `ChiefFactors.residual_chief_accounting`. It does not assert the full
G.2.5(8) count; the parent assembly still discharges the parabolic core premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.1 and G.2.5(8), printed pp.332,335–336, PDF pp.343,346–347.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups

private theorem perfect_pGroup_map_one {S Q : Type*} [Group S] [Group Q]
    [Finite Q] [Group.IsPerfect S] (f : S →* Q) (hp : IsPGroup 2 Q) (s : S) :
    f s = 1 := by
  have hr : f.range = ⊥ := by
    by_contra h
    let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr h
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    exact Group.IsPerfect.not_isNilpotent f.range (hp.to_subgroup _).isNilpotent
  exact Subgroup.mem_bot.mp (hr ▸ (show f s ∈ f.range from ⟨s, rfl⟩))

private theorem normal_section_trivial_of_simple_kernel
    {H S U : Type*} [Group H] [Finite H] [Group S] [Group U] [Finite U]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (j : S →* H) (χ : H →* U) (hker : χ.ker = j.range)
    (hodd : Odd (Nat.card U)) (A B : Subgroup H) [B.Normal]
    [(A.subgroupOf B).Normal] (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) := by
  let q := QuotientGroup.mk' (A.subgroupOf B)
  have hk (b : B) (hb : χ b = 1) : q b = 1 := by
    obtain ⟨s, hs⟩ := show (b : H) ∈ j.range from
      hker ▸ (show (b : H) ∈ χ.ker from hb)
    rcases (inferInstance : (B.comap j).Normal).eq_bot_or_eq_top with h | h
    · have hs1 : s = 1 := Subgroup.mem_bot.mp
        (h ▸ (show s ∈ B.comap j from (show j s ∈ B from hs.symm ▸ b.property)))
      have hb1 : b = 1 := Subtype.ext (hs.symm.trans (hs1 ▸ j.map_one))
      rw [hb1, map_one]
    · let k : S →* B := j.codRestrict B (fun s =>
        show s ∈ B.comap j from h ▸ mem_top s)
      have hs' : k s = b := Subtype.ext hs
      simpa only [MonoidHom.comp_apply, hs'] using
        perfect_pGroup_map_one (q.comp k) hp s
  apply subsingleton_of_forall_eq 1
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf B) x
  have hm : (q b) ^ Nat.card U = 1 := by
    rw [← map_pow]
    apply hk
    change χ ((b : H) ^ Nat.card U) = 1
    rw [map_pow, pow_card_eq_one']
  obtain ⟨k, hk⟩ := hp.exists_orderOf_dvd_pow (q b)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_left.pow_left k) hk (orderOf_dvd_of_pow_eq_one hm))

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree

variable (F : Type*) [Field F] [Finite F]

/-- Normal two-sections are trivial in any group identified with the actual
GL₂ matrix group. The determinant and SL₂ inclusion are transported through e. -/
theorem normal_two_section_trivial_of_GL2_equiv
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {H : Type*} [Group H] [Finite H] (e : H ≃* GL (Fin 2) F)
    (A B : Subgroup H) [A.Normal] [B.Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [← Nat.card_eq_fintype_card] using hF)
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  let : IsSimpleGroup PSL(2,F) := ProjectiveSpecialLinearGroup.rank_two_simple hcard
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  obtain ⟨t, ht0, ht1⟩ := ENat.exists_ne_ne_of_three_le (α := F)
    (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast (show 3 ≤ Fintype.card F by
      simpa only [Nat.card_eq_fintype_card] using (show 3 ≤ Nat.card F by omega))) 0 1
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top ht0 (by
    intro ht
    rcases sq_eq_one_iff.mp ht with h | h
    · exact ht1 h
    · exact ht1 (by simpa only [CharTwo.neg_eq] using h))⟩
  let j : SL(2,F) →* H := e.symm.toMonoidHom.comp SpecialLinearGroup.toGL
  let χ : H →* Fˣ := GeneralLinearGroup.det.comp e.toMonoidHom
  have hker : χ.ker = j.range := by
    ext x
    constructor
    · intro hx
      have hd : GeneralLinearGroup.det (e x) = 1 := hx
      let s : SL(2,F) := ⟨(e x : Matrix (Fin 2) (Fin 2) F), congrArg Units.val hd⟩
      refine ⟨s, ?_⟩
      change e.symm (SpecialLinearGroup.toGL s) = x
      apply e.injective
      simpa only [e.apply_symm_apply] using (show SpecialLinearGroup.toGL s = e x from
        Units.ext rfl)
    · rintro ⟨s, rfl⟩
      change GeneralLinearGroup.det (e (e.symm (SpecialLinearGroup.toGL s))) = 1
      simp
  exact normal_section_trivial_of_simple_kernel j χ hker
    (units_odd F hF (by omega)) A B hp

/-- GL₂ over a larger binary field has no nontrivial ambient-normal two-section. -/
theorem GL2_normal_two_section_trivial
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (A B : Subgroup (GL (Fin 2) F)) [A.Normal] [B.Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) :=
  normal_two_section_trivial_of_GL2_equiv F hF hn (MulEquiv.refl _) A B hp

/-- The model supplies the literal chief-series terminal predicate. -/
theorem GL2_hasNoTwoChiefFactors
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (GL (Fin 2) F) := by
  intro A B hAB hp
  have hs := GL2_normal_two_section_trivial F hF hn A.val B.val hp
  exact hAB.lt.not_ge (Subgroup.subgroupOf_eq_top.mp
    (QuotientGroup.subsingleton_iff.mp hs))

variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F} {n : ℕ} {g h : G} {d : Hypothesis D F n g h} (a : PointAlignment d)

/-- Restriction of the aligned star kernel to the literal embedded two-residual. -/
theorem localProjection_kernel_twoGroup (hn : 1 < n) :
    IsPGroup 2 (localProjection a hn).ker := by
  rw [localProjection, MonoidHom.ker_codRestrict, rawProjection, ← MonoidHom.comap_ker]
  exact a.projection_kernel_twoGroup.comap_of_injective _ (inclusion_injective _)

/-- The genuine local projection lifts the parabolic two-core exactly. -/
theorem local_core_preimage (hn : 1 < n) :
    (pCore 2 (pointParabolicSL F)).comap (localProjection a hn) = pCore 2 D.L₁ :=
  (localProjection a hn).comap_pCore_of_ker_isPGroup
    (localProjection_surjective a hn) (localProjection_kernel_twoGroup a hn)

/-- The terminal source quotient is GL₂, retaining its odd determinant factor.
Only the independent parabolic core comparison remains an explicit premise. -/
noncomputable def terminalQuotientEquiv (hn : 1 < n)
    (hcore : (block F).ker = pCore 2 (pointParabolicSL F)) :
    (D.L₁ ⧸ pCore 2 D.L₁) ≃* GL (Fin 2) F :=
  ((localProjection a hn).pCoreQuotientEquiv
    (localProjection_surjective a hn) (localProjection_kernel_twoGroup a hn)).trans
    ((QuotientGroup.quotientMulEquivOfEq hcore.symm).trans (blockQuotientEquiv F))

/-- The identification uses the literal aligned projection and block matrix. -/
@[simp] theorem terminalQuotientEquiv_mk (hn : 1 < n)
    (hcore : (block F).ker = pCore 2 (pointParabolicSL F)) (x : D.L₁) :
    terminalQuotientEquiv a hn hcore (QuotientGroup.mk' (pCore 2 D.L₁) x) =
      block F (localProjection a hn x) := rfl

include a in
/-- No nontrivial normal two-section survives above the source local two-core. -/
theorem terminal_normal_two_section_trivial (hn : 1 < n)
    (hcore : (block F).ker = pCore 2 (pointParabolicSL F))
    (A B : Subgroup (D.L₁ ⧸ pCore 2 D.L₁)) [A.Normal] [B.Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) :=
  normal_two_section_trivial_of_GL2_equiv F d.field_card hn
    (terminalQuotientEquiv a hn hcore) A B hp

include a in
/-- Discharges the terminal premise of `residual_chief_accounting`, conditional
only on the separately produced parabolic core comparison. -/
theorem terminal_hasNoTwoChiefFactors (hn : 1 < n)
    (hcore : (block F).ker = pCore 2 (pointParabolicSL F)) :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) := by
  intro A B hAB hp
  have hs := terminal_normal_two_section_trivial a hn hcore A.val B.val hp
  exact hAB.lt.not_ge (Subgroup.subgroupOf_eq_top.mp
    (QuotientGroup.subsingleton_iff.mp hs))

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
