module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.ModelCore
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.TerminalQuotient
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility

/-!
# Assembled scalar-sensitive source core and terminal quotient

The proved parabolic core comparison identifies the literal block kernel
with O₂(P). The aligned projection π from the original L₁ has a two-group
kernel, so it identifies L₁/O₂(L₁) with GL₂(F). Consequently this terminal
quotient has no nontrivial ambient-normal two-section and no two-chief factor.
No independent model core or terminal exclusion premise remains.

On the two-core, π gives an actual quotient
O₂(L₁)/(ker π ∩ O₂(L₁)) ≃ F². Conjugation has the action
w ↦ det(B)⁻¹ B⁻ᵀ w. Its additive and literal subgroup irreducibility,
noncentrality and order 2^(2n) are proved. The source point, natural and
dual marked layers are publicly supplied by `Irreducibility`; their
G.2.5(6–7) marking premises remain explicit there. Together these results
compute the requested constituent actions, without asserting which
sections survive the parent's intersection calculation or the printed count.

Source: Aschbacher–Smith, G.2.1 and G.2.5(1),(6–8),
printed pp.332,335–336; PDF pp.343,346–347.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree Irreducibility
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h} (a : PointAlignment d)

include d in
/-- The source field cardinality discharges the characteristic-two core comparison. -/
theorem source_block_kernel_eq_twoCore : (block F).ker = pCore 2 (pointParabolicSL F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [← Nat.card_eq_fintype_card] using d.field_card)
  exact block_kernel_eq_twoCore F

/-- The genuine L₁/O₂(L₁) is GL₂(F), with no independent core premise. -/
noncomputable def sourceTerminalEquiv (hn : 1 < n) :
    (D.L₁ ⧸ pCore 2 D.L₁) ≃* GL (Fin 2) F :=
  terminalQuotientEquiv a hn (source_block_kernel_eq_twoCore (d := d))

/-- The terminal equivalence retains the literal aligned projection and block map. -/
@[simp] theorem sourceTerminalEquiv_mk (hn : 1 < n) (x : D.L₁) :
    sourceTerminalEquiv a hn (QuotientGroup.mk' (pCore 2 D.L₁) x) =
      block F (localProjection a hn x) := rfl

include a in
/-- Every ambient-normal two-section above the actual local two-core is trivial. -/
theorem source_terminal_normal_two_section_trivial (hn : 1 < n)
    (A B : Subgroup (D.L₁ ⧸ pCore 2 D.L₁)) [A.Normal] [B.Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) :=
  terminal_normal_two_section_trivial a hn (source_block_kernel_eq_twoCore (d := d)) A B hp

include a in
/-- Discharges the terminal chief-factor premise using the proved parabolic core theorem. -/
theorem source_terminal_hasNoTwoChiefFactors (hn : 1 < n) :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) :=
  terminal_hasNoTwoChiefFactors a hn (source_block_kernel_eq_twoCore (d := d))

include d in
/-- The terminal conclusion under the source hypothesis alone; the alignment exists by SL₃ transitivity. -/
theorem larger_terminal_hasNoTwoChiefFactors (hn : 1 < n) :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) := by
  obtain ⟨b⟩ := exists_pointAlignment d
  exact source_terminal_hasNoTwoChiefFactors b hn

/-- The original local two-core is the preimage of the literal block kernel. -/
theorem source_core_mem_iff (hn : 1 < n) (x : D.L₁) :
    x ∈ pCore 2 D.L₁ ↔ localProjection a hn x ∈ (block F).ker := by
  rw [source_block_kernel_eq_twoCore (d := d), ← local_core_preimage a hn]
  rfl

/-- Coordinates on the image of the actual local two-core in the unipotent radical. -/
noncomputable def sourceRadicalProjection (hn : 1 < n) :
    pCore 2 D.L₁ →* Multiplicative (Fin 2 → F) :=
  (radicalEquiv F).symm.toMonoidHom.comp
    (((localProjection a hn).comp (pCore 2 D.L₁).subtype).codRestrict (block F).ker
      (fun x => (source_core_mem_iff a hn x).mp x.property))

/-- The coordinates recover precisely the original aligned projection. -/
@[simp] theorem sourceRadicalProjection_image (hn : 1 < n) (x : pCore 2 D.L₁) :
    radicalHom F (sourceRadicalProjection a hn x) = localProjection a hn x.val :=
  congrArg Subtype.val ((radicalEquiv F).apply_symm_apply _)

/-- The local two-core maps onto the whole geometric radical. -/
theorem sourceRadicalProjection_surjective (hn : 1 < n) :
    Function.Surjective (sourceRadicalProjection a hn) := by
  intro w
  obtain ⟨x,hx⟩ := localProjection_surjective a hn (radicalHom F w)
  have hc : x ∈ pCore 2 D.L₁ := (source_core_mem_iff a hn x).mpr (by
    rw [hx]; exact block_radical F w)
  refine ⟨⟨x,hc⟩, radicalHom_injective F ?_⟩
  rw [sourceRadicalProjection_image, hx]

/-- Only the original aligned star kernel is lost on restricting to the local two-core. -/
theorem sourceRadicalProjection_kernel (hn : 1 < n) :
    (sourceRadicalProjection a hn).ker = (localProjection a hn).ker.subgroupOf (pCore 2 D.L₁) := by
  ext x
  change sourceRadicalProjection a hn x = 1 ↔ localProjection a hn x.val = 1
  rw [← sourceRadicalProjection_image a hn x,
    ← (radicalHom F).map_one, (radicalHom_injective F).eq_iff]

/-- The literal radical section of O₂(L₁), retaining its original quotient denominator. -/
noncomputable def sourceRadicalQuotientEquiv (hn : 1 < n) :
    (pCore 2 D.L₁ ⧸ (localProjection a hn).ker.subgroupOf (pCore 2 D.L₁)) ≃*
      Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (sourceRadicalProjection_kernel a hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (sourceRadicalProjection_surjective a hn))

/-- Representative compatibility for the source radical section. -/
@[simp] theorem sourceRadicalQuotientEquiv_mk (hn : 1 < n) (x : pCore 2 D.L₁) :
    sourceRadicalQuotientEquiv a hn
      (QuotientGroup.mk' ((localProjection a hn).ker.subgroupOf (pCore 2 D.L₁)) x) =
      sourceRadicalProjection a hn x := rfl

/-- Conjugation by L₁ on its own normal two-core. -/
def sourceCoreConjugate (l : D.L₁) (y : pCore 2 D.L₁) : pCore 2 D.L₁ :=
  ⟨l * y.val * l⁻¹, (inferInstance : (pCore 2 D.L₁).Normal).conj_mem _ y.property l⟩

/-- Actual source conjugation has the full det⁻¹-twisted contragredient action. -/
theorem sourceRadicalProjection_conjugate (hn : 1 < n) (l : D.L₁) (y : pCore 2 D.L₁) :
    (sourceRadicalProjection a hn (sourceCoreConjugate l y)).toAdd =
      radicalAction F (localProjection a hn l) (sourceRadicalProjection a hn y).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply radicalHom_injective F
  change radicalHom F (sourceRadicalProjection a hn (sourceCoreConjugate l y)) = _
  rw [sourceRadicalProjection_image]
  exact source_radical_conjugation a hn l y.val _ (sourceRadicalProjection_image a hn y).symm

/-- The induced action on the literal source radical quotient. -/
noncomputable def sourceRadicalQuotientAction (hn : 1 < n) (l : D.L₁)
    (q : pCore 2 D.L₁ ⧸ (localProjection a hn).ker.subgroupOf (pCore 2 D.L₁)) :
    pCore 2 D.L₁ ⧸ (localProjection a hn).ker.subgroupOf (pCore 2 D.L₁) :=
  (sourceRadicalQuotientEquiv a hn).symm (Multiplicative.ofAdd
    (radicalAction F (localProjection a hn l) (sourceRadicalQuotientEquiv a hn q).toAdd))

/-- The quotient action is induced by actual group conjugation, not an arbitrary transported action. -/
theorem sourceRadicalQuotientAction_mk (hn : 1 < n) (l : D.L₁) (y : pCore 2 D.L₁) :
    sourceRadicalQuotientAction a hn l
      (QuotientGroup.mk' ((localProjection a hn).ker.subgroupOf (pCore 2 D.L₁)) y) =
    QuotientGroup.mk' ((localProjection a hn).ker.subgroupOf (pCore 2 D.L₁))
      (sourceCoreConjugate l y) := by
  apply (sourceRadicalQuotientEquiv a hn).injective
  apply Multiplicative.toAdd.injective
  simp only [sourceRadicalQuotientAction, MulEquiv.apply_symm_apply,
    sourceRadicalQuotientEquiv_mk]
  exact (sourceRadicalProjection_conjugate a hn l y).symm

/-- Binary irreducibility of the computed source action in additive coordinates. -/
theorem source_radical_irreducible (hn : 1 < n) :
    AdditivelyIrreducible (fun l => radicalAction F (localProjection a hn l)) :=
  radicalAction_irreducible F _ (localProjection_surjective a hn)

/-- The original residual acts nontrivially on the radical constituent. -/
theorem source_radical_noncentral (hn : 1 < n) :
    Noncentral (fun l => radicalAction F (localProjection a hn l)) :=
  radicalAction_noncentral F _ (localProjection_surjective a hn)

/-- Every subgroup of the literal source radical section invariant under L₁ is trivial or full. -/
theorem sourceRadicalQuotient_irreducible (hn : 1 < n) :
    SubgroupIrreducible (sourceRadicalQuotientAction a hn) := by
  intro K hK
  let e := sourceRadicalQuotientEquiv a hn
  have he (l : D.L₁) (q) : e (sourceRadicalQuotientAction a hn l q) =
      Multiplicative.ofAdd (radicalAction F (localProjection a hn l) (e q).toAdd) :=
    e.apply_symm_apply _
  have hInv : ∀ l v, v ∈ (K.map e.toMonoidHom).toAddSubgroup' →
      radicalAction F (localProjection a hn l) v ∈ (K.map e.toMonoidHom).toAddSubgroup' := by
    rintro l v ⟨q,hq,hv⟩
    refine ⟨sourceRadicalQuotientAction a hn l q, hK l q hq, ?_⟩
    change e (sourceRadicalQuotientAction a hn l q) = _
    rw [he]
    have hv' : (e q).toAdd = v := congrArg Multiplicative.toAdd hv
    rw [hv']
    rfl
  rcases source_radical_irreducible a hn _ hInv with h | h
  · left
    have hm : K.map e.toMonoidHom = ⊥ := Subgroup.toAddSubgroup'.injective
      (h.trans Subgroup.toAddSubgroup'.map_bot.symm)
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm
  · right
    have hm : K.map e.toMonoidHom = ⊤ := Subgroup.toAddSubgroup'.injective
      (h.trans Subgroup.toAddSubgroup'.map_top.symm)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_top_of_surjective _ e.surjective]
    exact hm

/-- The conjugation action on the literal source radical section is noncentral. -/
theorem sourceRadicalQuotient_noncentral (hn : 1 < n) :
    Noncentral (sourceRadicalQuotientAction a hn) := by
  obtain ⟨l,v,hv⟩ := source_radical_noncentral a hn
  let e := sourceRadicalQuotientEquiv a hn
  refine ⟨l,e.symm (Multiplicative.ofAdd v), ?_⟩
  intro he
  have hh := congrArg (fun q => (e q).toAdd) he
  change (e (e.symm (Multiplicative.ofAdd (radicalAction F (localProjection a hn l)
    (e (e.symm (Multiplicative.ofAdd v))).toAdd)))).toAdd = _ at hh
  simp only [e.apply_symm_apply] at hh
  exact hv hh

include a in
/-- The radical section has the required order 2^(2n). -/
theorem source_radical_card (hn : 1 < n) :
    Nat.card (pCore 2 D.L₁ ⧸ (localProjection a hn).ker.subgroupOf (pCore 2 D.L₁)) =
      2 ^ (2*n) := by
  rw [Nat.card_congr (sourceRadicalQuotientEquiv a hn).toEquiv]
  change Nat.card (Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul, Nat.mul_comm n 2]
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
