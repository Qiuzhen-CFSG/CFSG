module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.LocalGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore

/-!
# Source choices and the earlier local lemmas of Chapter J

Starting with the original Ru1/Ru2 setup, choose the cubic subgroup and its
invariant Singer subgroup, then choose the two involution representatives.
The proved J.2.2 and J.2.3 theorems discharge every extra input of the local
fusion argument. In particular the same literal choices carry J.2.4–6,
J.2.8 and the preliminary equality C_H(s) = T_s used in J.2.7.

Source: Aschbacher–Smith, J.2.1–8, printed pp.432–437.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- The choices preceding J.2.3 exist for every original local setup. -/
theorem exists_choices (d : LocalSetup G) : Nonempty (Centralizers.Choices d) := by
  obtain ⟨B, a, ha⟩ := SpecialCore.exists_source_choices d
  obtain ⟨e⟩ := ha.one.2
  let s := e.symm (Multiplicative.ofAdd (1, 0))
  have hs : s ≠ 1 := by
    intro hs
    have he := congrArg e hs
    simp only [s, MulEquiv.apply_symm_apply, map_one] at he
    have h := congrArg (fun x : Multiplicative (ZMod 2 × ZMod 2) => x.toAdd.1) he
    exact one_ne_zero h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := d.toTypeRuSetup.Z) 2
    (by rw [d.card_Z])
  have hzg : d.toTypeRuSetup.Z = zpowers (z : G) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr z.property) ?_).symm
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, d.card_Z]
  exact ⟨{
    sylowThree := B
    B7 := a.B7
    B7_le := a.le_L
    B7_card := a.card_seven
    B_normalizes := a.normalized
    s := s
    s_mem := s.property
    s_ne_one := fun h => hs (Subtype.ext h)
    z := z
    z_generator := hzg }⟩

variable {d : LocalSetup G} (c : Centralizers.Choices d)

/-- The chosen cubic subgroup has its source order. -/
theorem B_card : Nat.card c.B = 3 :=
  SpecialCore.cubicSubgroup_card d.toTypeRuSetup c.sylowThree d.card_Z
    (d.center_eq.le.trans inf_le_left)

/-- The chosen generator of Z is an involution. -/
theorem z_order : orderOf c.z = 2 := by
  rw [← Nat.card_zpowers, ← c.z_generator]
  exact d.card_Z

/-- The quaternion premise is supplied by the full source J.2.3. -/
theorem quaternion (B : Sylow 3 d.toTypeRuSetup.L₁) :
    Nonempty (Fusion.HB d.toTypeRuSetup B ≃* QuaternionGroup 2) := by
  obtain ⟨a, ha⟩ := lemma_J_2_3 d B
  exact ha.seven

/-- All four earlier fusion lemmas on the original representatives and maps. -/
theorem fusion : Fusion.SourceJ24 d.toTypeRuSetup ∧
    Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree ∧
    Fusion.SourceJ26 d.toTypeRuSetup c.z ∧
    Fusion.SourceJ28 d.toTypeRuSetup c.z := by
  apply Fusion.source_conclusions_of_earlier d c.sylowThree
  · intro l hl
    exact (lemma_J_2_2_five_source d l l.property hl).2
  · exact quaternion c.sylowThree
  · exact c.z_mem_Z
  · intro hz
    have ho := z_order c
    simp [hz] at ho

/-- J.2.5 for any cubic Sylow choice, without a quaternion or action premise. -/
theorem sourceJ25 (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    Fusion.SourceJ25 d.toTypeRuSetup B :=
  Fusion.Outer.sourceJ25_of_centralProduct d B
    (Fusion.centralProductData_of_quaternion d B (quaternion B))

/-- The exact earlier-source record needed by the five-centralizer argument. -/
theorem earlier : c.EarlierJ27Inputs :=
  ⟨d.card_Z, (fusion c).1, sourceJ25 d, (fusion c).2.2.1⟩

/-- The equality used before the normalizer-extension case distinction. -/
theorem H_inf_Gs_eq_Ts : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts :=
  c.H_inf_Gs_eq_Ts_source (fusion c).2.2.1

/-- The source Sylow choice and all local choices exist for every group of type Ru. -/
theorem local_choices_of_typeRu (h : IsTypeRu G) :
    ∃ d : LocalSetup G, Nonempty (Centralizers.Choices d) := by
  obtain ⟨d⟩ := h.nonempty_localSetup
  exact ⟨d, exists_choices d⟩

end CFSG.Quasithin.ChapterJ.SourceCompletion
