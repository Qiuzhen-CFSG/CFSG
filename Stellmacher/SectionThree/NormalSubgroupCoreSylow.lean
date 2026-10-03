module

public import Stellmacher.SectionThree.NormalSubgroupCoreControl

/-!
# The 2-core is Sylow in a proper normal local subgroup

Let `P ∈ PSet ⊤ S` be solvable, and let `O₂(P) ≤ K ◁ P`. If `KS`
is proper in `P`, then `O₂(P)` is a Sylow 2-subgroup of `K`. This
is the Sylow consequence of (3.3) used for the centralizer of `V` in (4.6).

The imported core-control theorem bounds `K ∩ S` by `O₂(P)`. Given a
Sylow subgroup of `K`, embed it in a Sylow subgroup of `P` and conjugate
that subgroup to the fixed `S`. Normality preserves both `K` and
`O₂(P)`, so the bound on the fixed Sylow intersection applies and
transfers back. Conversely the normal 2-subgroup `O₂(P)` lies in every
Sylow subgroup of `K`.

Source: `refs/latex/stellmacher-n-group.tex`, (3.3) and the second
paragraph of the proof of (4.6).
-/

open scoped Pointwise

namespace Stellmacher.SectionThree

universe u

/-- The 2-core is Sylow in a normal subgroup that fails to generate with the fixed Sylow. -/
public theorem twoCore_sylow_of_normal_not_generate
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P K : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (hKP : K ≤ P)
    (hKN : (K.subgroupOf P).Normal) (hnot : ¬ P ≤ K ⊔ S)
    (hcoreK : twoCoreAmbient P ≤ K) :
    IsSylowSubgroupIn (twoCoreAmbient P) K := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcontrol := normal_inf_sylow_le_twoCore S h P K hP hsolv hKP hKN hnot
  obtain ⟨SP, hSP⟩ := hP.1.2.1
  let T : Sylow 2 K := Classical.choice (Sylow.nonempty (p := 2) (G := K))
  let R : Subgroup G := (T : Subgroup K).map K.subtype
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRP : R ≤ P := hRK.trans hKP
  have hR2 : IsPGroup 2 R := T.isPGroup'.map K.subtype
  have hRp2 : IsPGroup 2 (R.subgroupOf P) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  obtain ⟨U, hRU⟩ := hRp2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P U SP
  have hRcore : R ≤ twoCoreAmbient P := by
    intro r hr
    let rP : P := ⟨r, hRP hr⟩
    have hrU : rP ∈ (U : Subgroup P) := hRU hr
    have hgrSP : g * rP * g⁻¹ ∈ (SP : Subgroup P) := by
      rw [← hg]
      change g * rP * g⁻¹ ∈ (U : Subgroup P).map (MulAut.conj g).toMonoidHom
      exact ⟨rP, hrU, rfl⟩
    have hgrS : ((g * rP * g⁻¹ : P) : G) ∈ S := by
      rw [← hSP]
      exact ⟨g * rP * g⁻¹, hgrSP, rfl⟩
    have hgrK : ((g * rP * g⁻¹ : P) : G) ∈ K :=
      hKN.conj_mem rP (hRK hr) g
    have hgrCore := hcontrol ⟨hgrK, hgrS⟩
    obtain ⟨t, ht, heq⟩ := hgrCore
    have hteq : t = g * rP * g⁻¹ := P.subtype_injective heq
    have hgrCoreP : g * rP * g⁻¹ ∈ pCore 2 P := by
      simpa [hteq] using ht
    have hrCoreP : rP ∈ pCore 2 P := by
      have hback := (pCore_normal (p := 2) (G := P)).conj_mem
        (g * rP * g⁻¹) hgrCoreP g⁻¹
      simpa [mul_assoc] using hback
    exact ⟨rP, hrCoreP, rfl⟩
  have hnormalP : ((twoCoreAmbient P).subgroupOf P).Normal := by
    rw [twoCoreAmbient, subgroupOf_map_subtype_eq]
    infer_instance
  have hnorm : P ≤ Subgroup.normalizer (twoCoreAmbient P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hnormalP
  have hnormalK : ((twoCoreAmbient P).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreK).mpr (hKP.trans hnorm)
  have hcore2K : IsPGroup 2 ((twoCoreAmbient P).subgroupOf K) :=
    ((pCore_isPGroup (p := 2) (G := P)).map P.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hcoreK).symm
  have hcoreR : twoCoreAmbient P ≤ R := by
    let _ : ((twoCoreAmbient P).subgroupOf K).Normal := hnormalK
    rw [← Subgroup.map_subgroupOf_eq_of_le hcoreK]
    exact Subgroup.map_mono (hcore2K.le_sylow_of_normal T)
  exact ⟨T, le_antisymm hRcore hcoreR⟩

end Stellmacher.SectionThree
