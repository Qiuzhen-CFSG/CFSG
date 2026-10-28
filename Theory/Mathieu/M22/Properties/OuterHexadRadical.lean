module

public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The hexad two-core in the full M₂₂ design group

Restrict the actual degree-22 permutations to the six points of a hexad.
The pointwise kernel in the full design group is exactly the included inner
kernel. For the standard hexad, the odd design involution induces a
transposition, whereas the inner stabilizer induces A₆. The design-group
normal form therefore excludes outer elements from the pointwise kernel.
Hexad conjugacy transports this fact to every hexad.

For every subgroup between the inner and full hexad stabilizers, the
restriction image is A₆ or S₆. Both have trivial two-core, so the restriction
kernel, already known to be a two-group, is precisely the intrinsic two-core.
All normality in this calculation is relative to the acting subgroup.

This is the native radical calculation used in Aschbacher–Smith 13.8.21(2),
printed p.956 (PDF p.973), for the subgroup K₁T in the M₂₂ case. Transport
from a source group to the concrete design action belongs to the consumer.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22OuterHexad
open Subgroup M22ValueBound.Concrete
open scoped Pointwise

/-- The actual restriction of a design automorphism to a set it stabilizes. -/
noncomputable def setAction (B : Finset (Fin 22)) :
    MulAction.stabilizer m22DesignAut B →* Equiv.Perm B where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

/-- Restriction to the six hexad points, using the same labels as the inner action. -/
noncomputable def action {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer m22DesignAut B →* Equiv.Perm (Fin 6) :=
  (m22HexadLabels hB).permCongrHom.toMonoidHom.comp (setAction B)

private noncomputable def innerStabilizer (B : Finset (Fin 22)) :
    MulAction.stabilizer M22 B →* MulAction.stabilizer m22DesignAut B where
  toFun g := ⟨inclusion g.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def oddStabilizer : MulAction.stabilizer m22DesignAut m22Hexad123 :=
  ⟨⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩, by
    change m22OddPairSwap • m22Hexad123 = m22Hexad123
    decide +kernel⟩

private theorem setAction_odd : setAction m22Hexad123 oddStabilizer =
    Equiv.swap ⟨18, by decide⟩ ⟨20, by decide⟩ := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change m22OddPairSwap a.val =
    (Equiv.swap (⟨18, by decide⟩ : m22Hexad123) ⟨20, by decide⟩ a).val
  revert a
  decide +kernel

private theorem action_odd_sign : Equiv.Perm.sign (action m22Hexad123_mem oddStabilizer) = -1 := by
  change Equiv.Perm.sign ((m22HexadLabels m22Hexad123_mem).permCongr
    (setAction m22Hexad123 oddStabilizer)) = -1
  rw [Equiv.Perm.sign_permCongr, setAction_odd]
  exact Equiv.Perm.sign_swap (by decide)

/-- The restriction kernel consists exactly of the pointwise hexad fixers. -/
theorem mem_action_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer m22DesignAut B) :
    g ∈ (action hB).ker ↔ ∀ a ∈ B, (g : m22DesignAut) • a = a := by
  rw [show (action hB).ker = (setAction B).ker from
    MonoidHom.ker_mulEquiv_comp _ (m22HexadLabels hB).permCongrHom]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨a, ha⟩)
  · intro h
    exact Equiv.ext (fun a => Subtype.ext (h a.val a.property))

private theorem standard_fixer_inner (g : m22DesignAut)
    (hg : ∀ a ∈ m22Hexad123, g • a = a) : g ∈ inner := by
  have hgs : g ∈ MulAction.stabilizer m22DesignAut m22Hexad123 := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    rwa [hg a ha]
  let gs : MulAction.stabilizer m22DesignAut m22Hexad123 := ⟨g, hgs⟩
  have hact : action m22Hexad123_mem gs = 1 :=
    (mem_action_ker m22Hexad123_mem gs).mpr hg
  obtain ⟨h, hh | hh⟩ := m22DesignAut_normalForm g
  · change g.val ∈ M22
    rw [hh]
    exact h.property
  · have he : g = inclusion h * oddStabilizer.val := Subtype.ext hh
    have hs : h ∈ MulAction.stabilizer M22 m22Hexad123 := by
      change inclusion h ∈ MulAction.stabilizer m22DesignAut m22Hexad123
      have hi : inclusion h = g * oddStabilizer.val⁻¹ := by rw [he]; group
      rw [hi]
      exact (MulAction.stabilizer m22DesignAut m22Hexad123).mul_mem hgs
        ((MulAction.stabilizer m22DesignAut m22Hexad123).inv_mem oddStabilizer.property)
    let hs' : MulAction.stabilizer M22 m22Hexad123 := ⟨h, hs⟩
    have he' : gs = innerStabilizer _ hs' * oddStabilizer := Subtype.ext he
    have heven : Equiv.Perm.sign (action m22Hexad123_mem (innerStabilizer _ hs')) = 1 := by
      apply Equiv.Perm.mem_alternatingGroup.mp
      rw [← m22HexadAction_range m22Hexad123_mem]
      exact ⟨hs', rfl⟩
    have hc := congrArg (fun x => Equiv.Perm.sign (action m22Hexad123_mem x)) he'
    rw [hact, map_one, map_mul, map_mul, heven, action_odd_sign, one_mul] at hc
    simp at hc

private theorem fixer_inner {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : m22DesignAut) (hg : ∀ a ∈ B, g • a = a) : g ∈ inner := by
  obtain ⟨u, hu⟩ := exists_smul_m22Hexad123_eq hB
  let v := inclusion u
  have hx : v⁻¹ * g * v ∈ inner := by
    apply standard_fixer_inner
    intro a ha
    have hm : u • a ∈ B := hu ▸ Finset.smul_mem_smul_finset ha
    change (v⁻¹ * g * v) • a = a
    rw [mul_smul, mul_smul]
    change v⁻¹ • (g • (u • a)) = a
    rw [hg _ hm]
    exact inv_smul_smul v a
  have hn := (inferInstance : inner.Normal).conj_mem _ hx v
  simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] using hn

/-- The full pointwise kernel is the included inner pointwise kernel. -/
theorem action_ker_map {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (action hB).ker.map (MulAction.stabilizer m22DesignAut B).subtype =
      (m22HexadPointwiseKernel B).map inclusion := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hf := (mem_action_ker hB x).mp hx
    have hi := fixer_inner hB x.val hf
    refine ⟨⟨x.val.val, hi⟩, ?_, rfl⟩
    exact (mem_m22HexadPointwiseKernel B _).mpr hf
  · rintro ⟨x, hx, rfl⟩
    have hf := (mem_m22HexadPointwiseKernel B x).mp hx
    have hs := m22HexadPointwiseKernel_le B hx
    exact ⟨innerStabilizer B ⟨x, hs⟩, (mem_action_ker hB _).mpr hf, rfl⟩

private theorem normal_two_symmetric_six_eq_bot (P : Subgroup (Equiv.Perm (Fin 6)))
    [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  by_contra hn
  have hnt : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hdiv : 360 ∣ Nat.card P := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 360) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

private theorem normal_two_alternating_six_eq_bot
    (P : Subgroup (alternatingGroup (Fin 6))) [P.Normal]
    (hP : IsPGroup 2 P) : P = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := P) with he | he
  · exact he
  · have hc : Nat.card P = 360 := by
      rw [he, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hthree : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 360)
    exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree))

private theorem intermediate_six (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : alternatingGroup (Fin 6) ≤ H) :
    H = alternatingGroup (Fin 6) ∨ H = ⊤ := by
  have hd : H.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le hH
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact Or.inr (index_eq_one.mp he)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two he)

private theorem core_le_ker {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 6)) (hf : alternatingGroup (Fin 6) ≤ f.range) :
    pCore 2 G ≤ f.ker := by
  rcases intermediate_six f.range hf with hr | hr
  · let fA : G →* alternatingGroup (Fin 6) :=
      f.codRestrict _ (fun g => hr ▸ (show f g ∈ f.range from ⟨g, rfl⟩))
    have hsur : Function.Surjective fA := by
      intro y
      obtain ⟨x, hx⟩ := (show y.val ∈ f.range from hr.symm ▸ y.property)
      exact ⟨x, Subtype.ext hx⟩
    have : ((pCore 2 G).map fA).Normal := (inferInstance : (pCore 2 G).Normal).map fA hsur
    have hle := (Subgroup.map_eq_bot_iff _).mp
      (normal_two_alternating_six_eq_bot _ (pCore_isPGroup.map fA))
    intro g hg
    exact congrArg Subtype.val (show fA g = 1 from hle hg)
  · have hsur := MonoidHom.range_eq_top.mp hr
    have : ((pCore 2 G).map f).Normal := (inferInstance : (pCore 2 G).Normal).map f hsur
    exact (Subgroup.map_eq_bot_iff _).mp
      (normal_two_symmetric_six_eq_bot _ (pCore_isPGroup.map f))

/-- Every intermediate hexad stabilizer has the same two-core, including
subgroups containing outer design automorphisms. -/
theorem radical_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (R : Subgroup m22DesignAut)
    (hinner : (MulAction.stabilizer M22 B).map inclusion ≤ R)
    (hR : R ≤ MulAction.stabilizer m22DesignAut B) :
    R.pCoreIn 2 = (m22HexadPointwiseKernel B).map inclusion := by
  let K := (m22HexadPointwiseKernel B).map inclusion
  have hKR : K ≤ R := (Subgroup.map_mono (m22HexadPointwiseKernel_le B)).trans hinner
  let f : R →* Equiv.Perm (Fin 6) := (action hB).comp (Subgroup.inclusion hR)
  have hf : alternatingGroup (Fin 6) ≤ f.range := by
    rw [← m22HexadAction_range hB]
    rintro y ⟨g, rfl⟩
    exact ⟨⟨inclusion g.val, hinner ⟨g.val, g.property, rfl⟩⟩, rfl⟩
  have hk : f.ker = K.subgroupOf R := by
    ext x
    change (Subgroup.inclusion hR x) ∈ (action hB).ker ↔ x.val ∈ K
    constructor
    · intro hx
      change x.val ∈ (m22HexadPointwiseKernel B).map inclusion
      rw [← action_ker_map hB]
      exact ⟨Subgroup.inclusion hR x, hx, rfl⟩
    · intro hx
      change x.val ∈ (m22HexadPointwiseKernel B).map inclusion at hx
      rw [← action_ker_map hB] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (show y = Subgroup.inclusion hR x from Subtype.ext he) ▸ hy
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact ((m22HexadPointwiseKernel_isTwoGroup hB).map inclusion).comap_subtype
  have hc : pCore 2 R = f.ker :=
    le_antisymm (core_le_ker f hf) (le_sSup ⟨inferInstance, hkp⟩)
  change (pCore 2 R).map R.subtype = K
  rw [hc, hk, map_subgroupOf_eq_of_le hKR]

end Sporadic.Mathieu.M22OuterHexad
