module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Intersection
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.Selection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.LocalFreeness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Torus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.RegularAction
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct


/-!
# The numerical endpoint of two-core growth

This proves the two numerical conclusions in the last paragraph of GLS,
Volume 4, Chapter 2, Proposition 17.6, from the original local cyclic-Sylow
hypothesis and the explicit counting data. The actual local split torus
lies in the inverted set and centralizes the marked involution `u`.
Sharp transitivity makes it free on distinguished involutions; the local
four-group argument in `CoreGrowth.LocalFreeness` makes it free on all
nonidentity elements of `O₂(M)`, without global involution classification.

Orbit counting and the binary-power remainder identity give a power of
`q`. Generation forces the inverted set to contain an element outside
`C_G(u)`, so its cardinality exceeds the torus order `q−1`. Its regular
orbit of distinguished involutions embeds in the nonidentity core,
yielding the strict lower bound. This includes the trivial torus at `q=2`.

The earlier conditional two-class route is preserved. Construction of
`TwoCoreCountingData` and the local cyclic-Sylow theorem remain with their
source owners; neither is asserted here.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Ambient involution classification descends through genuine Sylow fusion.
Normality is inside `M`, where the inverter excludes the two-point class. -/
public theorem TwoCoreCountingData.core_involutions_mem_of_two_classes
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hclasses : ∀ v : G, orderOf v = 2 → v ∈ Z ∨ IsConj v ((d.u : M) : G)) :
    ∀ v : pCore 2 M, orderOf v = 2 → ((v : M) : G) ∈ Z := by
  intro v hv
  have hvG : orderOf ((v : M) : G) = 2 := by simpa using hv
  rcases hclasses v hvG with hz | hc
  · exact hz
  · have hi {x : G} (hx : orderOf x = 2) : IsInvolution x := by
      obtain ⟨hs, hn⟩ := orderOf_eq_prime_iff.mp hx
      exact ⟨hn, hs⟩
    obtain ⟨S, hSM, hf⟩ := r.fusion
    have huG : orderOf ((d.u : M) : G) = 2 := by simpa using d.u_order
    obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf (hi hvG) (hi huG)
      (v : M).property (d.u : M).property hc
    have hm' : m * (v : M) * m⁻¹ = (d.u : M) := Subtype.ext hm
    have hu : (d.u : M) ∈ pCore 2 M := hm' ▸
      (inferInstance : (pCore 2 M).Normal).conj_mem v v.property m
    have he := Subgroup.disjoint_def.mp (d.disjoint_twoCore h hlocal) d.u.property hu
    have he' : d.u = 1 := Subtype.ext he
    have ho := d.u_order
    rw [he', orderOf_one] at ho
    omega

private theorem card_nonidentity (P : Type*) [Group P] [Finite P] :
    Nat.card {x : P // x ≠ 1} = Nat.card P - 1 := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

private theorem core_commute_eq_one
    (hinvol : ∀ v : pCore 2 M, orderOf v = 2 → ((v : M) : G) ∈ Z)
    (A : Subgroup M)
    (hfree : ∀ a : A, a ≠ 1 → ∀ z : M, (z : G) ∈ Z → ¬ Commute (a : M) z)
    (a : A) (ha : a ≠ 1) (v : pCore 2 M) (hv : Commute (a : M) (v : M)) : v = 1 := by
  by_contra hvne
  let C : Subgroup (pCore 2 M) := (Subgroup.centralizer ({(a : M)} : Set M)).comap
    (pCore 2 M).subtype
  have hvC : v ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hv.symm.eq
  let _ : Nontrivial C := ⟨⟨⟨v, hvC⟩, 1, fun he => hvne (congrArg Subtype.val he)⟩⟩
  have hC : IsPGroup 2 C := (pCore_isPGroup (p := 2) (G := M)).to_subgroup C
  obtain ⟨n, hn, hcard⟩ := hC.nontrivial_iff_card.mp inferInstance
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  have hyP : orderOf (y : pCore 2 M) = 2 := by simpa using hy
  have hz := hinvol y hyP
  exact hfree a ha y hz (Subgroup.mem_centralizer_singleton_iff.mp y.property).symm

private theorem core_card_sub_one_dvd
    (A : Subgroup M)
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : pCore 2 M,
      Commute (a : M) (v : M) → v = 1) :
    Nat.card A ∣ Nat.card (pCore 2 M) - 1 := by
  classical
  let P := pCore 2 M
  let f : A →* MulAut P := MulAut.conjNormal.comp A.subtype
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P f
  let X := {v : P // v ≠ 1}
  let _ : MulAction A X := {
    smul a v := ⟨f a v, fun he => v.property ((f a).injective (he.trans (map_one (f a)).symm))⟩
    one_smul v := by apply Subtype.ext; exact one_smul A (v : P)
    mul_smul a b v := by apply Subtype.ext; exact mul_smul a b (v : P) }
  have hstab (v : X) : MulAction.stabilizer A v = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply Subgroup.mem_bot.mpr
    by_contra hane
    have he : f a (v : P) = v := congrArg Subtype.val ha
    have heM : (a : M) * ((v : P) : M) * (a : M)⁻¹ = ((v : P) : M) :=
      congrArg Subtype.val he
    have hc : Commute (a : M) ((v : P) : M) := mul_inv_eq_iff_eq_mul.mp heM
    exact v.property (hfree a hane v hc)
  have hcount := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd
    (G := A) (X := X) hstab)
  rw [Nat.card_prod, card_nonidentity] at hcount
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by simpa [Nat.mul_comm] using hcount⟩

private theorem binary_power_of_sub_one_dvd {q m : ℕ}
    (hq : ∃ n : ℕ, q = 2 ^ n) (hm : ∃ e : ℕ, m = 2 ^ e)
    (hdiv : q - 1 ∣ m - 1) : ∃ k : ℕ, m = q ^ k := by
  obtain ⟨n, rfl⟩ := hq
  obtain ⟨e, rfl⟩ := hm
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hmod
  have hone : 2 ^ (e % n) = 1 := by
    have hp : 0 < 2 ^ (e % n) := pow_pos (by decide) _
    omega
  have hzero : e % n = 0 := by
    have heq : 2 ^ (e % n) = 2 ^ 0 := by simpa using hone
    exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) heq
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hzero
  exact ⟨k, by rw [hk, pow_mul]⟩

private theorem TwoCoreCountingData.core_growth_of_free_torus
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M)
    (A : Subgroup M) (hA : Nat.card A = d.q - 1)
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : pCore 2 M,
      Commute (a : M) (v : M) → v = 1)
    (htrace : d.q - 1 < Nat.card {z : M // (z : G) ∈ Z}) :
    d.q < Nat.card (pCore 2 M) ∧ ∃ k : ℕ, Nat.card (pCore 2 M) = d.q ^ k := by
  have hdiv := core_card_sub_one_dvd A hfree
  rw [hA] at hdiv
  have hpower := binary_power_of_sub_one_dvd d.binary
    (IsPGroup.exists_card_eq (pCore_isPGroup (p := 2) (G := M))) hdiv
  refine ⟨?_, hpower⟩
  obtain ⟨n, hdeg⟩ := d.binary_degree
  let f : {z : M // (z : G) ∈ Z} → {x : pCore 2 M // x ≠ 1} := fun z =>
    ⟨⟨z, distinguished_mem_twoCore_of_binary_degree h ha hdeg z.property z.val.property⟩,
      fun he => (h.involutions z z.property).ne_one
        (congrArg (fun x : pCore 2 M => ((x : M) : G)) he)⟩
  have hf : Function.Injective f := by
    intro z w he
    exact Subtype.ext (congrArg (fun x : {x : pCore 2 M // x ≠ 1} => ((x : pCore 2 M) : M)) he)
  have hbound := Nat.card_le_card_of_injective f hf
  rw [card_nonidentity] at hbound
  have hq := d.one_lt
  omega

private theorem TwoCoreCountingData.trace_growth_of_regular_inverted_set
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M)
    (hg : ResidualGeneration Z M)
    (hgen : (Subgroup.closure (coreGrowthInvertedSet M d.t)).map M.subtype =
      residualCommutator M d.t)
    (hregular : ∀ z : M, ∀ hz : (z : G) ∈ Z,
      Function.Bijective (coreGrowthConjugate h d.t z hz))
    (A : Subgroup M) (hA : Nat.card A = d.q - 1)
    (hAI : (A : Set M) ⊆ coreGrowthInvertedSet M d.t)
    (hAC : A.map M.subtype ≤ Subgroup.centralizer ({((d.u : M) : G)} : Set G)) :
    d.q - 1 < Nat.card {z : M // (z : G) ∈ Z} := by
  classical
  have hnot : ¬ ∀ i ∈ coreGrowthInvertedSet M d.t,
      (i : G) ∈ Subgroup.centralizer ({((d.u : M) : G)} : Set G) := by
    intro hI
    have hK : residualCommutator M d.t ≤
        Subgroup.centralizer ({((d.u : M) : G)} : Set G) := by
      rw [← hgen, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      exact hI
    have huG : orderOf ((d.u : M) : G) = 2 := by simpa using d.u_order
    have hu : IsInvolution ((d.u : M) : G) := by
      obtain ⟨hs, hn⟩ := orderOf_eq_prime_iff.mp huG
      exact ⟨hn, hs⟩
    exact residualCommutator_not_le_involution_centralizer h r hg
      d.z_mem d.z.property d.t_mem d.t_not_mem hu
      d.commutes_z.symm d.commutes_t.symm hK
  let f : A → coreGrowthInvertedSet M d.t := fun a => ⟨a, hAI a.property⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : coreGrowthInvertedSet M d.t => (x : M)) he)
  have hns : ¬ Function.Surjective f := by
    intro hs
    apply hnot
    intro i hi
    obtain ⟨a, ha⟩ := hs ⟨i, hi⟩
    have he : (a : M) = i := congrArg Subtype.val ha
    exact he ▸ hAC (Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩)
  have hlt : Nat.card A < Nat.card (coreGrowthInvertedSet M d.t) := by
    let _ : Fintype A := Fintype.ofFinite A
    let _ : Fintype (coreGrowthInvertedSet M d.t) := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective f hf hns
  have hcard : Nat.card (coreGrowthInvertedSet M d.t) =
      Nat.card {w : M // (w : G) ∈ Z} :=
    Nat.card_congr (Equiv.ofBijective _ (hregular d.z d.z_mem))
  rwa [hA, hcard] at hlt

omit [Finite G] in
private theorem inverted_subgroup_free_on_distinguished
    (h : IsProductDisconnected Z M) (t : G)
    (hregular : ∀ z : M, ∀ hz : (z : G) ∈ Z,
      Function.Bijective (coreGrowthConjugate h t z hz))
    (A : Subgroup M) (hAI : (A : Set M) ⊆ coreGrowthInvertedSet M t) :
    ∀ a : A, a ≠ 1 → ∀ z : M, (z : G) ∈ Z → ¬ Commute (a : M) z := by
  intro a hane z hz hc
  have he : coreGrowthConjugate h t z hz ⟨a, hAI a.property⟩ =
      coreGrowthConjugate h t z hz ⟨1, one_mem_coreGrowthInvertedSet M t⟩ := by
    apply Subtype.ext
    change (a : M) * z * (a : M)⁻¹ = 1 * z * (1 : M)⁻¹
    rw [hc.eq]
    simp [mul_assoc]
  have he' := congrArg Subtype.val ((hregular z hz).injective he)
  exact hane (Subtype.ext he')

/-- Conditional assembly from the actual inverted set, a compatible torus,
and global two-class fusion. The original interface is retained; the local
cyclic-Sylow route below discharges freeness without the two-class premise. -/
public theorem TwoCoreCountingData.core_growth_of_regular_inverted_set
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hclasses : ∀ v : G, orderOf v = 2 → v ∈ Z ∨ IsConj v ((d.u : M) : G))
    (hgen : (Subgroup.closure (coreGrowthInvertedSet M d.t)).map M.subtype =
      residualCommutator M d.t)
    (hregular : ∀ z : M, ∀ hz : (z : G) ∈ Z,
      Function.Bijective (coreGrowthConjugate h d.t z hz))
    (A : Subgroup M) (hA : Nat.card A = d.q - 1)
    (hAI : (A : Set M) ⊆ coreGrowthInvertedSet M d.t)
    (hAC : A.map M.subtype ≤ Subgroup.centralizer ({((d.u : M) : G)} : Set G)) :
    d.q < Nat.card (pCore 2 M) ∧ ∃ k : ℕ, Nat.card (pCore 2 M) = d.q ^ k := by
  have hinvol := d.core_involutions_mem_of_two_classes h r hlocal hclasses
  have hfree := inverted_subgroup_free_on_distinguished h d.t hregular A hAI
  exact d.core_growth_of_free_torus h ha A hA
    (core_commute_eq_one hinvol A hfree)
    (d.trace_growth_of_regular_inverted_set h r hg hgen hregular A hA hAI hAC)

/-- The core-growth conclusions of Proposition 17.6 from the original
local cyclic-Sylow and counting inputs. The marked torus, its action and
freeness are all constructed; no global involution-class premise is needed. -/
public theorem TwoCoreCountingData.core_growth_of_local_cyclicSylow
    (d : TwoCoreCountingData Z M) (h : MinimalCounterexample Z M)
    (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (_hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    d.q < Nat.card (pCore 2 M) ∧ ∃ k : ℕ, Nat.card (pCore 2 M) = d.q ^ k := by
  obtain ⟨A, _, hA, hAI, _, hAC⟩ :=
    d.exists_local_split_torus h.disconnected r (fun Y hY => (hlocal Y hY).1)
  obtain ⟨hgen, hregular⟩ := d.inverted_set_generation_and_regularity h hlocal
  have hfree := inverted_subgroup_free_on_distinguished h.disconnected d.t hregular A hAI
  apply d.core_growth_of_free_torus h.disconnected ha A hA ?_
    (d.trace_growth_of_regular_inverted_set h.disconnected r hg hgen hregular A hA hAI hAC)
  intro a hane v hav
  have hau : Commute (a : M) (d.u : M) := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hAC (Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩))
  exact d.core_commute_eq_one_of_local_cyclicSylow h.disconnected ha hlocal
    a hau (hfree a hane) v hav

end BenderSuzuki.ZD
