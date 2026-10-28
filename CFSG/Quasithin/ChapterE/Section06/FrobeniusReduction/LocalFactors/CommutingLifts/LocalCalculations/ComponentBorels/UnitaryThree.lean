module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.Defs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals.Quotients
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Commuting odd actions on the PSU₃ Borel

For q = 2ⁿ, the actual projective unitary Sylow normalizer has a cyclic
torus complement. Matrix form transport and Sylow conjugacy identify the
normalizer at the supplied Sylow subgroup. The actual intersection B = L ∩ M
is a proper Sylow overgroup, so B/O₂(B) is cyclic as well.

The action of B on V has odd order and therefore kills O₂(B). Every subgroup
of the cyclic quotient is invariant under its automorphisms. In particular,
an actor normalizing B preserves the image of X in B/O₂(B). If its induced
action on V commutes with X's, faithfulness on X forces it to fix that image
pointwise. Thus [A,X] ≤ O₂(B), and the original X is the required witness.

The model transport retains the matrix-field order q², Hermitian involution
x ↦ x^q, and the projective scalar kernel. The full centralizer C_B(V) need
not be a two-group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3b)
and the factor-count paragraph of E.6.25, printed pp.249–250,255;
Huppert II.10.12 for the model Borel.
-/

public section

open Subgroup
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.Unitary
open BenderSuzuki.MatrixGroups
open scoped Matrix

private theorem cyclic_subgroup_quotient {G : Type*} [Group G]
    (N B : Subgroup G) (hB : B ≤ N) [IsCyclic (N ⧸ pCore 2 N)] :
    IsCyclic (B ⧸ pCore 2 B) := by
  let f : B →* N ⧸ pCore 2 N := (QuotientGroup.mk' _).comp (inclusion hB)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 N)).ker).comap (inclusion hB))
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective (inclusion hB) (inclusion_injective hB)
  have hle : f.ker ≤ pCore 2 B := le_sSup ⟨inferInstance, hk⟩
  let _ : IsCyclic (B ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  let g := QuotientGroup.map f.ker (pCore 2 B) (MonoidHom.id B) hle
  apply isCyclic_of_surjective g
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) y
  exact ⟨QuotientGroup.mk' f.ker b, rfl⟩

private theorem normalizer_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Subgroup G) :
    Nonempty (normalizer (S : Set G) ≃*
      normalizer (S.map e.toMonoidHom : Set H)) :=
  ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq S e))⟩

private theorem cyclic_normalizer_quotient_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Subgroup G)
    [IsCyclic (normalizer (S : Set G) ⧸ pCore 2 (normalizer (S : Set G)))] :
    IsCyclic (normalizer (S.map e.toMonoidHom : Set H) ⧸
      pCore 2 (normalizer (S.map e.toMonoidHom : Set H))) := by
  obtain ⟨f⟩ := normalizer_equiv e S
  exact isCyclic_of_surjective (twoCoreQuotientEquiv f).toMonoidHom
    (twoCoreQuotientEquiv f).surjective

private theorem unitary_normalizer_quotient {H : Type*} [Group H] [Finite H]
    {n : ℕ} (iso : ClassicalGroup.IsPSU H 3 (2 ^ n)) (hn : 0 < n)
    (S : Sylow 2 H) :
    IsCyclic (normalizer (S : Set H) ⧸ pCore 2 (normalizer (S : Set H))) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := iso
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  let J₀ := FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective _ (suProjection_surjective J₀)
  obtain ⟨_, _, P, ⟨D, hD, _, hcyc, hdis, hsup⟩, _⟩ :=
    standard_psu_borel_data J₀ n hn hcard hconj rfl
  let _ : IsCyclic D := hcyc
  let N := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J₀))
  let eqv := quotientTorusEquiv N P D hD (twoCore_sylow_normalizer P) hdis hsup
  let _ : IsCyclic (N ⧸ pCore 2 N) :=
    isCyclic_of_injective eqv.toMonoidHom eqv.injective
  let R : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J₀) P R
  have hm : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J₀)).map
      (MulAut.conj g).toMonoidHom = (R : Subgroup _) := congrArg Sylow.toSubgroup hg
  have hc := cyclic_normalizer_quotient_map (MulAut.conj g) (P : Subgroup _)
  rw [hm] at hc
  have hc' : IsCyclic (normalizer ((S : Subgroup H).map e.toMonoidHom :
      Set (ProjectiveSpecialUnitaryMatrixGroup J₀)) ⧸ pCore 2
      (normalizer ((S : Subgroup H).map e.toMonoidHom :
        Set (ProjectiveSpecialUnitaryMatrixGroup J₀)))) := hc
  let _ := hc'
  obtain ⟨f⟩ := normalizer_equiv e (S : Subgroup H)
  exact isCyclic_of_injective (twoCoreQuotientEquiv f).toMonoidHom
    (twoCoreQuotientEquiv f).injective

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components Components.BorelActions
variable {G : Type*} [Group G] [Finite G]

/-- The actual component intersection has cyclic quotient by its intrinsic
two-core. It is placed in the model's Sylow normalizer using proper-overgroup
uniqueness, and cyclicity descends through the genuine subgroup inclusion. -/
theorem componentBorel_quotient_unitary_three
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    IsCyclic ((L ⊓ M : Subgroup G) ⧸ pCore 2 (L ⊓ M : Subgroup G)) := by
  have hQM : Q ≤ M := by rw [hQ]; exact inf_le_left.trans h.sylow_le
  have hSB : (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L := by
    intro x hx
    have hh : (x : G) ∈ L ⊓ Q := hS ▸ mem_map_of_mem L.subtype hx
    exact ⟨x.property, hQM hh.2⟩
  have hBproper : (L ⊓ M).subgroupOf L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hLM : L ≤ M := by
      intro x hx
      have hh : (⟨x, hx⟩ : L) ∈ (L ⊓ M).subgroupOf L := he ▸ mem_top _
      exact hh.2
    have hB : L ⊓ M = L := inf_eq_left.mpr hLM
    have hnorm : L ≤ normalizer (V : Set G) :=
      hB ▸ component_intersection_normalizes h hU hL.1
    let _ := component_quasisimple hL
    let e := (subgroupOfEquivOfLe hnorm).symm
    let _ : Group.IsPerfect (L.subgroupOf (normalizer (V : Set G))) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let _ : Group.IsPerfect (inducedAutomizer V L) := Group.IsPerfect.map _
    obtain ⟨a⟩ : Nonempty (inducedAutomizer V L ≃* Multiplicative (ZMod (2 ^ n - 1))) :=
      hB ▸ b.action
    let _ : Group.IsPerfect (Multiplicative (ZMod (2 ^ n - 1))) :=
      Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    have hp : 4 ≤ 2 ^ n := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    let : NeZero (2 ^ n - 1) := ⟨by omega⟩
    have hc : Nat.card (Multiplicative (ZMod (2 ^ n - 1))) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hc
    omega
  have hs : RankOneSylowFacts S := by
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := iso
    exact rankOneSylowFacts_of_equiv S e
      (rankOneSylowFacts_psu3 J n (by omega) hcard hconj _)
  let _ := unitary_normalizer_quotient iso (by omega : 0 < n) S
  let _ := cyclic_subgroup_quotient _ _ (hs.unique_maximal _ hSB hBproper)
  let eB := subgroupOfEquivOfLe (inf_le_left : L ⊓ M ≤ L)
  exact isCyclic_of_surjective (twoCoreQuotientEquiv eB).toMonoidHom
    (twoCoreQuotientEquiv eB).surjective

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts

private theorem cyclic_subgroup_invariant {H : Type*} [Group H] [IsCyclic H]
    (X : Subgroup H) (a : MulAut H) {x : H} (hx : x ∈ X) : a x ∈ X := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  obtain ⟨k, hk⟩ := hg (a g)
  obtain ⟨m, rfl⟩ := hg x
  have he : a (g ^ m) = (g ^ m) ^ k := by
    rw [map_zpow, ← hk, ← zpow_mul, mul_comm k m, zpow_mul]
  rw [he]
  exact X.zpow_mem hx k

private theorem core_le_ker_of_odd_target {H D : Type*} [Group H] [Group D]
    [Finite D] (f : H →* D) (ho : Odd (Nat.card D)) : pCore 2 H ≤ f.ker := by
  intro x hx
  obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := H) ⟨x, hx⟩
  have hp : f x ^ (2 ^ k) = 1 := by
    have hh : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    simpa only [map_pow, map_one] using congrArg f hh
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_left.pow_left k) (orderOf_dvd_of_pow_eq_one hp)
    (orderOf_dvd_natCard (f x)))

private theorem quotient_fixed_of_faithful_image {H D : Type*} [Group H] [Group D]
    [IsCyclic (H ⧸ pCore 2 H)]
    (f : H →* D) (X : Subgroup H) (hk : pCore 2 H ≤ f.ker)
    (hf : Function.Injective (f.comp X.subtype)) (a : MulAut H)
    (hfix : ∀ x ∈ X, f (a x) = f x) {x : H} (hx : x ∈ X) :
    QuotientGroup.mk' (pCore 2 H) (a x) = QuotientGroup.mk' (pCore 2 H) x := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let aq := quotientAut (pCore 2 H) a
  have hm : aq (q x) ∈ X.map q :=
    cyclic_subgroup_invariant (X.map q) aq (mem_map_of_mem q hx)
  obtain ⟨y, hy, he⟩ := hm
  change q y = quotientAut (pCore 2 H) a (QuotientGroup.mk' (pCore 2 H) x) at he
  rw [quotientAut_apply_mk] at he
  have hfy : f y = f x := by
    have hh := congrArg (QuotientGroup.lift (pCore 2 H) f hk) he
    change f y = f (a x) at hh
    exact hh.trans (hfix x hx)
  have hyx : y = x := congrArg Subtype.val (hf (a₁ := ⟨y, hy⟩) (a₂ := ⟨x, hx⟩) hfy)
  subst y
  exact he.symm

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components
variable {G : Type*} [Group G] [Finite G]

private theorem componentBorel_lift_of_cyclic_quotient
    {K : GroupClass} {T : Sylow 2 G} {M V U L X : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hXL : X ≤ L) (b : BorelAlternative M V U L n) (hn : 0 < n)
    [IsCyclic ((L ⊓ M : Subgroup G) ⧸ pCore 2 (L ⊓ M : Subgroup G))] :
    ComponentBorelLiftConclusion M V U L X := by
  let _ := h.elementary
  let B := L ⊓ M
  have hBN := component_intersection_normalizes h hU hL.1
  have hXB : X ≤ B := le_inf hXL
    (hX.contained.trans (inf_le_left.trans inf_le_left))
  let e := (subgroupOfEquivOfLe hBN).symm
  let f : B →* inducedAutomizer V B :=
    (V.normalizerMonoidHom.rangeRestrict.subgroupMap
      (B.subgroupOf (normalizer (V : Set G)))).comp e.toMonoidHom
  have hker (x : B) : f x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
    constructor
    · intro hx
      have he : inclusion hBN x ∈ V.normalizerMonoidHom.ker :=
        congrArg (fun z : inducedAutomizer V B => z.val.val) hx
      rwa [normalizerMonoidHom_ker] at he
    · intro hx
      apply Subtype.ext
      apply Subtype.ext
      change inclusion hBN x ∈ V.normalizerMonoidHom.ker
      rwa [normalizerMonoidHom_ker]
  have hf : Function.Injective (f.comp (X.subgroupOf B).subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxC : (x.val : G) ∈ centralizer (V : Set G) := (hker x.val).mp hx
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact mem_bot.mp (hX.faithful ▸ (show (x.val : G) ∈ X ⊓ centralizer (V : Set G)
      from ⟨x.property, hxC⟩))
  have hoB : Odd (Nat.card (inducedAutomizer V B)) := by
    obtain ⟨a⟩ := b.action
    rw [Nat.card_congr a.toEquiv]
    have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    let : NeZero (2 ^ n - 1) := ⟨by omega⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hk := core_le_ker_of_odd_target f hoB
  refine ⟨X, hXL, hX, rfl, ?_⟩
  intro A hA ho hc
  have hAB := odd_normalizes_local_intersection h earlier hU hX hL hA ho hc
  have hcommC := cross_commutator_le_kernel hA
    (hX.contained.trans (inf_le_left.trans inf_le_right)) hc
  apply commutator_le.mpr
  intro a ha x hx
  let α := B.normalizerMonoidHom ⟨a, hAB ha⟩
  let xb : B := ⟨x, hXB hx⟩
  have hfix (z : B) (hz : z ∈ X.subgroupOf B) : f (α z) = f z := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    apply (hker _).mpr
    exact hcommC (commutator_mem_commutator ha hz)
  have he := quotient_fixed_of_faithful_image f (X.subgroupOf B) hk hf α hfix
    (x := xb) hx
  have hm : α xb * xb⁻¹ ∈ pCore 2 B := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 B) (α xb * xb⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  exact ⟨α xb * xb⁻¹, hm, rfl⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components
variable {G : Type*} [Group G] [Finite G]

/-- The PSU₃ Borel supplies the complete E.6.25 local bound, with the original
regular cyclic subgroup as witness. The matrix-field order and Hermitian
involution are those of the actual `ClassicalGroup.IsPSU` isomorphism. -/
theorem componentBorel_lift_unitary_three
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hLc : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    ComponentBorelLiftConclusion M V U L X := by
  let _ := componentBorel_quotient_unitary_three h hU hL b hn hQ S hS iso
  exact componentBorel_lift_of_cyclic_quotient h earlier hU hX hLc hXL b (by omega)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
