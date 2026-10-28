module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.ModelEight
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.TwentyOne.LinearModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.TwentyOne.ModelConjugacy
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.OddSubgroupLift

/-!
# From the local elementary eight-group to a subgroup of order twenty-one

Local conjugacy of self-centralizing elementary eights, together with ambient
involution fusion, makes the normalizer of `Hstar` transitive on its seven
nonidentity elements. Its order is divisible by seven and by the order 192
of the local normalizer. Its action kernel is `Hstar`, so the automorphism
count 168 forces the whole automorphism group to occur.

The explicit nonabelian subgroup of order twenty-one in GL₃(2) transports to
this automorphism group and lifts through the two-group action kernel by
Schur–Zassenhaus. Its injective ambient image has the required order and
noncommuting elements. No splitting of the entire normalizer is needed.

The intermediate reductions retain local conjugacy as an explicit premise.
The final theorem `nonabelian_twenty_one_of_involution_normalizers` discharges
it using `CaseII.modelHstar_conjugacy` in the actual twisted model.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 4, p.8, Lemma 9.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy

private theorem map_conj_natural {G K : Type*} [Group G] [Group K]
    (S : Subgroup G) (f : G →* K) (g : G) :
    (S.map (MulAut.conj g).toMonoidHom).map f =
      (S.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp

private theorem selfCentralizing_map {G : Type*} [Group G] (S : Subgroup G)
    [IsElementaryAbelian 2 S] (hS : centralizer (S : Set G) = S) (e : MulAut G) :
    centralizer (S.map e.toMonoidHom : Set G) = S.map e.toMonoidHom := by
  let := IsElementaryAbelian.map (p := 2) (A := S) e.toMonoidHom
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    apply mem_map_of_mem
    rw [← hS]
    intro t ht
    apply e.injective
    simpa only [map_mul] using hx (e t) (mem_map_of_mem e.toMonoidHom ht)
  · exact le_centralizer _

private theorem local_conjugacy_of_model_conjugacy
    {G : Type*} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (hunique : ∀ S : Subgroup TwistedModel, IsElementaryAbelian 2 S →
      Nat.card S = 8 → centralizer (S : Set TwistedModel) = S →
      ∃ c : TwistedModel, S.map (MulAut.conj c).toMonoidHom = CaseII.modelHstar)
    (S : Subgroup G) [IsElementaryAbelian 2 S]
    (hSC : S ≤ D.centralizer) (hS : Nat.card S = 8)
    (hcent : centralizer (S : Set G) = S) :
    ∃ c : D.centralizer,
      S.map (MulAut.conj (c : G)).toMonoidHom = CaseII.Hstar D k := by
  let T := (S.subgroupOf D.centralizer).map k.symm.toMonoidHom
  let := IsElementaryAbelian.subgroupOf (p := 2) hSC
  let := IsElementaryAbelian.map (p := 2) (A := S.subgroupOf D.centralizer) k.symm.toMonoidHom
  have hTmap : T.map (CaseII.into D k) = S := by
    change ((S.subgroupOf D.centralizer).map k.symm.toMonoidHom).map _ = S
    rw [map_map]
    have hf : (CaseII.into D k).comp k.symm.toMonoidHom = D.centralizer.subtype := by
      ext x
      exact congrArg Subtype.val (k.apply_symm_apply x)
    rw [hf, map_subgroupOf_eq_of_le hSC]
  have hTcard : Nat.card T = 8 := by
    rw [← card_map_of_injective (CaseII.into_injective D k), hTmap, hS]
  have hTcent : centralizer (T : Set TwistedModel) = T := by
    apply le_antisymm
    · intro x hx
      have hxS : CaseII.into D k x ∈ S := by
        rw [← hcent]
        intro t ht
        rw [← hTmap] at ht
        obtain ⟨y, hy, rfl⟩ := ht
        simpa only [← map_mul] using congrArg (CaseII.into D k) (hx y hy)
      rw [← hTmap] at hxS
      obtain ⟨y, hy, he⟩ := hxS
      exact CaseII.into_injective D k he ▸ hy
    · exact le_centralizer T
  obtain ⟨c, hc⟩ := hunique T inferInstance hTcard hTcent
  refine ⟨k c, ?_⟩
  have hh := congrArg (Subgroup.map (CaseII.into D k)) hc
  rw [map_conj_natural, hTmap] at hh
  exact hh

/-- Local uniqueness and involution fusion give the full nonidentity orbit. -/
public theorem Hstar_nonidentity_orbit_of_model_conjugacy
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (h2 : InvolutionNormalizerData D k)
    (hunique : ∀ S : Subgroup TwistedModel, IsElementaryAbelian 2 S →
      Nat.card S = 8 → centralizer (S : Set TwistedModel) = S →
      ∃ c : TwistedModel, S.map (MulAut.conj c).toMonoidHom = CaseII.modelHstar) :
    MulAction.orbit (normalizer (CaseII.Hstar D k : Set G))
      (⟨D.z, CaseII.z_mem_Hstar D k⟩ : CaseII.Hstar D k) =
        {x : CaseII.Hstar D k | x ≠ 1} := by
  let H := CaseII.Hstar D k
  let N := normalizer (H : Set G)
  let zH : H := ⟨D.z, CaseII.z_mem_Hstar D k⟩
  let := CaseII.Hstar_elementary D k
  have hf : ∀ x : H, x ≠ 1 → ∃ n : N, n • x = zH := by
    intro x hx
    have hxorder : orderOf (x : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 H) x
      · exact hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (h2.involution_fusion x hxorder)
    let S := H.map (MulAut.conj g).toMonoidHom
    let := IsElementaryAbelian.map (p := 2) (A := H) (MulAut.conj g).toMonoidHom
    have hSC : S ≤ D.centralizer := by
      rintro _ ⟨t, ht, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have htcomm : t * (x : G) = (x : G) * t :=
        congrArg Subtype.val (mul_comm (⟨t, ht⟩ : H) x)
      rw [← hg]
      exact (map_mul (MulAut.conj g) t (x : G)).symm.trans
        ((congrArg (MulAut.conj g) htcomm).trans (map_mul (MulAut.conj g) (x : G) t))
    have hS : Nat.card S = 8 :=
      (card_map_of_injective (MulAut.conj g).injective).trans (CaseII.Hstar_card D k)
    have hcent : centralizer (S : Set G) = S :=
      selfCentralizing_map H (CaseII.Hstar_centralizer D k) (MulAut.conj g)
    obtain ⟨c, hc⟩ := local_conjugacy_of_model_conjugacy D k hunique S hSC hS hcent
    have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj ((c : G) * g)).toMonoidHom := by
      ext t
      simp [mul_assoc]
    have hn : (c : G) * g ∈ N := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change H.map (MulAut.conj ((c : G) * g)).toMonoidHom = H
      rw [← hcomp, ← map_map]
      exact hc
    refine ⟨⟨(c : G) * g, hn⟩, ?_⟩
    apply Subtype.ext
    change (c : G) * g * (x : G) * ((c : G) * g)⁻¹ = D.z
    calc
      _ = (c : G) * (g * (x : G) * g⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * D.z * (c : G)⁻¹ := by rw [hg]
      _ = D.z := by
        rw [mem_centralizer_singleton_iff.mp c.property, mul_inv_cancel_right]
  ext x
  change x ∈ MulAction.orbit N zH ↔ x ≠ 1
  constructor
  · rintro ⟨n, rfl⟩ he
    have hh := congrArg (fun t : H => n⁻¹ • t) he
    have hz : zH = 1 := by simpa only [inv_smul_smul, smul_one] using hh
    exact D.z_ne_one (congrArg Subtype.val hz)
  · intro hx
    obtain ⟨n, hn⟩ := hf x hx
    refine ⟨n⁻¹, ?_⟩
    change n⁻¹ • zH = x
    rw [← hn, inv_smul_smul]

/-- The local order and the seven-element orbit force the full automorphism action. -/
public theorem Hstar_normalizer_action_surjective_of_model_conjugacy
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (h2 : InvolutionNormalizerData D k)
    (hunique : ∀ S : Subgroup TwistedModel, IsElementaryAbelian 2 S →
      Nat.card S = 8 → centralizer (S : Set TwistedModel) = S →
      ∃ c : TwistedModel, S.map (MulAut.conj c).toMonoidHom = CaseII.modelHstar) :
    Function.Surjective (CaseII.Hstar D k).normalizerMonoidHom := by
  classical
  let H := CaseII.Hstar D k
  let N := normalizer (H : Set G)
  let f := H.normalizerMonoidHom
  let zH : H := ⟨D.z, CaseII.z_mem_Hstar D k⟩
  let := CaseII.Hstar_elementary D k
  have hker : Nat.card f.ker = 8 := by
    rw [normalizerMonoidHom_ker, CaseII.Hstar_centralizer D k,
      Nat.card_congr (subgroupOfEquivOfLe H.le_normalizer).toEquiv]
    exact CaseII.Hstar_card D k
  have hprod : 8 * Nat.card f.range = Nat.card N := by
    simpa only [hker, index_ker] using f.ker.card_mul_index
  have h192 : 192 ∣ Nat.card N := by
    have hh := card_dvd_of_le
      (le_normalizer_map (H := CaseII.modelHstar) (CaseII.into D k))
    rw [card_map_of_injective (CaseII.into_injective D k),
      CaseII.modelHstar_normalizer_card] at hh
    exact hh
  have horbitcard : Nat.card (MulAction.orbit N zH) = 7 := by
    rw [Hstar_nonidentity_orbit_of_model_conjugacy D k h2 hunique]
    let := Fintype.ofFinite H
    change Nat.card {x : H // x ≠ 1} = 7
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, CaseII.Hstar_card, H]
  have h7 : 7 ∣ Nat.card N := by
    rw [← horbitcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N zH),
      ← index_eq_card]
    exact (MulAction.stabilizer N zH).index_dvd_card
  have h24range : 24 ∣ Nat.card f.range := by omega
  have h7range : 7 ∣ Nat.card f.range := by
    apply (show Nat.Coprime 7 8 by decide).dvd_of_dvd_mul_left
    rwa [hprod]
  have h168range : 168 ∣ Nat.card f.range :=
    (show Nat.Coprime 24 7 by decide).mul_dvd_of_dvd_of_dvd h24range h7range
  have hAut : Nat.card (MulAut H) = 168 :=
    card_mulAut_of_elementary_eight H (CaseII.Hstar_card D k)
  have hrange : Nat.card f.range ∣ 168 := hAut ▸ f.range.card_subgroup_dvd_card
  apply MonoidHom.range_eq_top.mp
  exact f.range.eq_top_of_card_eq ((Nat.dvd_antisymm hrange h168range).trans hAut.symm)

private theorem noncomm_map {G K : Type*} [Group G] [Group K]
    (S : Subgroup G) (f : G →* K) (hf : Function.Injective f)
    (hS : ∃ x y : S, x * y ≠ y * x) :
    ∃ x y : S.map f, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := hS
  refine ⟨⟨f x, mem_map_of_mem f x.property⟩,
    ⟨f y, mem_map_of_mem f y.property⟩, ?_⟩
  intro he
  apply hxy
  apply Subtype.ext
  apply hf
  simpa only [Subgroup.coe_mul, map_mul] using congrArg Subtype.val he

private theorem noncomm_of_map {G K : Type*} [Group G] [Group K]
    (S : Subgroup G) (T : Subgroup K) (f : G →* K) (hmap : S.map f = T)
    (hT : ∃ x y : T, x * y ≠ y * x) :
    ∃ x y : S, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := hT
  have hx : (x : K) ∈ S.map f := hmap.symm ▸ x.property
  have hy : (y : K) ∈ S.map f := hmap.symm ▸ y.property
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨t, ht, hyt⟩ := hy
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
  intro he
  apply hxy
  apply Subtype.ext
  have hh := congrArg f (congrArg Subtype.val he)
  simpa only [Subgroup.coe_mul, map_mul, hxs, hyt] using hh

/-- The remaining local conjugacy premise suffices for the order-twenty-one conclusion. -/
public theorem nonabelian_twenty_one_of_model_conjugacy
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (h2 : InvolutionNormalizerData D k)
    (hunique : ∀ S : Subgroup TwistedModel, IsElementaryAbelian 2 S →
      Nat.card S = 8 → centralizer (S : Set TwistedModel) = S →
      ∃ c : TwistedModel, S.map (MulAut.conj c).toMonoidHom = CaseII.modelHstar) :
    ∃ A : Subgroup G, Nat.card A = 21 ∧ ∃ x y : A, x * y ≠ y * x := by
  let H := CaseII.Hstar D k
  let N := normalizer (H : Set G)
  let f := H.normalizerMonoidHom
  let := CaseII.Hstar_elementary D k
  obtain ⟨e⟩ := elementaryEight_mulAut_equiv_GL H (CaseII.Hstar_card D k)
  obtain ⟨A, hA, hAnc⟩ := linear_nonabelian_twenty_one
  let B := A.map e.symm.toMonoidHom
  have hB : Nat.card B = 21 := (card_map_of_injective e.symm.injective).trans hA
  have hBnc : ∃ x y : B, x * y ≠ y * x :=
    noncomm_map A e.symm.toMonoidHom e.symm.injective hAnc
  have hker : IsPGroup 2 f.ker := by
    apply IsPGroup.of_card (n := 3)
    rw [normalizerMonoidHom_ker, CaseII.Hstar_centralizer D k,
      Nat.card_congr (subgroupOfEquivOfLe H.le_normalizer).toEquiv]
    exact CaseII.Hstar_card D k
  have hsurj : Function.Surjective f :=
    Hstar_normalizer_action_surjective_of_model_conjugacy D k h2 hunique
  obtain ⟨L, hLmap, _, hLcard, _⟩ :=
    f.exists_odd_subgroup_lift hsurj hker B (by rw [hB]; decide)
  refine ⟨L.map N.subtype, ?_, ?_⟩
  · rw [card_map_of_injective N.subtype_injective, hLcard, hB]
  · exact noncomm_map L N.subtype N.subtype_injective (noncomm_of_map L B f hLmap hBnc)

/-- Janko's Lemma 9, the nonabelian order-twenty-one conclusion, from the
Case II centralizer model and the preceding involution-normalizer data. -/
public theorem nonabelian_twenty_one_of_involution_normalizers
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (h2 : InvolutionNormalizerData D k) :
    ∃ A : Subgroup G, Nat.card A = 21 ∧ ∃ x y : A, x * y ≠ y * x := by
  exact nonabelian_twenty_one_of_model_conjugacy D k h2 CaseII.modelHstar_conjugacy

end Theory.GroupTheory.HeldM22A10.M22Identification
