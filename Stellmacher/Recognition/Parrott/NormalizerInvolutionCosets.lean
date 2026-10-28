module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCyclic
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder
public import Theory.GroupAction.ThreeInvolutionCosets
public import Theory.GroupAction.Quotient

/-!
# Involution-bearing cosets of the second elementary subgroup

Every involution in the actual normalizer core belongs to its omega subgroup.
An order-three actor cannot fix a nonidentity F-coset containing involutions:
the square-one lifts have two-power cardinality, so a fixed coset supplies a
fixed involution, and the derived-core calculation puts that involution in F.
The original core contains at least four of the eight F-cosets, and its
involutions lie in the two cosets of E∨F. Hence at most five nonidentity
cosets contain involutions. Their number is a positive multiple of three;
they form a single orbit, giving transport by the supplied Q into E∨F.
This argument derives the geometry without choosing the representatives
w, y, and ywb. It only needs the supplied derived-centralizer containment;
the fixed-line hypotheses also give the actual cyclic order-four centralizer.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678, the three involution-bearing cosets in Ω₁(K)/F.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
/-- Every square-one element of the actual normalizer core is in its omega image. -/
public theorem normalizer_core_square_one_mem_omega (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ y ∈ K.map N.subtype, y ^ 2 = 1 →
      y ∈ (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro N K y hy hy2
  obtain ⟨n, hn, rfl⟩ := hy
  let k : K := ⟨n, hn⟩
  have hk : k ∈ omega₁ K (p := 2) := by
    apply Subgroup.subset_closure
    change k ^ (2 ^ 1) = 1
    exact Subtype.ext (Subtype.ext hy2)
  exact mem_map_of_mem (N.subtype.comp K.subtype) hk

/-- Discharge the derived-order input in the existing cyclic-centralizer theorem,
retaining the supplied Q and fixed involution v. -/
public theorem exists_normalizer_three_cyclic_generator_of_centralizer_le_derived
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∃ b : G, b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b := by
  intro N X D A hCD v hv hfix
  exact d.exists_normalizer_three_cyclic_generator_of_derived_calculations h hN hproper Q
    (d.normalizer_core_derived_order h hN hproper) hCD v hv hfix

/-- At most five nonidentity F-cosets in the actual omega image contain
square-one elements. At least four cosets come from the original core,
whose involutions lie in the two cosets of E∨F. -/
public theorem normalizer_core_involution_cosets_le_five
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let F₀ := d.F.subgroupOf W
    Nat.card {c : W ⧸ F₀ // c ≠ QuotientGroup.mk (1 : W) ∧
      ∃ u : W, u ^ 2 = 1 ∧ QuotientGroup.mk u = c} ≤ 5 := by
  intro N K W F₀
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let L := J.map H.subtype
  let X := K.map N.subtype
  let B := L.subgroupOf W
  let C := (E ⊔ d.F).subgroupOf W
  have hWX : W ≤ X := by
    rw [show W = ((omega₁ K (p := 2)).map K.subtype).map N.subtype from
      (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  have hWN : W ≤ N := hWX.trans (map_subtype_le K)
  have hFW : d.F ≤ W := d.normalizer_core_omega_inclusions.1
  have hCW : E ⊔ d.F ≤ W := d.elementary_join_le_normalizer_core_omega h hN hproper
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  let f := QuotientGroup.mk' F₀
  have hFcard : Nat.card F₀ = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFW).toEquiv).trans d.card
  have hWcard : Nat.card W = 256 :=
    (card_map_of_injective (K := omega₁ K (p := 2)) (f := N.subtype.comp K.subtype)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hRcard : Nat.card (W ⧸ F₀) = 8 := by
    have hh := F₀.index_mul_card
    change Nat.card (W ⧸ F₀) * Nat.card F₀ = Nat.card W at hh
    rw [hFcard, hWcard] at hh
    omega
  have hFB : F₀ ≤ B := fun u hu => d.le_core hu
  have hFC : F₀ ≤ C := fun u hu => mem_sup_right hu
  have himage (S : Subgroup W) (hFS : F₀ ≤ S) :
      32 * Nat.card (S.map f) = Nat.card S := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup W) F₀ S bot_le hFS
    rw [relIndex_bot_left, relIndex_bot_left, hFcard] at hh
    have hi := relIndex_ker S f
    rw [QuotientGroup.ker_mk'] at hi
    change F₀.relIndex S = Nat.card (S.map f) at hi
    rwa [hi] at hh
  have hCcard : Nat.card C = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCW).toEquiv).trans (d.elementary_join_card h)
  have hCimage : Nat.card (C.map f) ≤ 2 := by
    have hh := himage C hFC
    rw [hCcard] at hh
    omega
  have hBcard : 128 ≤ Nat.card B := by
    obtain ⟨y, hy, hy2, hyJ⟩ :=
      d.exists_normalizer_core_involution_outside_original_core h hN hproper
    let Z := E ⊓ centralizer ({y} : Set G)
    let B₀ := L ⊓ centralizer (Z : Set G)
    have hB₀card : Nat.card B₀ = 128 :=
      (d.normalizer_core_outer_fixed_centralizer h hN hproper y hy hy2 hyJ).2.1
    have hB₀W : B₀ ≤ W := d.normalizer_core_outer_fixed_kernel_le_omega h hN hproper y hy hy2 hyJ
    let inclusionB : B₀ → B := fun b => ⟨⟨b, hB₀W b.property⟩, b.property.1⟩
    have hinj : Function.Injective inclusionB := by
      intro a b hab
      exact Subtype.ext (congrArg (fun x : B => ((x : W) : G)) hab)
    have hh := Nat.card_le_card_of_injective inclusionB hinj
    rwa [hB₀card] at hh
  have hBimage : 4 ≤ Nat.card (B.map f) := by
    have hh := himage B hFB
    omega
  have hBC : ∀ u ∈ B, u ^ 2 = 1 → u ∈ C := by
    intro u hu hu2
    obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
      d.exists_normalizer_core_center_generator h hN hproper
    have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
      rw [hcenter]
      exact mem_sup_right (mem_zpowers t)
    have hKC := d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
    change X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) at hKC
    have hKcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 := by
      rw [← hKC, card_map_of_injective N.subtype_injective]
      exact (d.normalizer_core_order h hN hproper).2.1
    have hut : (u : G) ∈ centralizer ({t} : Set G) := (hKC ▸ hWX u.property).2
    exact d.t_centralizer_core_involution_mem_elementary_join h t ht htz hKcard
      u ⟨hu, hut⟩ (congrArg W.subtype hu2)
  exact Theory.GroupAction.square_one_images_le_five f B C
    ((QuotientGroup.ker_mk' F₀).symm ▸ hFB) hRcard hBimage hCimage hBC

/-- The supplied Q transports every square-one element of the actual
normalizer core into E∨F. The involution-bearing cosets are a single
three-element orbit, by the five-coset bound and exclusion of fixed cosets. -/
public theorem normalizer_core_involution_transport
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ y ∈ X, y ^ 2 = 1 →
      ∃ q : Q, ((q : N) : G) * y * ((q : N) : G)⁻¹ ∈ E ⊔ d.F := by
  classical
  intro H J E N K X D A hCD y hy hy2
  let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
  let F₀ := d.F.subgroupOf W
  have hcount := d.normalizer_core_involution_cosets_le_five h hN hproper
  by_cases hyF : y ∈ d.F
  · exact ⟨1, by simpa using (mem_sup_right hyF : y ∈ E ⊔ d.F)⟩
  let U := omega₁ K (p := 2)
  let V := U.map K.subtype
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNW : N ≤ normalizer (W : Set G) := by
    have hh := le_normalizer_map (H := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  have hWX : W ≤ X := by
    rw [show W = V.map N.subtype from (map_map _ _ _).symm]
    exact map_mono (map_subtype_le U)
  have hWN : W ≤ N := hWX.trans (map_subtype_le K)
  have hFW : d.F ≤ W := d.normalizer_core_omega_inclusions.1
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  let action : Q →* MulAut W :=
    (W.normalizerMonoidHom.comp (inclusion hNW)).comp (Q : Subgroup N).subtype
  let : MulDistribMulAction Q W := MulDistribMulAction.compHom W action
  have hInv : IsInvariant Q W F₀ := by
    constructor
    intro q u
    change (u : G) ∈ d.F ↔ ((q : N) : G) * (u : G) * ((q : N) : G)⁻¹ ∈ d.F
    exact mem_normalizer_iff.mp (q : N).property u
  let : MulDistribMulAction Q (W ⧸ F₀) := quotientMulDistribMulAction F₀ hInv
  let f := QuotientGroup.mk' F₀
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : IsElementaryAbelian 2 F₀ := IsElementaryAbelian.subgroupOf hFW
  have hker : f.ker = F₀ := QuotientGroup.ker_mk' F₀
  let : IsElementaryAbelian 2 f.ker := hker.symm ▸ inferInstance
  have hFcard : Nat.card F₀ = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFW).toEquiv).trans d.card
  have hcoprime : ¬ 3 ∣ Nat.card f.ker := by rw [hker, hFcard]; decide
  have hequiv (q : Q) (u : W) : f (q • u) = q • f u := by
    let : MulAction.QuotientAction Q F₀ := quotientAction_of_isInvariant F₀ hInv
    exact (MulAction.Quotient.smul_coe F₀ q u).symm
  have hfixed (u : W) (hu : u ^ 2 = 1) (hfix : ∀ q : Q, q • u = u) : f u = 1 := by
    apply (QuotientGroup.eq_one_iff u).mpr
    change (u : G) ∈ d.F
    apply (d.normalizer_core_derived_square_one_iff h hN hproper (u : G) ?_).mp
      (congrArg W.subtype hu)
    apply hCD
    refine ⟨hWX u.property, ?_⟩
    rintro a ⟨q, hq, rfl⟩
    have hh := congrArg W.subtype (hfix ⟨q, hq⟩)
    change (q : G) * (u : G) * (q : G)⁻¹ = (u : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans
      (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hnot : ¬ E ≤ d.F := by
    intro he
    exact d.ne_derived (eq_of_le_of_card_ge he (by rw [d.card, hEcard])).symm
  obtain ⟨w, hw, hwF⟩ := SetLike.not_le_iff_exists.mp hnot
  have hwW : w ∈ W := d.elementary_join_le_normalizer_core_omega h hN hproper
    (mem_sup_left hw)
  let u : W := ⟨y, d.normalizer_core_square_one_mem_omega y hy hy2⟩
  let t : W := ⟨w, hwW⟩
  obtain ⟨q, hq⟩ := Theory.GroupAction.three_involution_cosets_transitive f
    (d.normalizer_three_card h hN hproper Q) hcoprime hequiv hfixed hcount u t
    (Subtype.ext hy2) (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw))
    (fun hh => hyF ((QuotientGroup.eq_one_iff u).mp hh))
    (fun hh => hwF ((QuotientGroup.eq_one_iff t).mp hh))
  have hmem : (q • u) / t ∈ F₀ := QuotientGroup.eq_iff_div_mem.mp hq
  have hdiff : (((q : N) : G) * y * ((q : N) : G)⁻¹) / w ∈ d.F := hmem
  refine ⟨q, ?_⟩
  have hm := (E ⊔ d.F).mul_mem (mem_sup_right hdiff) (mem_sup_left hw)
  simpa only [div_mul_cancel] using hm


/-- The requested normalizer conjugator for an outer core involution, retaining
the supplied Q and fixed line. In fact the conjugator comes from Q, and the
stronger transport theorem does not need the outer or fixed-line premises. -/
public theorem normalizer_core_outer_involution_conjugate_into_elementary_join
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ y : G, y ∈ X → y ∉ J.map H.subtype → orderOf y = 2 →
      ∃ n : N, (n : G) * y * (n : G)⁻¹ ∈ E ⊔ d.F := by
  intro H J E N X D A hCD _v _hv _hfix y hy _hyJ hy2
  obtain ⟨q, hq⟩ := d.normalizer_core_involution_transport h hN hproper Q hCD y hy
    (hy2 ▸ pow_orderOf_eq_one y)
  exact ⟨q, hq⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
