module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCyclic
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder
public import Theory.GroupTheory.ElementaryEightPlanePointStabilizer
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The local second centralizer from the supplied data

Let N=N_G(F), K=O₂(N), and U=Ω₁(K). A supplied generator v of the
Q-fixed line in F is the fixed point in Z(U) outside Z(K). In particular,
Z(U)=Z(K)⟨v⟩ and U centralizes v. The derived-core calculation and the
explicit containment C_K(Q)≤K′ provide a cyclic group of order four whose
generator squares to this same v.

These statements use the supplied Sylow three-subgroup and involution;
no replacement by incompatible existential witnesses is made. The faithful
plane-stabilizer action on Z(U) has order 24. Stabilizing v gives S₃,
with kernel U. Thus C_N(v) has order 1536 and actual two-core U of order
256. These are local results and do not presume C_G(v)≤N.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.677 and §4, pp.682–683.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The supplied fixed involution lies in the omega center outside the core
center, generates their quotient, and is not conjugate to z. -/
public theorem normalizer_three_fixed_point_geometry
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    let ZK := (center K).map i
    let ZU := (center U).map (i.comp U.subtype)
    v ∈ ZU ∧ v ∉ ZK ∧ ZU = ZK ⊔ zpowers v ∧ ¬ IsConj z v ∧
      U.map i ≤ centralizer ({v} : Set G) := by
  intro N K U i ZK ZU
  let A := (Q : Subgroup N).map N.subtype
  have hvFC : v ∈ d.F ⊓ centralizer (A : Set G) := hfix.symm ▸ mem_zpowers v
  have hvZC : v ∈ ZU ⊓ centralizer (A : Set G) :=
    d.normalizer_three_fixed_elementary h hN hproper Q ▸ hvFC
  have hv1 : v ≠ 1 := by intro he; simp [he] at hv
  have hvout : v ∉ ZK := by
    intro hh
    have hh' : v ∈ ZK ⊓ centralizer (A : Set G) := ⟨hh, hvFC.2⟩
    rw [(d.normalizer_three_center_fixed_cards h hN hproper Q).1] at hh'
    exact hv1 hh'
  have hZKcard : Nat.card ZK = 4 :=
    (card_map_of_injective (K := center K) (f := i)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  have hZUcard : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hjoin : ZU = ZK ⊔ zpowers v := by
    apply (eq_of_le_of_card_ge
      (sup_le d.normalizer_core_omega_inclusions.2.1 (zpowers_le.mpr hvZC.1)) ?_).symm
    rw [card_sup_zpowers_of_normalizing_involution ZK v (hv ▸ pow_orderOf_eq_one v)
      hvout (d.normalizer_core_centers_normalized.1
        (d.sylow_le_normalizer (d.le_sylow hvFC.1))), hZKcard, hZUcard]
  refine ⟨hvZC.1, hvout, hjoin,
    d.normalizer_three_fixed_not_isConj h hN hproper Q v hvFC.2, ?_⟩
  obtain ⟨vU, hvU, heq⟩ := hvZC.1
  rintro x ⟨xK, hxU, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (i.comp U.subtype) (mem_center_iff.mp hvU ⟨xK, hxU⟩)
  change i xK * (i.comp U.subtype) vU = (i.comp U.subtype) vU * i xK at hh
  rwa [heq] at hh

/-- The explicit derived-centralizer containment supplies a cyclic generator
with square equal to the given fixed involution. The derived order is proved,
not an additional input. -/
public theorem exists_normalizer_three_cyclic_generator_of_local_data
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
  exact d.exists_normalizer_three_cyclic_generator_of_derived_calculations
    h hN hproper Q (d.normalizer_core_derived_order h hN hproper) hCD v hv hfix

/-- The second involution has centralizer of order 1536 inside the second
normalizer. This conclusion does not assume ambient centralizer containment. -/
public theorem normalizer_fixed_centralizer_structure
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let B := (centralizer ({v} : Set G)).subgroupOf N
    Nat.card B = 1536 ∧
      ((pCore 2 B).map B.subtype).map N.subtype = U.map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 B) = 256 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) := by
  classical
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let U := omega₁ K (p := 2)
  let i := N.subtype.comp K.subtype
  let Z := (center U).map (i.comp U.subtype)
  let D := (center K).map i
  let V := U.map K.subtype
  let B := (centralizer ({v} : Set G)).subgroupOf N
  have hNZ : N ≤ normalizer (Z : Set G) := d.normalizer_core_centers_normalized.2
  have hND : N ≤ normalizer (D : Set G) := d.normalizer_core_centers_normalized.1
  have hDZ : D ≤ Z := d.normalizer_core_omega_inclusions.2.1
  let f : N →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hNZ)
  have hker : f.ker = V := by
    ext x
    rw [MonoidHom.mem_ker]
    have hfix' : f x = 1 ↔ (x : G) ∈ centralizer (Z : Set G) := by
      constructor
      · intro hx u hu
        have hh := congrArg (fun a : MulAut Z => (a ⟨u, hu⟩ : G)) hx
        change (x : G) * u * (x : G)⁻¹ = u at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro hx
        apply MulEquiv.ext
        intro u
        apply Subtype.ext
        change (x : G) * (u : G) * (x : G)⁻¹ = u
        exact mul_inv_eq_iff_eq_mul.mpr (hx u u.property).symm
    rw [hfix']
    have hX : N ⊓ centralizer (Z : Set G) = V.map N.subtype := by
      simpa only [V, map_map, i] using d.normalizer_omega_center_centralizer h hN hproper
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := (hX ▸ ⟨x.property, hx⟩ : (x : G) ∈ V.map N.subtype)
      exact (N.subtype_injective heq) ▸ hy
    · intro hx
      exact (hX.symm ▸ mem_map_of_mem N.subtype hx).2
  have hVcard : Nat.card V = 256 :=
    (card_map_of_injective K.subtype_injective).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hRcard : Nat.card f.range = 24 := by
    have hc := f.ker.index_mul_card
    rw [index_ker, hker, hVcard, (d.normalizer_core_order h hN hproper).1] at hc
    omega
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hDcard : Nat.card (D.subgroupOf Z) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDZ).toEquiv]
    exact (card_map_of_injective (K := center K) (f := i)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  let : IsElementaryAbelian 2 (center U) := d.normalizer_core_omega_center_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map (i.comp U.subtype)
  have hstable : ∀ a : f.range, ∀ x : Z,
      (a : MulAut Z) x ∈ D.subgroupOf Z ↔ x ∈ D.subgroupOf Z := by
    rintro ⟨a, ha⟩ x
    obtain ⟨n, rfl⟩ := ha
    change (n : G) * (x : G) * (n : G)⁻¹ ∈ D ↔ (x : G) ∈ D
    exact (mem_normalizer_iff.mp (hND n.property) x).symm
  obtain ⟨hvZ, hvD, _, _, _⟩ := d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix
  let vZ : Z := ⟨v, hvZ⟩
  let S := MulAction.stabilizer f.range vZ
  have hS : Nat.card S = 6 := elementaryEight_plane_order24_outside_stabilizer_card
    hZcard (D.subgroupOf Z) hDcard f.range hRcard hstable vZ hvD
  have hB : B = S.comap f.rangeRestrict := by
    ext n
    change (n : G) ∈ centralizer ({v} : Set G) ↔ f n vZ = vZ
    rw [mem_centralizer_singleton_iff, Subtype.ext_iff]
    change (n : G) * v = v * (n : G) ↔ (n : G) * v * (n : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.symm
  have hBindex : B.index = 4 := by
    rw [hB, index_comap_of_surjective _ f.rangeRestrict_surjective]
    have hc := S.index_mul_card
    rw [hS, hRcard] at hc
    omega
  have hBcard : Nat.card B = 1536 := by
    have hc := B.index_mul_card
    rw [hBindex, (d.normalizer_core_order h hN hproper).1] at hc
    omega
  let g : B →* S := {
    toFun b := ⟨f.rangeRestrict b.val, (show b.val ∈ S.comap f.rangeRestrict from hB ▸ b.property)⟩
    map_one' := by apply Subtype.ext; exact f.rangeRestrict.map_one
    map_mul' a b := by apply Subtype.ext; exact f.rangeRestrict.map_mul a.val b.val }
  have hgsurj : Function.Surjective g := by
    intro s
    obtain ⟨n, hn⟩ := f.rangeRestrict_surjective s.val
    have hnB : n ∈ B := by
      rw [hB]
      change f.rangeRestrict n ∈ S
      rw [hn]
      exact s.property
    exact ⟨⟨n, hnB⟩, Subtype.ext hn⟩
  have hgker : g.ker = V.subgroupOf B := by
    ext b
    change g b = 1 ↔ b.val ∈ V
    rw [← hker, MonoidHom.mem_ker]
    constructor
    · intro hh
      exact congrArg (fun a : S => (a.val : MulAut Z)) hh
    · intro hh
      exact Subtype.ext (Subtype.ext hh)
  have hVB : V ≤ B := by
    intro n hn
    have hh := (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.2
    apply hh
    simpa only [V, map_map] using (mem_map_of_mem N.subtype hn)
  have hkerCard : Nat.card g.ker = 256 := by
    rw [hgker, Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv]
    exact hVcard
  obtain ⟨e⟩ := elementaryEight_plane_order24_outside_stabilizer_equiv_S3
    hZcard (D.subgroupOf Z) hDcard f.range hRcard hstable vZ hvD
  let g3 := e.toMonoidHom.comp g
  have hg3 : g3.ker = g.ker := MonoidHom.ker_comp_of_injective g e.toMonoidHom e.injective
  have hg3P : IsPGroup 2 g3.ker := IsPGroup.of_card (n := 8) (by rw [hg3, hkerCard]; decide)
  have hcore : g3.ker = pCore 2 B :=
    ker_eq_twoCore_of_surjective_perm_three g3 (e.surjective.comp hgsurj) hg3P
  refine ⟨hBcard, ?_, ?_, ?_⟩
  · rw [← hcore, hg3, hgker, map_subgroupOf_eq_of_le hVB, map_map]
  · rw [← hcore, hg3, hkerCard]
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g3 (e.surjective.comp hgsurj))⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
