module
public import Stellmacher.Recognition.Parrott.OmegaGeometry
public import Stellmacher.Recognition.Parrott.DerivedWeakClosure
public import Stellmacher.Recognition.Parrott.OmegaNormalizerMovement
public import Theory.GroupAction.SixteenFourSuborbit

/-!
# The five-element fixed-join normalizer orbit

Under the core-involution negation, let y be an outer involution of H
conjugate to z and X the actual mapped Ω₁(C_H(y)). The index of N_G(X)∩H
in N_G(X) is five. The native normalizer conjugation action on X has
four-element E-suborbits outside Z = E∩C_G(y), by the exact centralizer
identities and |E:Z|=4. Weak closure confines the orbit's intersection with
Z to z, and normalizer enlargement moves z. The order-sixteen orbit theorem
therefore gives five, and orbit-stabilizer identifies the claimed index.
The fixed-join version requires only weak closure in E and movement of z;
the original omega interface follows from the core-involution premise.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 3, printed p.675.
-/

open Subgroup MulAction
namespace Stellmacher.Recognition

/-- Weak closure and movement give index five for the outer fixed-join normalizer. -/
public theorem parrott_outer_fixed_join_normalizer_index
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ E → IsConj z t → t = z) →
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let X := zpowers (y : G) ⊔ (E ⊓ centralizer ({(y : G)} : Set G))
      ¬ normalizer (X : Set G) ≤ H →
      (H.subgroupOf (normalizer (X : Set G))).index = 5 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ E → IsConj z t → t = z) → _
  intro hweak y hy hyJ
  dsimp only
  intro hnot
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let X := zpowers (y : G) ⊔ Z
  let N := normalizer (X : Set G)
  let A := E.subgroupOf N
  let U := Z.subgroupOf X
  change (H.subgroupOf N).index = 5
  obtain ⟨hEcard, hZcard, hXcard, _, _, hzZ, hZX, _, hEN, _, _, houter⟩ :=
    parrott_outer_fixed_join_geometry z h y hy hyJ
  change E ≤ N at hEN
  change Z ≤ X at hZX
  have hAcard : Nat.card A = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hEcard
  have hUcard : Nat.card U = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZX).toEquiv).trans hZcard
  let zX : X := ⟨z, hZX hzZ⟩
  have hzU : zX ∈ U := hzZ
  have hAz (a : A) : a • zX = zX := by
    apply Subtype.ext
    change ((a : N) : G) * z * ((a : N) : G)⁻¹ = z
    have haH : ((a : N) : G) ∈ H := by
      obtain ⟨d, _, hd⟩ := a.property
      have hh : ((d : H) : G) = ((a : N) : G) := hd
      exact hh ▸ (d : H).property
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp haH)
  have hfour (x : X) (hxU : x ∉ U) : Nat.card (orbit A x) = 4 := by
    let S := stabilizer A x
    let f : A →* G := N.subtype.comp A.subtype
    have hf : Function.Injective f := N.subtype_injective.comp A.subtype_injective
    have hSmap : S.map f = Z := by
      have hout : E ⊓ centralizer ({(x : G)} : Set G) = Z := houter x x.property hxU
      rw [← hout]
      apply le_antisymm
      · rintro g ⟨a, ha, rfl⟩
        refine ⟨a.property, mem_centralizer_singleton_iff.mpr ?_⟩
        have hh := congrArg (fun v : X => (v : G)) (mem_stabilizer_iff.mp ha)
        exact mul_inv_eq_iff_eq_mul.mp hh
      · intro g hg
        let a : A := ⟨⟨g, hEN hg.1⟩, hg.1⟩
        refine ⟨a, mem_stabilizer_iff.mpr ?_, rfl⟩
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg.2)
    have hScard : Nat.card S = 8 := by
      have hh := card_map_of_injective (K := S) (f := f) hf
      rw [hSmap] at hh
      exact hh.symm.trans hZcard
    have hc := S.index_mul_card
    rw [show S.index = Nat.card (orbit A x) from index_stabilizer A x, hScard, hAcard] at hc
    omega
  have hinter (x : X) (hx : x ∈ orbit N zX) (hxU : x ∈ U) : x = zX := by
    apply Subtype.ext
    apply hweak x hxU.1
    obtain ⟨n, hn⟩ := hx
    exact isConj_iff.mpr ⟨(n : G), congrArg (fun v : X => (v : G)) hn⟩
  have hmove : ∃ n : N, n • zX ≠ zX := by
    obtain ⟨n, hn, hnH⟩ := SetLike.not_le_iff_exists.mp hnot
    refine ⟨⟨n, hn⟩, ?_⟩
    intro heq
    apply hnH
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg (fun v : X => (v : G)) heq))
  have horbit := card_orbit_five_of_card_sixteen_and_four_suborbits
    hXcard U hUcard zX hzU A hAz hfour hinter hmove
  have hstab : stabilizer N zX = H.subgroupOf N := by
    ext n
    rw [mem_stabilizer_iff]
    change n • zX = zX ↔ (n : G) ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul]
    exact Subtype.ext_iff
  rw [← hstab, index_stabilizer]
  exact horbit

/-- The normalizer of the actual omega subgroup has centralizer intersection of index five. -/
public theorem parrott_omega_normalizer_index
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      (H.subgroupOf (normalizer (X : Set G))).index = 5 := by
  dsimp only
  intro hcore y hy hyJ hconj
  have hX := (parrott_outer_centralizer_omega z h hcore y hy hyJ).2.1
  have hnot := parrott_omega_normalizer_not_le_centralizer z h hcore y hy hyJ hconj
  dsimp only at hnot
  rw [hX] at hnot ⊢
  exact parrott_outer_fixed_join_normalizer_index z h
    (parrott_derived_weakClosure_of_core_involutions hN z h hcore) y hy hyJ hnot

end Stellmacher.Recognition
