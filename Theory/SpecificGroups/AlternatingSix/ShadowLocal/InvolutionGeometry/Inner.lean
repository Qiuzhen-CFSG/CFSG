module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.Alternating.proposition_5_2_4

/-!
# Inner involutions of A₆ and their automorphism centralizers

There are 45 involutions in the actual six-point alternating group, all
conjugate in A₆. Orbit–stabilizer for conjugation and for the full automorphism
action gives fixed-group order eight and automorphism-centralizer order 32.
These are Sylow two-subgroups; the fixed subgroup is dihedral.

The final containment calculation keeps the inner embedding explicit. For an
inner involution, its fixed subgroup maps into P exactly when the involution
lies in the image of the center of `sylowInner P`. Equal subgroup orders give
the forward implication, rather than an assumed local-group identification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.567–570, particularly Lemma 2.5.26.
The involution count and support check use kernel-checked finite computation;
conjugacy uses the alternating-group conjugacy theorem in GLS vol.3, §5.2.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem involution_card : Nat.card {a : A6 // a ^ 2 = 1 ∧ a ≠ 1} = 45 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem involution_support_card (a : A6) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    (a : Equiv.Perm (Fin 6)).support.card = 4 := by
  revert a
  decide +kernel

theorem involutions_isConj (a b : A6) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hane : a ≠ 1 := by intro h; simp [h] at ha
  have hbne : b ≠ 1 := by intro h; simp [h] at hb
  exact SchurPresentation.alternating_involution_isConj_of_card_support_eq
    (congrArg Subtype.val ha2) (congrArg Subtype.val hb2) hane
    ((involution_support_card a ha2 hane).trans (involution_support_card b hb2 hbne).symm)

theorem aut_conj_inner (β : AutA6) (a : A6) :
    β * MulAut.conj a * β⁻¹ = MulAut.conj (β a) := by
  ext x
  simp

theorem centralizer_inner_eq_stabilizer (a : A6) :
    centralizer ({MulAut.conj a} : Set AutA6) = MulAction.stabilizer AutA6 a := by
  ext β
  rw [mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  rw [← mul_inv_eq_iff_eq_mul, aut_conj_inner, inner_injective.eq_iff]

theorem aut_orbit_involution (a : A6) (ha : orderOf a = 2) :
    MulAction.orbit AutA6 a = {b : A6 | b ^ 2 = 1 ∧ b ≠ 1} := by
  ext b
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨β, rfl⟩
    change (β a) ^ 2 = 1 ∧ β a ≠ 1
    have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hane : a ≠ 1 := by intro h; simp [h] at ha
    exact ⟨by rw [← map_pow, ha2, map_one], by simpa using hane⟩
  · rintro ⟨hb2, hbne⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj a b ha
      (orderOf_eq_prime hb2 hbne))
    exact ⟨MulAut.conj g, hg⟩

theorem inner_involution_centralizer_card (a : A6) (ha : orderOf a = 2) :
    Nat.card (centralizer ({MulAut.conj a} : Set AutA6)) = 32 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup AutA6 a)
  rw [Nat.card_prod, aut_orbit_involution a ha, card_aut] at h
  change Nat.card {b : A6 // b ^ 2 = 1 ∧ b ≠ 1} *
    Nat.card (MulAction.stabilizer AutA6 a) = 1440 at h
  rw [involution_card] at h
  rw [centralizer_inner_eq_stabilizer]
  omega

noncomputable def innerInvolutionSylow (a : A6) (ha : orderOf a = 2) : Sylow 2 AutA6 := by
  let C := centralizer ({MulAut.conj a} : Set AutA6)
  have hc : Nat.card C = 32 := inner_involution_centralizer_card a ha
  have hp : IsPGroup 2 C := IsPGroup.of_card (show Nat.card C = 2 ^ 5 from hc)
  exact hp.toSylow (by
    have h := C.card_mul_index
    rw [hc, card_aut] at h
    have hi : C.index = 45 := by omega
    rw [hi]
    decide)

theorem innerInvolutionSylow_coe (a : A6) (ha : orderOf a = 2) :
    (innerInvolutionSylow a ha : Subgroup AutA6) = centralizer {MulAut.conj a} := rfl

theorem inner_fixed_eq_centralizer (a : A6) :
    automorphismFixedSubgroup (MulAut.conj a) = centralizer {a} := by
  ext b
  change a * b * a⁻¹ = b ↔ b ∈ centralizer {a}
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem alternating_orbit_involution (a : A6) (ha : orderOf a = 2) :
    MulAction.orbit (ConjAct A6) a = {b : A6 | b ^ 2 = 1 ∧ b ≠ 1} := by
  ext b
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    change (g.ofConjAct * a * g.ofConjAct⁻¹) ^ 2 = 1 ∧
      g.ofConjAct * a * g.ofConjAct⁻¹ ≠ 1
    have ho : orderOf (MulAut.conj g.ofConjAct a) = 2 :=
      ((MulAut.conj g.ofConjAct).orderOf_eq a).trans ha
    exact ⟨ho ▸ pow_orderOf_eq_one _, by intro h; change orderOf (g.ofConjAct * a * g.ofConjAct⁻¹) = 2 at ho; rw [h, orderOf_one] at ho; contradiction⟩
  · rintro ⟨hb2, hbne⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj a b ha
      (orderOf_eq_prime hb2 hbne))
    exact ⟨ConjAct.toConjAct g, hg⟩

theorem inner_involution_fixed_card (a : A6) (ha : orderOf a = 2) :
    Nat.card (automorphismFixedSubgroup (MulAut.conj a)) = 8 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct A6) a)
  rw [Nat.card_prod, alternating_orbit_involution a ha] at h
  change Nat.card {b : A6 // b ^ 2 = 1 ∧ b ≠ 1} *
    Nat.card (MulAction.stabilizer (ConjAct A6) a) = Nat.card A6 at h
  rw [involution_card, card_A6, ConjAct.stabilizer_eq_centralizer] at h
  rw [inner_fixed_eq_centralizer]
  change 45 * Nat.card (centralizer ({a} : Set A6)) = 360 at h
  omega

/-- The center of the actual inner Sylow intersection, viewed in Aut(A₆). -/
def innerSylowCenter (P : Sylow 2 AutA6) : Subgroup AutA6 :=
  (center (sylowInner P)).map
    ((P : Subgroup AutA6).subtype.comp (sylowInner P).subtype)

theorem fixedInner_le_inner (β : AutA6) :
    (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤ inner := by
  rintro _ ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

theorem inner_involution_fixed_le_sylow_iff (P : Sylow 2 AutA6)
    (β : AutA6) (hβ : orderOf β = 2) (hinner : β ∈ inner) :
    (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤
      (P : Subgroup AutA6) ↔ β ∈ innerSylowCenter P := by
  obtain ⟨a, rfl⟩ := hinner
  have ha : orderOf a = 2 := by
    rwa [orderOf_injective _ inner_injective] at hβ
  let F := (automorphismFixedSubgroup (MulAut.conj a)).map (MulAut.conj : A6 →* AutA6)
  have hFcard : Nat.card F = 8 := by
    rw [Subgroup.card_map_of_injective inner_injective]
    exact inner_involution_fixed_card a ha
  constructor
  · intro hFP
    have haF : MulAut.conj a ∈ F := by
      refine ⟨a, ?_, rfl⟩
      change a * a * a⁻¹ = a
      simp
    let b : sylowInner P := ⟨⟨MulAut.conj a, hFP haF⟩, ⟨a, rfl⟩⟩
    have hFint : F = (inner ⊓ (P : Subgroup AutA6)) := by
      apply Subgroup.eq_of_le_of_card_ge (le_inf (fixedInner_le_inner _) hFP)
      have e : sylowInner P ≃* ↥(inner ⊓ (P : Subgroup AutA6)) := {
        toFun x := ⟨x.val.val, x.property, x.val.property⟩
        invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl }
      rw [← Nat.card_congr e.toEquiv, sylowInner_card, hFcard]
    have hb : b ∈ center (sylowInner P) := by
      rw [mem_center_iff]
      intro c
      have hc : c.val.val ∈ F := by rw [hFint]; exact ⟨c.property, c.val.property⟩
      obtain ⟨d, hd, he⟩ := hc
      have hdcomm : d * a = a * d := by
        rw [inner_fixed_eq_centralizer] at hd
        exact mem_centralizer_singleton_iff.mp hd
      apply Subtype.ext
      apply Subtype.ext
      change c.val.val * MulAut.conj a = MulAut.conj a * c.val.val
      rw [← he, ← map_mul, ← map_mul, hdcomm]
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, he⟩
    change b.val.val = MulAut.conj a at he
    have hcenter : (P : Subgroup AutA6) ⊓ inner ≤
        centralizer ({MulAut.conj a} : Set AutA6) := by
      intro c hc
      let d : sylowInner P := ⟨⟨c, hc.1⟩, hc.2⟩
      have hd := mem_center_iff.mp hb d
      rw [mem_centralizer_singleton_iff]
      have hc' : c * b.val.val = b.val.val * c :=
        congrArg (fun x : sylowInner P => x.val.val) hd
      simpa only [he] using hc'
    have hfixed : (P : Subgroup AutA6) ⊓ inner = F := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro c hc
        obtain ⟨d, rfl⟩ := hc.2
        refine ⟨d, ?_, rfl⟩
        have hcomm := mem_centralizer_singleton_iff.mp (hcenter hc)
        have hd : d * a = a * d := inner_injective (by simpa only [map_mul] using hcomm)
        rw [inner_fixed_eq_centralizer]
        exact mem_centralizer_singleton_iff.mpr hd
      · have e : sylowInner P ≃* ↥((P : Subgroup AutA6) ⊓ inner) := {
          toFun x := ⟨x.val.val, x.val.property, x.property⟩
          invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
          left_inv _ := rfl
          right_inv _ := rfl
          map_mul' _ _ := rfl }
        rw [← Nat.card_congr e.toEquiv, sylowInner_card, hFcard]
    change F ≤ (P : Subgroup AutA6)
    rw [← hfixed]
    exact inf_le_left

theorem inner_involution_fixed_equiv_dihedral (a : A6) (ha : orderOf a = 2) :
    Nonempty (automorphismFixedSubgroup (MulAut.conj a) ≃* DihedralGroup 4) := by
  let F := automorphismFixedSubgroup (MulAut.conj a)
  have hc : Nat.card F = 8 := inner_involution_fixed_card a ha
  have hp : IsPGroup 2 F := IsPGroup.of_card (show Nat.card F = 2 ^ 3 from hc)
  let Q : Sylow 2 A6 := hp.toSylow (by
    have h := F.card_mul_index
    rw [hc, card_A6] at h
    have hi : F.index = 45 := by omega
    rw [hi]
    decide)
  exact alternatingSylow_dihedral Q

theorem inner_involution_centralizer_sylow (β : AutA6) (hβ : orderOf β = 2)
    (hinner : β ∈ inner) :
    ∃ P : Sylow 2 AutA6, (P : Subgroup AutA6) = centralizer {β} := by
  obtain ⟨a, rfl⟩ := hinner
  have ha : orderOf a = 2 := by rwa [orderOf_injective _ inner_injective] at hβ
  exact ⟨innerInvolutionSylow a ha, rfl⟩

theorem innerSylowCenter_le_inner (P : Sylow 2 AutA6) : innerSylowCenter P ≤ inner := by
  rintro _ ⟨b, _, rfl⟩
  exact b.property

theorem innerSylowCenter_le_sylow (P : Sylow 2 AutA6) :
    innerSylowCenter P ≤ (P : Subgroup AutA6) := by
  rintro _ ⟨b, _, rfl⟩
  exact b.val.property

theorem fixed_inner_card_dvd_sylow (P : Sylow 2 AutA6) (β : AutA6)
    (h : (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤
      (P : Subgroup AutA6)) :
    Nat.card (automorphismFixedSubgroup β) ∣ 32 := by
  have hd := Subgroup.card_dvd_of_le h
  rwa [Subgroup.card_map_of_injective inner_injective, sylow_card] at hd

end AlternatingSix.ShadowLocal
