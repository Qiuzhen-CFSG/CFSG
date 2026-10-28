module
public import Stellmacher.Recognition.Parrott.OuterCentralizerOmega
public import Theory.GroupTheory.ElementaryInvolutionFixedJoin

/-!
# Geometry of Parrott's outer fixed join

Under the negation of the core-involution conclusion, an outer involution y
in H = C_G(z) gives the actual subgroup X = Ω₁(C_H(y)), mapped into G.
Writing E for the mapped derived two-core and Z = E ∩ C_G(y), we have
|E| = 32, |Z| = 8, |X| = 16 and z ∈ Z. Moreover E normalizes X,
C_E(X) = E ∩ X = Z, and C_E(x) = Z for every x in X outside Z.

The fixed-join theorem is applied inside H, where the derived two-core is
normal. Its conclusions are then transported through the actual inclusion
H → G. This avoids imposing ambient normality on E. These identities give
the four-element suborbits and the order-four elementary automorphism image
used in the final contradiction. The fixed-join geometry is also exposed
without the core-involution premise, for the order-sixteen case of Lemma 5.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 3, printed p.675, and the order-sixteen case on p.676.
-/

open Subgroup
namespace Stellmacher.Recognition

/-- The geometry of the outer fixed join, independently of the other core involutions. -/
public theorem parrott_outer_fixed_join_geometry
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let Z := E ⊓ centralizer ({(y : G)} : Set G)
      let X := zpowers (y : G) ⊔ Z
      Nat.card E = 32 ∧ Nat.card Z = 8 ∧ Nat.card X = 16 ∧
        IsElementaryAbelian 2 E ∧ IsElementaryAbelian 2 X ∧
        z ∈ Z ∧ Z ≤ X ∧ X ≤ H ∧ E ≤ normalizer (X : Set G) ∧
        E ⊓ centralizer (X : Set G) = Z ∧ E ⊓ X = Z ∧
        ∀ x : G, x ∈ X → x ∉ Z → E ⊓ centralizer ({x} : Set G) = Z := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  intro y hy hyJ
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let X := zpowers (y : G) ⊔ Z
  let ZH := DH ⊓ centralizer ({y} : Set H)
  let XH := zpowers y ⊔ ZH
  change Nat.card E = 32 ∧ Nat.card Z = 8 ∧ Nat.card X = 16 ∧
    IsElementaryAbelian 2 E ∧ IsElementaryAbelian 2 X ∧
    z ∈ Z ∧ Z ≤ X ∧ X ≤ H ∧ E ≤ normalizer (X : Set G) ∧
    E ⊓ centralizer (X : Set G) = Z ∧ E ⊓ X = Z ∧ _
  obtain ⟨hcenter, _, _, _, hupper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hDHmap : DH.map H.subtype = E := map_map _ _ _
  have hyDH : y ∉ DH := fun hyD => hyJ (map_subtype_le D hyD)
  obtain ⟨_, hENH, hCXH, hEXH, houterH⟩ := elementary_involution_fixed_join_data DH y hy hyDH
  change DH ≤ normalizer (XH : Set H) at hENH
  change DH ⊓ centralizer (XH : Set H) = ZH at hCXH
  change DH ⊓ XH = ZH at hEXH
  have hZmap : ZH.map H.subtype = Z := by
    apply le_antisymm
    · rintro a ⟨b, hb, rfl⟩
      exact ⟨hDHmap ▸ mem_map_of_mem H.subtype hb.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hb.2))⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := hDHmap.symm ▸ ha.1
      refine ⟨b, ⟨hb, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))
  obtain ⟨hXelem, hXcard, _⟩ := parrott_outer_fixed_join_data z h y hy hyJ
  have hXjoin : X = zpowers (y : G) ⊔ Z := rfl
  have hXmap : XH.map H.subtype = X := by
    change (zpowers y ⊔ ZH).map H.subtype = X
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZmap]
    exact hXjoin.symm
  have hZX : Z ≤ X := by rw [hXjoin]; exact le_sup_right
  have hXH : X ≤ H := by rw [← hXmap]; exact map_subtype_le _
  have hEN : E ≤ normalizer (X : Set G) := by
    rw [← hDHmap, ← hXmap]
    exact (map_mono hENH).trans (le_normalizer_map H.subtype)
  have hCX : E ⊓ centralizer (X : Set G) = Z := by
    apply le_antisymm
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := hDHmap.symm ▸ ha.1
      have hbC : b ∈ centralizer (XH : Set H) := by
        intro c hc
        apply Subtype.ext
        exact ha.2 (c : G) (hXmap ▸ mem_map_of_mem H.subtype hc)
      rw [← hZmap]
      exact mem_map_of_mem H.subtype (hCXH ▸ (show b ∈ DH ⊓ centralizer (XH : Set H) from ⟨hb, hbC⟩))
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := hZmap.symm ▸ ha
      have hb' : b ∈ DH ⊓ centralizer (XH : Set H) := hCXH.symm ▸ hb
      refine ⟨hDHmap ▸ mem_map_of_mem H.subtype hb'.1, ?_⟩
      intro c hc
      obtain ⟨d, hd, rfl⟩ := hXmap.symm ▸ hc
      exact congrArg H.subtype (hb'.2 d hd)
  have hEX : E ⊓ X = Z := by
    rw [← hDHmap, ← hXmap, ← Subgroup.map_inf DH XH H.subtype H.subtype_injective,
      hEXH, hZmap]
  have houter (x : G) (hx : x ∈ X) (hxZ : x ∉ Z) :
      E ⊓ centralizer ({x} : Set G) = Z := by
    obtain ⟨xH, hxH, rfl⟩ := hXmap.symm ▸ hx
    have hxZH : xH ∉ ZH := fun hh => hxZ (hZmap ▸ mem_map_of_mem H.subtype hh)
    have hlocal := houterH xH hxH hxZH
    change DH ⊓ centralizer ({xH} : Set H) = ZH at hlocal
    apply le_antisymm
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := hDHmap.symm ▸ ha.1
      have hbC : b ∈ centralizer ({xH} : Set H) :=
        mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2))
      rw [← hZmap]
      exact mem_map_of_mem H.subtype (hlocal ▸ (show b ∈ DH ⊓ centralizer ({xH} : Set H) from ⟨hb, hbC⟩))
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := hZmap.symm ▸ ha
      have hb' : b ∈ DH ⊓ centralizer ({xH} : Set H) := hlocal.symm ▸ hb
      exact ⟨hDHmap ▸ mem_map_of_mem H.subtype hb'.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hb'.2))⟩
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := D) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hZcard : Nat.card Z = 8 := by
    have hc := parrott_outer_involution_fixed_card z h y hy hyJ
    have hm := card_map_of_injective
      (K := (centralizer ({(y : G)} : Set G)).subgroupOf E) (f := E.subtype) E.subtype_injective
    rw [subgroupOf_map_subtype] at hm
    exact (show Nat.card Z = Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) by
      simpa only [Z, inf_comm] using hm).trans hc
  have hzE : z ∈ E := by
    have hzC : z ∈ (center J).map (H.subtype.comp J.subtype) := hcenter.symm ▸ mem_zpowers z
    apply map_mono (show center J ≤ D from ?_) hzC
    rw [show D = Subgroup.upperCentralSeries J 2 from hupper, ← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono J (by decide : 1 ≤ 2)
  have hzZ : z ∈ Z := ⟨hzE, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp y.property).symm⟩
  exact ⟨hEcard, hZcard, hXcard, inferInstance, hXelem, hzZ, hZX, hXH,
    hEN, hCX, hEX, houter⟩

/-- Fixed-join geometry in G for the actual omega subgroup, with its cardinalities. -/
public theorem parrott_outer_omega_geometry
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      let Z := E ⊓ centralizer ({(y : G)} : Set G)
      Nat.card E = 32 ∧ Nat.card Z = 8 ∧ Nat.card X = 16 ∧
        IsElementaryAbelian 2 E ∧ IsElementaryAbelian 2 X ∧
        z ∈ Z ∧ Z ≤ X ∧ X ≤ H ∧ E ≤ normalizer (X : Set G) ∧
        E ⊓ centralizer (X : Set G) = Z ∧ E ⊓ X = Z ∧
        ∀ x : G, x ∈ X → x ∉ Z → E ⊓ centralizer ({x} : Set G) = Z := by
  dsimp only
  intro hcore y hy hyJ
  have hX := (parrott_outer_centralizer_omega z h hcore y hy hyJ).2.1
  rw [hX]
  exact parrott_outer_fixed_join_geometry z h y hy hyJ

end Stellmacher.Recognition
