module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Two-perfect subgroups with small Fitting subgroup

If a normal subgroup K has two-group outer automorphism group and solvable
centralizer, and F(G) has order one or three, every two-perfect subgroup D
lies in K F(G). Indeed D acts on K by inner automorphisms and centralizes
the small normal subgroup F(C_G(K)); solvable Fitting self-centralization
then absorbs the centralizer coordinate into F(G).

These elementary finite-group deductions supply the covered residual placement
in Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 13.8.21(1),
printed p.957, using its earlier Fitting alternative 13.8.14 on p.951.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem aut_two_of_card_one_or_three (N : Type*) [Group N] [Finite N]
    (hN : Nat.card N = 1 ∨ Nat.card N = 3) : IsPGroup 2 (MulAut N) := by
  rcases hN with hN | hN
  · have : Subsingleton N := (Nat.card_eq_one_iff_unique.mp hN).1
    have : Subsingleton (MulAut N) := ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact IsPGroup.of_card (n := 0) (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩)
  · let : IsCyclic N := isCyclic_of_prime_card hN
    apply IsPGroup.of_card (n := 1)
    rw [IsCyclic.card_mulAut, hN, Nat.totient_prime Nat.prime_three]
    norm_num

theorem twoPerfect_centralizes_small_normal (D N : Subgroup G) [N.Normal]
    (hD : IsPPerfect 2 D) (hN : Nat.card N = 1 ∨ Nat.card N = 3) :
    D ≤ centralizer (N : Set G) := by
  let f : D →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp D.subtype
  have hf := hD.hom_eq_one_of_isPGroup (aut_two_of_card_one_or_three N hN) f
  intro d hd
  rw [← MulAut.conjNormal_ker_eq_centralizer N]
  exact congrArg (fun a : D →* MulAut N => a ⟨d, hd⟩) hf

theorem twoPerfect_le_normal_sup_fitting (K D : Subgroup G) [K.Normal]
    (hD : IsPPerfect 2 D) (ho : IsPGroup 2 (MulAut.Outer K))
    (hC : Group.IsSolvable (centralizer (K : Set G)))
    (hF : Nat.card (fittingSubgroup G) = 1 ∨ Nat.card (fittingSubgroup G) = 3) :
    D ≤ K ⊔ fittingSubgroup G := by
  let C := centralizer (K : Set G)
  let B := fittingSubgroupOf C
  have hBN : B.Normal := fittingSubgroupOf_normal C inferInstance
  have hBF : B ≤ fittingSubgroup G :=
    le_sSup ⟨hBN, fittingSubgroupOf_isNilpotent C⟩
  have hBc : Nat.card B = 1 ∨ Nat.card B = 3 := by
    have hd := card_dvd_of_le hBF
    rcases hF with hF | hF
    · rw [hF] at hd
      exact Or.inl (Nat.dvd_one.mp hd)
    · rw [hF] at hd
      exact (Nat.dvd_prime Nat.prime_three).mp hd
  have hDC : D ≤ centralizer (B : Set G) :=
    twoPerfect_centralizes_small_normal D B hD hBc
  have hinner : D ≤ K ⊔ C := by
    rw [← MulAut.conjNormal_comap_innerSubgroup K]
    let f : D →* MulAut.Outer K := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      ((MulAut.conjNormal : G →* MulAut K).comp D.subtype)
    have hf := hD.hom_eq_one_of_isPGroup ho f
    intro d hd
    change (MulAut.conjNormal d : MulAut K) ∈ MulAut.innerSubgroup K
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun a : D →* MulAut.Outer K => a ⟨d, hd⟩) hf)
  intro d hd
  obtain ⟨k, hk, c, hc, hkc⟩ := mem_sup_of_normal_left.mp (hinner hd)
  have hkB : k ∈ centralizer (B : Set G) :=
    (le_centralizer_iff.mpr (show B ≤ centralizer (K : Set G) from map_subtype_le _)) hk
  have hcB : c ∈ centralizer (B : Set G) := by
    have he : c = k⁻¹ * d := by rw [← hkc]; group
    rw [he]
    exact (centralizer (B : Set G)).mul_mem ((centralizer (B : Set G)).inv_mem hkB) (hDC hd)
  have hcfit : (⟨c, hc⟩ : C) ∈ fittingSubgroup C := by
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hC
    intro b hb
    exact Subtype.ext (hcB b.val (mem_map_of_mem C.subtype hb))
  rw [← hkc]
  exact (K ⊔ fittingSubgroup G).mul_mem (mem_sup_left hk)
    (mem_sup_right (hBF (mem_map_of_mem C.subtype hcfit)))

omit [Finite G] in
theorem centralizer_solvable_of_centerless_quotient (K : Subgroup G) [K.Normal]
    (hz : center K = ⊥) [Group.IsSolvable (G ⧸ K)] :
    Group.IsSolvable (centralizer (K : Set G)) := by
  let C := centralizer (K : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro c hc
  have hcK : c.val ∈ K := (QuotientGroup.eq_one_iff _).mp hc
  have hcZ : (⟨c.val, hcK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (c.property k.val k.property)
  rw [hz, mem_bot] at hcZ
  exact Subtype.ext (congrArg (fun k : K => (k : G)) hcZ)

omit [Finite G] in
theorem twoPerfect_le_of_le_sup_twoGroup (K D Q : Subgroup G) [K.Normal]
    (hD : IsPPerfect 2 D) (hQ : IsPGroup 2 Q) (hle : D ≤ K ⊔ Q) : D ≤ K := by
  let q := QuotientGroup.mk' K
  have him : D.map q ≤ Q.map q := by
    have h := map_mono (f := q) hle
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] using h
  let f : D →* Q.map q := (q.comp D.subtype).codRestrict _
    (fun d => him (mem_map_of_mem q d.property))
  have hf := hD.hom_eq_one_of_isPGroup (hQ.map q) f
  intro d hd
  apply (QuotientGroup.eq_one_iff _).mp
  exact congrArg (fun a : D →* Q.map q => (a ⟨d, hd⟩).val) hf
end Subgroup
