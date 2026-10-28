module

public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Detecting local characteristic p at the center of a Sylow subgroup

Let T be a Sylow p-subgroup of a finite group G and let M contain T with
nontrivial p-core Q. A central subgroup of order p in Q ∩ T supplies
z ∈ Q ∩ Z(T). If C_G(z) has characteristic p, then C_M(z) does too:
it contains the full Sylow subgroup T of C_G(z). Moreover C_M(Q) lies
in C_M(z). The core-centralizer overgroup criterion therefore proves that
M has characteristic p.

Consequently, checking the centralizers of prime-order elements in Z(T)
covers every normalizer of a nontrivial p-subgroup that contains T.
Normality and prime cores are intrinsic to the indicated local group.

For p = 2 this is the even-characteristic criterion used in the converse
of Aschbacher–Smith, Theorem 0.1.2, printed pp.3–4 (also pp.481–482),
combined manuscript of 1 March 2004. It uses only Sylow containment,
normal-subgroup fixed points and characteristic-p inheritance.
-/

public section

open Subgroup

namespace Subgroup

/-- Detect characteristic p in a Sylow overgroup using its central elements. -/
theorem sylow_overgroup_core_selfCentralizing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hne : pCore p M ≠ ⊥)
    (hc : ∀ z : T, z ∈ center T → orderOf z = p →
      centralizer (pCore p (centralizer ({(z : G)} : Set G)) :
        Set (centralizer ({(z : G)} : Set G))) ≤
          pCore p (centralizer ({(z : G)} : Set G))) :
    centralizer (pCore p M : Set M) ≤ pCore p M := by
  let S : Sylow p M := T.subtype hTM
  have hQS : pCore p M ≤ (S : Subgroup M) := pCore_isPGroup.le_sylow_of_normal S
  let Q := (pCore p M).subgroupOf (S : Subgroup M)
  let : Nontrivial (pCore p M) := (nontrivial_iff_ne_bot _).mpr hne
  have hQ : Nontrivial Q := (subgroupOfEquivOfLe hQS).nontrivial
  let : Fact (IsPGroup p S) := ⟨S.isPGroup'⟩
  obtain ⟨Z, _, hZQ, hZcard, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := p) Q hQ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p (by rw [hZcard])
  let zM : M := (z : S)
  let zT : T := ⟨zM, (z : S).property⟩
  have hzT : orderOf zT = p := by
    have h := (orderOf_coe z).trans hz
    have h' := (orderOf_coe (z : S)).trans h
    have h'' := (orderOf_coe zM).trans h'
    exact (orderOf_coe zT).symm.trans h''
  have hzcenter : zT ∈ center T := by
    apply (Subgroup.mem_center_iff (G := T)).mpr
    intro t
    have ht : (⟨⟨t, hTM t.property⟩, t.property⟩ : S) * (z : S) =
        (z : S) * (⟨⟨t, hTM t.property⟩, t.property⟩ : S) :=
      mem_center_iff.mp (hZcenter z.property) _
    exact Subtype.ext (congrArg (fun x : S => ((x : M) : G)) ht)
  let C := centralizer ({(zT : G)} : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzcenter ⟨t, ht⟩))
  have hMC : centralizer (pCore p (M.subgroupOf C) : Set (M.subgroupOf C)) ≤
      pCore p (M.subgroupOf C) :=
    centralizer_pCore_le_of_sylow_le (T.subtype hTC) (M.subgroupOf C)
      (fun x hx => hTM hx) (hc zT hzcenter hzT)
  let e : centralizer ({zM} : Set M) ≃* M.subgroupOf C :=
    { toFun := fun x => ⟨⟨x, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
        x.val.property⟩
      invFun := fun x => ⟨⟨x, x.property⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  apply centralizer_pCore_le_of_overgroup p (centralizer ({zM} : Set M))
    ((Theory.Quasithin.centralizer_pCore_le_iff p e).mpr hMC)
  exact centralizer_le (Set.singleton_subset_iff.mpr (hZQ z.property))

/-- Normalizers containing a full Sylow subgroup have self-centralizing cores
when the centralizers of its central prime-order elements do. -/
theorem normalizer_core_selfCentralizing_of_sylow_centralizers
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (Q : Subgroup G) (hp : IsPGroup p Q) (hne : Q ≠ ⊥)
    (hTN : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hc : ∀ z : T, z ∈ center T → orderOf z = p →
      centralizer (pCore p (centralizer ({(z : G)} : Set G)) :
        Set (centralizer ({(z : G)} : Set G))) ≤
          pCore p (centralizer ({(z : G)} : Set G))) :
    centralizer (pCore p (normalizer (Q : Set G)) :
      Set (normalizer (Q : Set G))) ≤ pCore p (normalizer (Q : Set G)) := by
  apply sylow_overgroup_core_selfCentralizing T _ hTN ?_ hc
  have hcore : Q.subgroupOf (normalizer (Q : Set G)) ≤
      pCore p (normalizer (Q : Set G)) := le_sSup ⟨inferInstance, hp.comap_subtype⟩
  intro hb
  have hQ : Q.subgroupOf (normalizer (Q : Set G)) = ⊥ := bot_unique (hb ▸ hcore)
  apply hne
  rw [← map_subgroupOf_eq_of_le (le_normalizer (H := Q)), hQ, map_bot]

end Subgroup
