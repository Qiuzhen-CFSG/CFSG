module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Subnormal p-subgroups and the p-core

A `p`-subgroup that is subnormal in a finite group lies in its `p`-core.  The
theorem here is stated for ambient subgroups `A ≤ B`: subnormality is expressed
inside `B`, while the conclusion maps `pCore p B` back into the common ambient
group.

The proof follows a subnormal chain from `A` to `B`.  At each normal step, the
`p`-core of the smaller subgroup is characteristic, so its ambient image is a
normal `p`-subgroup of the next subgroup and therefore lies in the next
`p`-core.  This standard result supplies the subnormal-p-subgroup step in
Stellmacher's proof of (4.5).
-/

noncomputable section

universe u

private def pCoreAmbient
    {G : Type u} [Group G] (P : Subgroup G) (p : ℕ) : Subgroup G :=
  (pCore p P).map P.subtype

private theorem pCoreAmbient_isPGroup
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (p : ℕ) : IsPGroup p (pCoreAmbient P p) := by
  exact (pCore_isPGroup (G := P) (p := p)).map P.subtype

private def IsNormalIn
    {G : Type u} [Group G] (A B : Subgroup G) : Prop :=
  A ≤ B ∧ ∀ b : G, b ∈ B → ∀ a : G, a ∈ A → b * a * b⁻¹ ∈ A

private theorem map_characteristic_isNormalIn
    {G : Type u} [Group G] {H N : Subgroup G}
    (K : Subgroup H) (hKchar : K.Characteristic)
    (hHnormal : IsNormalIn H N) :
    IsNormalIn (K.map H.subtype) N := by
  refine ⟨(Subgroup.map_subtype_le K).trans hHnormal.1, ?_⟩
  intro n hn x hx
  rcases (Subgroup.mem_map).1 hx with ⟨k, hk, rfl⟩
  let e : H ≃* H :=
    { toFun := fun y ↦ ⟨n * y.1 * n⁻¹, hHnormal.2 n hn y.1 y.2⟩
      invFun := fun y ↦ ⟨n⁻¹ * y.1 * n, by
        have hy := hHnormal.2 n⁻¹ (N.inv_mem hn) y.1 y.2
        simpa using hy⟩
      left_inv := by intro y; ext; group
      right_inv := by intro y; ext; group
      map_mul' := by
        intro a b
        ext
        change n * ↑(a * b) * n⁻¹ =
          (n * ↑a * n⁻¹) * (n * ↑b * n⁻¹)
        rw [Subgroup.coe_mul]
        group }
  have hek : e k ∈ K := by
    rw [← (Subgroup.characteristic_iff_map_eq.mp hKchar) e]
    exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  exact Subgroup.mem_map.mpr ⟨e k, hek, rfl⟩

private theorem pCoreAmbient_mono_of_isNormalIn
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hAB : IsNormalIn A B) :
    pCoreAmbient A p ≤ pCoreAmbient B p := by
  have hQnormal : IsNormalIn (pCoreAmbient A p) B := by
    simpa [pCoreAmbient] using
      map_characteristic_isNormalIn (pCore p A)
        (inferInstance : (pCore p A).Characteristic) hAB
  let Q : Subgroup B := (pCoreAmbient A p).subgroupOf B
  have hQnormalB : Q.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQnormal.1]
    intro x b hx hb
    exact hQnormal.2 b hb x hx
  have hQp : IsPGroup p Q :=
    (pCoreAmbient_isPGroup A p).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQnormal.1).symm
  have hQle : Q ≤ pCore p B := le_sSup ⟨hQnormalB, hQp⟩
  have hmap := Subgroup.map_mono (f := B.subtype) hQle
  have hQmap : Q.map B.subtype = pCoreAmbient A p :=
    Subgroup.map_subgroupOf_eq_of_le hQnormal.1
  rw [hQmap] at hmap
  exact hmap

/-- A subnormal `p`-subgroup of `B`, expressed as an ambient subgroup, lies
in the ambient image of `O_p(B)`. -/
public theorem isPGroup_le_pCoreAmbient_of_isSubnormalIn
    {G : Type u} [Group G] [Finite G]
    (B A : Subgroup G) (p : ℕ)
    (hAB : A ≤ B) (hsub : (A.subgroupOf B).IsSubnormal)
    (hAp : IsPGroup p A) : A ≤ (pCore p B).map B.subtype := by
  rcases (Subgroup.IsSubnormal.isSubnormal_iff
      (G := B) (H := A.subgroupOf B)).1 hsub with
    ⟨n, f, hmono, hnormal, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n →
      A ≤ pCoreAmbient ((f i).map B.subtype) p := by
    intro i hi
    induction i with
    | zero =>
        have hK0 : (f 0).map B.subtype = A := by
          rw [hf0]
          exact Subgroup.map_subgroupOf_eq_of_le hAB
        rw [hK0]
        intro a ha
        change a ∈ (pCore p A).map A.subtype
        have htop : (⊤ : Subgroup A) ≤ pCore p A :=
          le_sSup ⟨inferInstance, hAp.to_subgroup ⊤⟩
        exact ⟨⟨a, ha⟩, htop trivial, rfl⟩
    | succ i ih =>
        have hKi : IsNormalIn ((f i).map B.subtype)
            ((f (i + 1)).map B.subtype) := by
          refine ⟨Subgroup.map_mono (hmono (Nat.le_succ i)), ?_⟩
          intro b hb x hx
          rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
          rcases (Subgroup.mem_map).1 hb with ⟨b0, hb0, rfl⟩
          have hc := (Subgroup.normal_subgroupOf_iff
            (hmono (Nat.le_succ i))).mp (hnormal i) x0 b0 hx0 hb0
          exact Subgroup.mem_map.mpr
            ⟨b0 * x0 * b0⁻¹, hc, by simp [mul_assoc]⟩
        exact (ih (Nat.le_of_succ_le hi)).trans
          (pCoreAmbient_mono_of_isNormalIn _ _ p hKi)
  have hlast := hmain n le_rfl
  have htop : (⊤ : Subgroup B).map B.subtype = B := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := B))
  rw [hfn, htop] at hlast
  simpa [pCoreAmbient] using hlast
