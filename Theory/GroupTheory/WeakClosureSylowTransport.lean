module

public import Theory.GroupTheory.ConjugationFamilyWeakClosure

/-!
# Transport of weak closure from a Sylow subgroup

Weak closure in one Sylow p-subgroup implies weak closure in every p-overgroup
containing the subgroup. Conjugate an arbitrary containing Sylow subgroup to
the first one. Weak closure forces this conjugator to normalize the subgroup,
so the original weak-closure statement transports back.

For an extension of an inner group `K`, the separate Frattini condition
`G = K N_G(Q)` suffices to transfer internal weak closure of `Q` to `G`.
This condition must be established for the chosen radical, particularly when
graph automorphisms can change its parabolic type.

Source: Sylow conjugacy and the Frattini argument; used with
Aschbacher--Smith I.2.5 in the local arguments of Chapters 10, 12 and 14.
-/

namespace SubgroupFusion

variable {G : Type*} [Group G]

/-- Weak closure in one Sylow subgroup suffices for all p-overgroups. -/
public theorem weakly_closed_in_p_overgroup_of_one_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (Q R : Subgroup G)
    (hQR : Q ≤ R) (hR : IsPGroup p R)
    (hweak : ∀ g : G, Q.conjBy g ≤ (S : Subgroup G) → Q.conjBy g = Q)
    (x : G) (hx : Q.conjBy x ≤ R) : Q.conjBy x = Q := by
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hPS : (P : Subgroup G).conjBy g = (S : Subgroup G) := by
    exact congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
  have hQg : Q.conjBy g ≤ (S : Subgroup G) := by
    rw [← hPS]
    exact Subgroup.map_mono (hQR.trans hRP)
  have hfix := hweak g hQg
  have hQginv : Q.conjBy g⁻¹ = Q := by
    have hback := congrArg (fun U : Subgroup G => U.conjBy g⁻¹) hfix
    rw [Subgroup.conjBy_inv] at hback
    exact hback.symm
  have hbound : (Q.conjBy x).conjBy g ≤ (S : Subgroup G) := by
    rw [← hPS]
    exact Subgroup.map_mono (hx.trans hRP)
  have hfixed : (Q.conjBy x).conjBy g = Q := by
    rw [Subgroup.conjBy_conjBy] at hbound ⊢
    exact hweak (g * x) hbound
  calc
    Q.conjBy x = ((Q.conjBy x).conjBy g).conjBy g⁻¹ :=
      (Subgroup.conjBy_inv _ g).symm
    _ = Q.conjBy g⁻¹ := congrArg (fun U : Subgroup G => U.conjBy g⁻¹) hfixed
    _ = Q := hQginv

/-- All p-overgroups of such a weakly closed subgroup normalize it. -/
public theorem p_overgroup_le_normalizer_of_one_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (Q R : Subgroup G)
    (hQR : Q ≤ R) (hR : IsPGroup p R)
    (hweak : ∀ g : G, Q.conjBy g ≤ (S : Subgroup G) → Q.conjBy g = Q) :
    R ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply weakly_closed_in_p_overgroup_of_one_sylow S Q R hQR hR hweak g
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hQR
  have hfix : R.conjBy g = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hg)
  change Q.conjBy g ≤ R.conjBy g at hmap
  exact hmap.trans hfix.le

/-- A single suitable family proves weak closure in every p-overgroup. -/
public theorem ControlsFusion.member_weakly_closed_in_p_overgroup [Finite G]
    {p : ℕ} [Fact p.Prime] {S : Sylow p G} {Q R : Subgroup G}
    {family : Subgroup G → Prop} (hf : ControlsFusion (S : Subgroup G) family)
    (hQS : Q ≤ (S : Subgroup G)) (hQ : family Q)
    (hnorm : ∀ D E, family D → family E → D ≤ E →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hQR : Q ≤ R) (hR : IsPGroup p R) (g : G) (hg : Q.conjBy g ≤ R) :
    Q.conjBy g = Q :=
  weakly_closed_in_p_overgroup_of_one_sylow S Q R hQR hR
    (fun x hx => hf.member_weakly_closed hQS hQ hnorm x hx) g hg

/-- The Frattini condition for a chosen subgroup transfers internal weak
closure to an extension. It makes the automorphism requirement explicit. -/
public theorem weakly_closed_of_normalizer_frattini (K Q R : Subgroup G)
    [K.Normal] (hQK : Q ≤ K)
    (hcover : K ⊔ Subgroup.normalizer (Q : Set G) = ⊤)
    (hweak : ∀ k : K, (Q.subgroupOf K).conjBy k ≤ R.subgroupOf K →
      (Q.subgroupOf K).conjBy k = Q.subgroupOf K)
    (g : G) (hg : Q.conjBy g ≤ R) : Q.conjBy g = Q := by
  have hgcover : g ∈ K ⊔ Subgroup.normalizer (Q : Set G) := by
    rw [hcover]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_left.mp hgcover
  have hnfix : Q.conjBy n = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hgk : Q.conjBy g = Q.conjBy k := by
    rw [← hkn, Subgroup.conjBy_mul, hnfix]
  have hkbound : Q.conjBy k ≤ R := hgk ▸ hg
  let kK : K := ⟨k, hk⟩
  have hlocal : (Q.subgroupOf K).conjBy kK ≤ R.subgroupOf K := by
    rintro _ ⟨q, hq, rfl⟩
    exact hkbound (Subgroup.mem_map.mpr ⟨(q : G), hq, rfl⟩)
  have hmap := congrArg (fun U : Subgroup K => U.map K.subtype) (hweak kK hlocal)
  have hconj : ((Q.subgroupOf K).conjBy kK).map K.subtype = Q.conjBy k := by
    unfold Subgroup.conjBy
    rw [Subgroup.map_map]
    have hcomp : K.subtype.comp (MulAut.conj kK).toMonoidHom =
        (MulAut.conj k).toMonoidHom.comp K.subtype := by
      ext q
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hQK]
  rw [hconj, Subgroup.map_subgroupOf_eq_of_le hQK] at hmap
  exact hgk.trans hmap

end SubgroupFusion
