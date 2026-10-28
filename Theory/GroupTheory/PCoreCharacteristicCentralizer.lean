module

public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction

/-!
# Detecting a core centralizer on a characteristic subgroup

In a finite group with self-centralizing p-core Q, a characteristic subgroup
E of Q detects its ambient centralizer whenever restriction Aut(Q) → Aut(E)
has p-group kernel. The conjugation kernel is a p-group, so the composite
kernel is a normal p-group and lies in Q.

Two intrinsic sufficient conditions are proved here: E is self-centralizing
in Q, or E is abelian and has index two in its centralizer in the two-group Q.
For the second condition, C_Q(E) is characteristic and self-centralizing.
An automorphism fixing E has a two-power that fixes C_Q(E), and another
two-power is the identity.

This supplies a correction route for Aschbacher--Smith, Lemma 14.2.21,
printed p.989, without identifying the second center with C_Q([Q,Q]).
The finite-group argument uses the restriction-kernel theorem and the
index-two displacement calculation in the imported modules.
-/

namespace Subgroup

/-- Detection up to a p-group kernel recovers the ambient centralizer. -/
public theorem centralizer_le_pCore_of_characteristic_detection
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G)
    (E : Subgroup (pCore p G)) [E.Characteristic]
    (hdetect : IsPGroup p (MulAut.characteristic E).ker) :
    centralizer (E.map (pCore p G).subtype : Set G) ≤ pCore p G := by
  let Q := pCore p G
  let conjugation : G →* MulAut Q := MulAut.conjNormal
  let action := (MulAut.characteristic E).comp conjugation
  have hconjker : conjugation.ker ≤ Q := by
    intro g hg
    apply hcentral
    rw [mem_centralizer_iff]
    intro q hq
    have hfix := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G))
      (MonoidHom.mem_ker.mp hg)
    change g * q * g⁻¹ = q at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hkernel : IsPGroup p action.ker :=
    hdetect.comap_of_ker_isPGroup conjugation (pCore_isPGroup.to_le hconjker)
  have hle : action.ker ≤ pCore p G := le_sSup ⟨inferInstance, hkernel⟩
  intro g hg
  apply hle
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro e
  apply Subtype.ext
  apply Subtype.ext
  change g * (e.1 : G) * g⁻¹ = (e.1 : G)
  have hcomm := mem_centralizer_iff.mp hg (e.1 : G)
    (mem_map_of_mem Q.subtype e.property)
  rw [← hcomm, mul_inv_cancel_right]

/-- A self-centralizing characteristic subgroup of the core detects its
ambient centralizer. -/
public theorem centralizer_le_pCore_of_characteristic_selfCentralizing
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G)
    (E : Subgroup (pCore p G)) [E.Characteristic]
    (hself : centralizer (E : Set (pCore p G)) ≤ E) :
    centralizer (E.map (pCore p G).subtype : Set G) ≤ pCore p G :=
  centralizer_le_pCore_of_characteristic_detection p hcentral E
    (E.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (pCore_isPGroup.to_subgroup E) hself)

/-- The index-two centralizer case also detects automorphisms up to a
two-group kernel. The abelianness condition is `hEC`. -/
public theorem isPGroup_characteristic_restriction_kernel_of_centralizer_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E : Subgroup P) [E.Characteristic]
    (hEC : E ≤ centralizer (E : Set P))
    (hi : E.relIndex (centralizer (E : Set P)) = 2) :
    IsPGroup 2 (MulAut.characteristic E).ker := by
  let C := centralizer (E : Set P)
  let R := E.subgroupOf C
  have hCker : IsPGroup 2 (MulAut.characteristic C).ker :=
    C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (centralizer_le hEC)
  obtain ⟨n, hn⟩ := ((hP.to_subgroup C).to_subgroup R).exists_card_eq
  intro f
  have hfixed (e : P) (he : e ∈ E) : (f : MulAut P) e = e :=
    congrArg Subtype.val (DFunLike.congr_fun f.property (⟨e, he⟩ : E))
  have hpow : (MulAut.characteristic C (f : MulAut P)) ^ Nat.card R = 1 :=
    pow_card_eq_one_of_fixed_index_two R hi _ (by
      intro x hx
      apply Subtype.ext
      exact hfixed x hx)
  have hmem : (f : MulAut P) ^ 2 ^ n ∈ (MulAut.characteristic C).ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hn]
    exact hpow
  obtain ⟨m, hm⟩ := hCker ⟨_, hmem⟩
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  change (f : MulAut P) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

/-- The index-two centralizer criterion inside the two-core gives ambient
centralizer containment. -/
public theorem centralizer_le_twoCore_of_characteristic_centralizer_index_two
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (E : Subgroup (pCore 2 G)) [E.Characteristic]
    (hEC : E ≤ centralizer (E : Set (pCore 2 G)))
    (hi : E.relIndex (centralizer (E : Set (pCore 2 G))) = 2) :
    centralizer (E.map (pCore 2 G).subtype : Set G) ≤ pCore 2 G :=
  centralizer_le_pCore_of_characteristic_detection 2 hcentral E
    (isPGroup_characteristic_restriction_kernel_of_centralizer_index_two
      pCore_isPGroup E hEC hi)

end Subgroup
