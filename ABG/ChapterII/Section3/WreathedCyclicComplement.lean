module
public import ABG.ChapterII.Section1.WreathedInvariantSubgroups
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section2.WreathedQuaternionKernelQ
public import ABG.ChapterII.Section2.SylowShapeTransport
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Mathlib.GroupTheory.Complement

/-!
# A full cyclic complement in a wreathed Sylow overgroup

Suppose a Sylow two-subgroup of a finite group G embeds in a wreathed
group of height n, and G is the product of a normal subgroup K and a
disjoint cyclic subgroup A of order 2^n. Then G has a normal two-complement
or K is a Q-group with generalized quaternion Sylow two-subgroups.

Choose a Sylow subgroup containing A and transport the given embedding
by Sylow conjugacy. Map its normal intersection with K and its subgroup A
into the wreathed overgroup. Lemma2(xiii) makes the intersection cyclic or
makes the embedding surjective. Cyclic Sylow transfer and normal-complement
extension prove the first alternative. Otherwise full wreathed fusion
applies. The QD pattern cannot have a nontrivial two-group quotient, while
the D kernel forces the base into K, contradicting its index 2^n≥4. In the
Q pattern the no-index-two kernel lies in K by residual containment; equal
indices identify them. The quaternion-kernel theorem supplies the enlarged
Q-group assertion for that actual K.

Source: Alperin--Brauer--Gorenstein II.3 Lemma3, article p30 (PDF page31).
The normal subgroup K is arbitrary; no Q-group assumption is imposed on it.
-/

namespace ABG
universe u
open BenderSuzuki.External

private theorem cyclic_or_surjective {T W : Type*} [Group T] [Group W]
    {n : ℕ} (hW : IsWreathedOfHeight W n) (f : T →* W) (hf : Function.Injective f)
    (X A : Subgroup T) [X.Normal] [IsCyclic A] (hA : Nat.card A = 2 ^ n)
    (hdis : Disjoint X A) (hsup : X ⊔ A = ⊤) :
    IsCyclic X ∨ Function.Surjective f := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hW
  have hc : Nat.card (A.map f) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective hf, hA]
  let : IsCyclic (A.map f) := isCyclic_of_injective
    (A.equivMapOfInjective f hf).symm.toMonoidHom (A.equivMapOfInjective f hf).symm.injective
  have hn : A.map f ≤ Subgroup.normalizer (X.map f : Set W) :=
    (Subgroup.map_mono (by rw [X.normalizer_eq_top]; exact le_top :
      A ≤ Subgroup.normalizer (X : Set T))).trans
      (X.le_normalizer_map f)
  rcases P.invariant_disjoint_cyclic (X.map f) (A.map f) hc hn
      (Subgroup.disjoint_map hf hdis.symm) with hcyc | htop
  · let : IsCyclic (X.map f) := hcyc
    let e := X.equivMapOfInjective f hf
    exact Or.inl (isCyclic_of_injective e.toMonoidHom e.injective)
  · right
    apply MonoidHom.range_eq_top.mp
    rwa [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map] at htop

private theorem complement_index {G : Type*} [Group G]
    (K A : Subgroup G) [K.Normal] (hdis : Disjoint K A) (hsup : K ⊔ A = ⊤) :
    K.index = Nat.card A := by
  have hcompl : A.IsComplement' K := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdis.symm, fun g => ?_⟩
    have hg : g ∈ A ⊔ K := by rw [sup_comm, hsup]; trivial
    obtain ⟨a, ha, k, hk, h⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    exact ⟨(⟨a, ha⟩, ⟨k, hk⟩), h⟩
  exact hcompl.index_eq_card

private theorem full_wreathed_case {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (hS : IsWreathedOfHeight S n)
    (K : Subgroup G) [K.Normal] (hKi : K.index = 2 ^ n) :
    HasNormalPComplement 2 G ∨ (IsQGroup K ∧ HasGeneralizedQuaternionSylowTwo K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquot : IsPGroup 2 (G ⧸ K) := IsPGroup.of_card (by rwa [← K.index_eq_card])
  have hfour : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hS.1
  obtain ⟨U, V, hf⟩ := exists_wreathedFusionFrame S n hS
  rcases Wreathed.proposition_two S n U V hf with hQD | hQ | hD | hcomp
  · have htop : K = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff (N := K) (x := g)).mp
        (MonoidHom.eq_one_of_no_normal_index_prime hQD.1 hquot (QuotientGroup.mk' K) g)
    rw [htop, Subgroup.index_top] at hKi
    omega
  · obtain ⟨L, hLn, hLi, hLq, hLno⟩ := hQ.1
    let : L.Normal := hLn
    have hle := Subgroup.le_normal_of_no_normal_index_prime L K hLno hquot
    have heq : L = K := Subgroup.eq_of_le_of_card_ge hle (by
      have hLcard := L.card_mul_index
      have hKcard := K.card_mul_index
      rw [hLi] at hLcard
      rw [hKi] at hKcard
      have : 0 < 2 ^ n := by positivity
      nlinarith)
    subst L
    exact Or.inr ⟨normal_quaternion_kernel_isQGroup S hS K hKi hLq hLno, hLq⟩
  · obtain ⟨L, hLn, hLno, P, hPU⟩ := hD.1
    let : L.Normal := hLn
    have hLK := Subgroup.le_normal_of_no_normal_index_prime L K hLno hquot
    have hUK : U ≤ K := by
      rw [← hPU]
      exact (Subgroup.map_subtype_le (P : Subgroup L)).trans hLK
    have hle : U.subgroupOf S ≤ K.comap (S : Subgroup G).subtype :=
      Subgroup.comap_mono hUK
    have hindex := normal_sylow_intersection_index S K hKi
    have hne : K.comap (S : Subgroup G).subtype ≠ ⊤ := by
      intro he
      rw [he, Subgroup.index_top] at hindex
      omega
    have heq : K.comap (S : Subgroup G).subtype = U.subgroupOf S := by
      by_contra he
      exact hne (hf.2.2.2.1.2 _ (lt_of_le_of_ne hle (Ne.symm he)))
    rw [heq] at hindex
    have htwo := S.isPGroup'.index_of_isCoatom _ hf.2.2.2.1
    omega
  · exact Or.inl hcomp.1

public theorem wreathed_cyclic_complement_dichotomy
    {G W : Type u} [Group G] [Finite G] [Group W]
    (R : Sylow 2 G) {n : ℕ} (hW : IsWreathedOfHeight W n)
    (f : R →* W) (hf : Function.Injective f)
    (K A : Subgroup G) [K.Normal] [IsCyclic A]
    (hA : Nat.card A = 2 ^ n) (hsup : K ⊔ A = ⊤) (hdis : Disjoint K A) :
    HasNormalPComplement 2 G ∨ (IsQGroup K ∧ HasGeneralizedQuaternionSylowTwo K) := by
  have hAp : IsPGroup 2 A := IsPGroup.of_card hA
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  let fT : T →* W := f.comp (T.equiv R).toMonoidHom
  have hfT : Function.Injective fT := hf.comp (T.equiv R).injective
  let X := K.comap (T : Subgroup G).subtype
  let B := A.subgroupOf T
  let eB : B ≃* A := Subgroup.subgroupOfEquivOfLe hAT
  let : IsCyclic B := isCyclic_of_injective eB.toMonoidHom eB.injective
  have hBcard : Nat.card B = 2 ^ n := (Nat.card_congr eB.toEquiv).trans hA
  have hXB : Disjoint X B := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hB
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis hx hB)
  have hgen : X ⊔ B = ⊤ := by
    apply top_unique
    intro g _
    have hg : (g : G) ∈ K ⊔ A := by rw [hsup]; trivial
    obtain ⟨k, hk, a, ha, hka⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hkT : k ∈ (T : Subgroup G) := by
      have he : k = (g : G) * a⁻¹ := by rw [← hka, mul_inv_cancel_right]
      rw [he]
      exact T.mul_mem g.property (T.inv_mem (hAT ha))
    exact Subgroup.mem_sup_of_normal_left.mpr
      ⟨⟨k, hkT⟩, hk, ⟨a, hAT ha⟩, ha, Subtype.ext hka⟩
  rcases cyclic_or_surjective hW fT hfT X B hBcard hXB hgen with hX | hfull
  · left
    let P := hallSylowSubgroupOfNormal T K
    let e : P ≃* X := {
      toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
    let : IsCyclic X := hX
    have hPcyc : IsCyclic P := isCyclic_of_injective e.toMonoidHom e.injective
    have hKcomp : HasNormalPComplement 2 K := by
      by_cases htwo : 2 ∣ Nat.card K
      · exact Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1 P
          ((Nat.minFac_eq_two_iff (Nat.card K)).mpr htwo) hPcyc
      · exact hkt_hasNormalPComplement_of_not_dvd_card htwo
    have hquot := Subgroup.quotient_isPGroup_of_sup_eq_top A K hAp (sup_comm K A ▸ hsup)
    exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient K hquot hKcomp
  · let e := MulEquiv.ofBijective fT ⟨hfT, hfull⟩
    have hT := wreathed_equiv e.symm hW
    exact full_wreathed_case T hT K ((complement_index K A hdis hsup).trans hA)

end ABG
