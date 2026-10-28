module
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.Quasithin.Rank
public import Theory.Alternating.FivePairBorelTorus

/-!
# Cubic planes and centers above an A₅ section

Let J be a normal C-component and K ≤ J have quotient A₅ by its two-core.
Suppose an elementary subgroup A of order nine meets J inside K, and the
ambient three-rank is at most two. Then the center of J/O₂(J) has order
prime to three. In the ambient two-core quotient, the literal image of A
still has order nine and meets the image of J inside the image of K.
Its intersection with the center lies in the two-core of the A₅ section,
so is trivial. The rank-two disjoint-plane theorem excludes a central
three-element, including when A lies outside J.

Source application: Aschbacher–Smith, Proposition 9.3.1, printed p.732,
the containing-component reduction. The final rank argument is A.1.27.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.A5PlaneCenter
variable {X : Type*} [Group X] [Finite X]

private theorem center_coprime_of_five_intersection
    (I K A : Subgroup X) [I.Normal] [IsElementaryAbelian 3 A]
    (hX : primeRank 3 X ≤ 2) (hA : Nat.card A = 9)
    (hKI : K ≤ I) (hAK : A ⊓ I ≤ K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Nat.Coprime 3 (Nat.card (center I)) := by
  let Z := (center I).map I.subtype
  let : Z.Normal := inferInstance
  have hd : Disjoint A Z := by
    apply disjoint_def.mpr
    intro x hxA hxZ
    obtain ⟨j,hj,rfl⟩ := hxZ
    have hxK : (j : X) ∈ K := hAK ⟨hxA,j.property⟩
    let k : K := ⟨j,hxK⟩
    have hk : k ∈ center K := by
      apply mem_center_iff.mpr
      intro l
      apply Subtype.ext
      exact congrArg (fun z : I => (z : X)) ((mem_center_iff.mp hj) ⟨l,hKI l.property⟩)
    let f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
    have hfk : f k ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨l,rfl⟩ := hf a
      simpa only [map_mul] using congrArg f ((mem_center_iff.mp hk) l)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hfk
    have hkQ : k ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff k).mp
      exact eK.map_eq_one_iff.mp hfk
    have hjQ : (j : X) ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype hkQ
    exact disjoint_def.mp ((IsElementaryAbelian.isPGroup 3 A).disjoint_of_coprime
      (isPGroup_pCoreIn 2 K) (by decide)) hxA hjQ
  have hh := coprime_card_of_normalized_disjoint_plane hX A Z hA
    le_normalizer_of_normal hd
  simpa only [Z,card_map_of_injective I.subtype_injective] using hh

omit [Finite X] in
private theorem threeGroup_le_normal_of_le_join_twoCore
    (J C : Subgroup X) [J.Normal] (hC : IsPGroup 3 C)
    (hCJ : C ≤ J ⊔ pCore 2 X) : C ≤ J := by
  let r := QuotientGroup.mk' J
  have hCr : C.map r ≤ (pCore 2 X).map r := by
    have hh := map_mono (f := r) hCJ
    simpa only [r,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] using hh
  have hb : C.map r = ⊥ := disjoint_self.mp
    ((hC.map r).disjoint_of_coprime (((pCore_isPGroup (p := 2) (G := X)).map r).to_le hCr)
      (by decide))
  simpa only [r,QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hb

omit [Finite X] in
/-- A three-subgroup intersects a normal subgroup exactly after quotienting
by the ambient two-core. -/
theorem threeGroup_inf_normal_image_twoCore
    (J A : Subgroup X) [J.Normal] (hA : IsPGroup 3 A) :
    A.map (QuotientGroup.mk' (pCore 2 X)) ⊓ J.map (QuotientGroup.mk' (pCore 2 X)) =
      (A ⊓ J).map (QuotientGroup.mk' (pCore 2 X)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hCJ : A ⊓ (J ⊔ pCore 2 X) ≤ J :=
    threeGroup_le_normal_of_le_join_twoCore J _ (hA.to_le inf_le_left) inf_le_right
  apply le_antisymm
  · rintro x ⟨⟨a,ha,rfl⟩,hj⟩
    have hj' : a ∈ J ⊔ pCore 2 X := by
      change a ∈ (J.map q).comap q at hj
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hj
    exact ⟨a,⟨ha,hCJ ⟨ha,hj'⟩⟩,rfl⟩
  · exact map_inf_le _ _ _

/-- A normal C-component containing an A₅ section cannot have three-divisible
center modulo its two-core when an elementary three-plane meets it inside
that section and the ambient three-rank is at most two. -/
theorem center_twoCore_quotient_coprime_three
    (J K A : Subgroup X) (hJ : J.IsCComponent) [J.Normal]
    [IsElementaryAbelian 3 A] (hX : primeRank 3 X ≤ 2)
    (hA : Nat.card A = 9) (hKJ : K ≤ J) (hAK : A ⊓ J ≤ K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let I := J.map q
  let : I.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 3 (A.map q) := IsElementaryAbelian.map q
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hAc : Nat.card (A.map q) = 9 := by
    have hi := Theory.AlternatingFive.injective_on_three_subgroup q hker A
      (IsElementaryAbelian.isPGroup 3 A)
    have hr : (q.comp A.subtype).range = A.map q := by
      rw [MonoidHom.range_comp,range_subtype]
    exact (hr ▸ (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm).trans hA
  have hAKq : A.map q ⊓ I ≤ K.map q := by
    rw [threeGroup_inf_normal_image_twoCore J A (IsElementaryAbelian.isPGroup 3 A)]
    exact map_mono hAK
  have hk : IsPGroup 2 (q.subgroupMap K).ker := by
    rw [ker_subgroupMap]
    exact hker.comap_subtype
  let ek : ((K.map q) ⧸ pCore 2 (K.map q)) ≃* alternatingGroup (Fin 5) :=
    ((q.subgroupMap K).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective K) hk).symm.trans eK
  have hc := center_coprime_of_five_intersection I (K.map q) (A.map q)
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hX)
    hAc (map_mono hKJ) hAKq ek
  let ej : (J ⧸ pCore 2 J) ≃* I := cComponentTwoCoreQuotientEquiv hJ
  rw [Nat.card_congr (centerCongr ej).toEquiv]
  exact hc

end Theory.GroupTheory.A5PlaneCenter

