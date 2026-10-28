module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.OddActor
public import Theory.GroupTheory.SolvableResidual.NormalizerLifting
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# Odd-actor control in the first J₄ involution centralizer

Restrict the perfect residual and the odd actors to the index-two preimage
of 3.M₂₂. The original cubic survives projection to M₂₂: the solvable kernel
on the perfect simple two-core extension is a two-group. The solvable image
containing a full Sylow has order 384, so an odd actor normalized by that
cubic lies in it. Normalization lifts first through the central scalar C₃,
then through the two-core, which the original full Sylow normalizes.

Both lifts recover the original perfect subgroup as a solvable residual;
no splitting, arbitrary module invariance or full-preimage equality is used.
Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
The imported concrete centralizer maps retain their ATLAS provenance.
-/

public noncomputable section
open Subgroup Sporadic.Mathieu
namespace Janko4.InvolutionCentralizers.First.QuotientExtension
attribute [local irreducible] modelGroup matrixA matrixB

private theorem cover_ker_two : IsPGroup 2 coverProjection.ker := by
  rw [coverProjection_ker]
  exact pCore_isPGroup.comap_subtype

private theorem mathieu_ker_solvable : Group.IsSolvable mathieuProjection.ker := by
  let : Group.IsNilpotent coverProjection.ker := cover_ker_two.isNilpotent
  have hs : Group.IsSolvable coverCentralProjection.ker := by
    rw [coverCentralProjection_ker]
    exact Group.isSolvable_of_comm fun x y =>
      Subtype.ext (mem_center_iff.mp y.property x)
  let := hs
  rw [mathieuProjection,←MonoidHom.comap_ker]
  exact isSolvable_comap_of_solvable_ker _ _

/-- The literal M₂₂ projection detects the normalizer of the same perfect subgroup. -/
theorem mathieu_normalizer_comap (B : Subgroup H) [Group.IsPerfect B]
    (hn : Q.subgroupOf H ≤ normalizer (B : Set H)) :
    (normalizer (B.map mathieuProjection : Set Sporadic.Mathieu.M22)).comap mathieuProjection =
      normalizer (B : Set H) := by
  let : Group.IsNilpotent coverProjection.ker := cover_ker_two.isNilpotent
  let : Group.IsPerfect (B.map coverProjection) := Group.IsPerfect.map _
  have hs : Group.IsSolvable coverCentralProjection.ker := by
    rw [coverCentralProjection_ker]
    exact Group.isSolvable_of_comm fun x y =>
      Subtype.ext (mem_center_iff.mp y.property x)
  let := hs
  have hc : coverCentralProjection.ker ≤ normalizer (B.map coverProjection : Set M22TripleCover) := by
    rw [coverCentralProjection_ker]
    exact center_le_normalizer _
  have hk : coverProjection.ker ≤ normalizer (B : Set H) := by rwa [coverProjection_ker]
  rw [mathieuProjection,←map_map,←comap_comap,
    normalizer_map_comap_eq_of_perfect coverCentralProjection (B.map coverProjection) hc,
    normalizer_map_comap_eq_of_perfect coverProjection B hk]

private theorem cubic_image_card (B E : Subgroup H) [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ pCore 2 B)] (hEB : E ≤ B) (hE : Nat.card E = 3) :
    Nat.card (E.map mathieuProjection) = 3 := by
  let f := mathieuProjection
  let q := f.comp B.subtype
  let : Group.IsSolvable f.ker := mathieu_ker_solvable
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
    (f := B.subtype.subgroupComap f.ker)
    (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun a : f.ker => (a : H)) h)))
  have hk := Theory.GroupTheory.PerfectCoreTwoExtension.ker_isTwoGroup q
  let E' := E.subgroupOf B
  have hE' : Nat.card E' = 3 := (Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv).trans hE
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hd : Disjoint E' q.ker := disjoint_of_coprime_natCard (by
    rw [hE',hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hi : Function.Injective (f.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have he : (⟨x.val,hEB x.property⟩ : B) = 1 := hd.le_bot ⟨x.property,hx⟩
    exact congrArg (fun b : B => (b : H)) he
  let e : E ≃* E.map f := MulEquiv.ofBijective (f.subgroupMap E)
    ⟨fun x y hh => hi (congrArg Subtype.val hh),f.subgroupMap_surjective E⟩
  exact (Nat.card_congr e.toEquiv).symm.trans hE

/-- On the index-two preimage of 3.M22, the original cubic controls the odd actor. -/
theorem cover_odd_actor_normalizes (S : Sylow 2 H) (B D E K : Subgroup H)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hn : Q.subgroupOf H ≤ normalizer (B : Set H))
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup H) ≤ K)
    (hDK : D ≤ K) (hEK : E ≤ K) (hD : Odd (Nat.card D))
    (hE : Nat.card E = 3) (hEB : E ≤ B) (hED : E ≤ normalizer (D : Set H)) :
    D ≤ normalizer (B : Set H) := by
  let f := mathieuProjection
  let := hs
  have hs' : Group.IsSolvable (K.map f) := Group.isSolvable_of_surjective
    (f := f.subgroupMap K) (f.subgroupMap_surjective K)
  have hd := Sporadic.Mathieu.M22SolvableSylow.odd_actor_le_cubic
    (S.mapSurjective (f := f) mathieuProjection_surjective) (K.map f) (D.map f) (E.map f)
    hs' (map_mono hSK) (map_mono hDK) (map_mono hEK)
    (hD.of_dvd_nat (D.card_map_dvd f)) (cubic_image_card B E hEB hE)
    ((map_mono hED).trans (D.le_normalizer_map f))
  have hnorm : D.map f ≤ normalizer (B.map f : Set Sporadic.Mathieu.M22) :=
    hd.trans ((map_mono hEB).trans (B.map f).le_normalizer)
  have hh := map_le_iff_le_comap.mp hnorm
  rwa [mathieu_normalizer_comap B hn] at hh

private theorem odd_le_H (D : Subgroup centralizer) (hd : Odd (Nat.card D)) : D ≤ H := by
  let f := centralizerOuterCharacter
  have hc : Nat.card (D.map f) = 1 := Nat.eq_one_of_dvd_coprimes hd.coprime_two_right
    (D.card_map_dvd f) (by simpa using (D.map f).card_subgroup_dvd_card)
  have hm : D.map f = ⊥ := (D.map f).eq_bot_of_card_eq hc
  rw [←centralizerOuterCharacter_ker]
  simpa only [MonoidHom.comap_bot] using (map_le_iff_le_comap.mp hm.le)

/-- The odd actor in a solvable Sylow overgroup normalizes the original perfect section. -/
theorem odd_actor_normalizes_perfect_section (S : Sylow 2 centralizer) (B D E K : Subgroup centralizer)
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hSB : (S : Subgroup centralizer) ≤ normalizer (B : Set centralizer))
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup centralizer) ≤ K)
    (hDK : D ≤ K) (hEK : E ≤ K) (hD : Odd (Nat.card D))
    (hE : Nat.card E = 3) (hEB : E ≤ B) (hED : E ≤ normalizer (D : Set centralizer)) :
    D ≤ normalizer (B : Set centralizer) := by
  let : Group.IsSolvable (centralizer ⧸ H) := Group.isSolvable_of_surjective
    (f := centralizerQuotientEquivC2.symm.toMonoidHom) centralizerQuotientEquivC2.symm.surjective
  have hBH : B ≤ H := le_of_isPerfect_of_solvable_quotient B H
  have hDH : D ≤ H := odd_le_H D hD
  have hEH : E ≤ H := hEB.trans hBH
  let d := subgroupOfEquivOfLe hBH
  let : Group.IsPerfect (B.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let : IsSimpleGroup (B.subgroupOf H ⧸ pCore 2 (B.subgroupOf H)) := e.isSimpleGroup
  let := hs
  let : Group.IsSolvable (K.subgroupOf H) := Group.isSolvable_of_isSolvable_injective
    (f := H.subtype.subgroupComap K)
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun k : K => (k : centralizer)) he)))
  obtain ⟨P,hPS⟩ := S.exists_subgroupOf_eq_of_normal H
  have hn : Q.subgroupOf H ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact comap_mono ((pCore_isPGroup.le_sylow_of_normal S).trans hSB)
  have hh := cover_odd_actor_normalizes P (B.subgroupOf H) (D.subgroupOf H) (E.subgroupOf H) (K.subgroupOf H)
    hn inferInstance (by rw [hPS]; exact comap_mono hSK) (comap_mono hDK) (comap_mono hEK)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv])
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv]) (comap_mono hEB) (by
      rw [←subgroupOf_normalizer_eq hDH]
      exact comap_mono hED)
  have hm := map_mono (f := H.subtype) hh
  rw [map_subgroupOf_eq_of_le hDH] at hm
  exact hm.trans ((B.subgroupOf H).le_normalizer_map H.subtype) |>.trans (by
    rw [map_subgroupOf_eq_of_le hBH])
end Janko4.InvolutionCentralizers.First.QuotientExtension
