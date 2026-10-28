module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersection
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalGeneration
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSplitting


/-!
# Pointwise automorphisms of the source intersection rectangle

The normal cyclic subgroup in the symmetric tensor factor has order three
and acts without fixed points on the rectangle. Its inverse image has
order 192. Maximality and index seven put that inverse image inside the
point–plane intersection. An automorphism fixing the rectangle pointwise
has displacement in that rectangle, since it is self-centralizing. The
fixed-point-free cubic element makes that displacement principal, so the
automorphism is conjugation by a rectangle element.

The final theorem applies the argument to the literal source intersection,
including its relative normal subgroup and quotient map. This supplies the
kernel step in the marked form of Aschbacher, *Sporadic Groups* (1994),
41.3, printed p.222; neither simplicity nor an ambient isomorphism is used.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem fixed_displacement {G : Type*} [Group G]
    (A : Subgroup G) [A.Normal] (hself : centralizer (A : Set G) ≤ A)
    (a : MulAut G) (ha : ∀ x ∈ A, a x = x) (g : G) : a g * g⁻¹ ∈ A := by
  apply hself
  apply mem_centralizer_iff.mpr
  intro x hx
  have hi : g⁻¹ * x * g ∈ A := by
    simpa only [inv_inv] using (inferInstance : A.Normal).conj_mem x hx g⁻¹
  have he := ha (g⁻¹ * x * g) hi
  rw [map_mul, map_mul, map_inv, ha x hx] at he
  have hh := congrArg (fun b => a g * b * g⁻¹) he
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh

private theorem inner_of_fixed_normal_cyclic_quotient
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hself : centralizer (A : Set G) ≤ A)
    {Q : Type*} [Group Q] (q : G →* Q) (hker : q.ker = A) (c : G)
    (hcyclic : (zpowers (q c)).Normal)
    (hfixed : ∀ x ∈ A, c * x = x * c → x = 1)
    (a : MulAut G) (ha : ∀ x ∈ A, a x = x) :
    ∃ u : A, a = MulAut.conj (u : G) := by
  let f : A → A := fun u => ⟨(u : G) * c * (u : G)⁻¹ * c⁻¹, by
    have h := (inferInstance : A.Normal).conj_mem (u : G)⁻¹ (A.inv_mem u.property) c
    simpa only [mul_assoc] using A.mul_mem u.property h⟩
  have hinj : Function.Injective f := by
    intro u v he
    have he' := congrArg Subtype.val he
    change (u : G) * c * (u : G)⁻¹ * c⁻¹ = (v : G) * c * (v : G)⁻¹ * c⁻¹ at he'
    have hc : c * ((v : G)⁻¹ * u) = ((v : G)⁻¹ * u) * c := by
      calc
        _ = (v : G)⁻¹ * ((v : G) * c * (v : G)⁻¹ * c⁻¹) * c * u := by group
        _ = (v : G)⁻¹ * ((u : G) * c * (u : G)⁻¹ * c⁻¹) * c * u := by rw [he']
        _ = _ := by group
    have hz := hfixed ((v : G)⁻¹ * u) (A.mul_mem (A.inv_mem v.property) u.property) hc
    exact Subtype.ext ((inv_mul_eq_one.mp hz).symm)
  obtain ⟨u, hu⟩ := (Finite.surjective_of_injective hinj)
    ⟨a c * c⁻¹, fixed_displacement A hself a ha c⟩
  have hac : a c = (u : G) * c * (u : G)⁻¹ := by
    have h := congrArg Subtype.val hu
    exact (mul_right_cancel h).symm
  let b : MulAut G := a.trans (MulAut.conj (u : G)⁻¹)
  have hbA (x : G) (hx : x ∈ A) : b x = x := by
    change (u : G)⁻¹ * a x * ((u : G)⁻¹)⁻¹ = x
    rw [ha x hx, inv_inv, setLike_mul_comm (A.inv_mem u.property) hx, mul_assoc,
      inv_mul_cancel, mul_one]
  have hbc : b c = c := by
    change (u : G)⁻¹ * a c * ((u : G)⁻¹)⁻¹ = c
    rw [hac]
    group
  have hbg (g : G) : b (g * c * g⁻¹) = g * c * g⁻¹ := by
    have hm : q (g * c * g⁻¹) ∈ zpowers (q c) := by
      rw [map_mul, map_mul, map_inv]
      exact hcyclic.conj_mem _ (mem_zpowers _) _
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hm
    have hx : (g * c * g⁻¹) * (c ^ n)⁻¹ ∈ A := by
      rw [← hker, MonoidHom.mem_ker]
      change q ((g * c * g⁻¹) * (c ^ n)⁻¹) = 1
      rw [map_mul, map_inv, map_zpow, ← hn, mul_inv_cancel]
    have he : g * c * g⁻¹ = ((g * c * g⁻¹) * (c ^ n)⁻¹) * c ^ n := by group
    conv_lhs => rw [he]
    rw [map_mul, hbA _ hx, map_zpow, hbc]
    group
  have hb : b = MulEquiv.refl G := by
    ext g
    have hd : g⁻¹ * b g ∈ A := by
      have hh := (inferInstance : A.Normal).conj_mem _
        (fixed_displacement A hself b hbA g) g⁻¹
      simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
    have he := hbg g
    rw [map_mul, map_mul, map_inv, hbc] at he
    have hc : c * (g⁻¹ * b g) = (g⁻¹ * b g) * c := by
      calc
        _ = g⁻¹ * (g * c * g⁻¹) * b g := by group
        _ = g⁻¹ * (b g * c * (b g)⁻¹) * b g := by rw [he]
        _ = _ := by group
    exact (inv_mul_eq_one.mp (hfixed _ hd hc)).symm
  refine ⟨u, ?_⟩
  ext g
  have he := congrArg (fun f : MulAut G => f g) hb
  change (u : G)⁻¹ * a g * ((u : G)⁻¹)⁻¹ = g at he
  change a g = (u : G) * g * (u : G)⁻¹
  calc
    _ = (u : G) * ((u : G)⁻¹ * a g * ((u : G)⁻¹)⁻¹) * (u : G)⁻¹ := by group
    _ = _ := by rw [he]

end Theory.GroupTheory.TransvectionFive.UniquenessLinear

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem normal_card_not_seven_le
    {M : Type*} [Group M] [Finite M] (H R : Subgroup M) [R.Normal]
    (hmax : IsCoatom H) (hi : H.index = 7) (hR : Nat.card R = 192) : R ≤ H := by
  by_contra hn
  have hs : H ⊔ R = ⊤ := hmax.2 _ (lt_of_le_of_ne le_sup_left (by
    intro he
    exact hn (le_sup_right.trans_eq he.symm)))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes R H (by
    rw [R.normalizer_eq_top]
    exact le_top)
  rw [sup_comm R H, hs, Nat.card_congr Subgroup.topEquiv.toEquiv, hR,
    ← H.index_mul_card, hi] at hc
  have he : 192 * Nat.card H = (Nat.card (R ⊓ H : Subgroup M) * 7) * Nat.card H := by
    rw [hc, mul_assoc]
  have he' := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) he
  omega

variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

private theorem plane_cubic_in_index_seven
    (K : Subgroup G) (hKN : K ≤ sourcePlaneNormalizer F)
    (hmax : IsCoatom (K.subgroupOf (sourcePlaneNormalizer F)))
    (hi : K.relIndex (sourcePlaneNormalizer F) = 7) :
    ∃ c : K, tensorMap F hlinear ⟨c, hKN c.property⟩ = cubic := by
  let f := tensorMap F hlinear
  let R := (zpowers cubic).comap f
  let : (zpowers cubic).Normal := cubic_normal
  have hkR : f.ker ≤ R := ker_le_comap _ _
  have hmap : R.map f = zpowers cubic := map_comap_eq_self (by
    rw [f.range_eq_top_of_surjective (tensorMap_surjective F hlinear)]
    exact le_top)
  have hkcard : Nat.card f.ker = 64 := by
    rw [tensorMap_ker]
    exact (Nat.card_congr (subgroupOfEquivOfLe F.plane.le_normalizer).toEquiv).trans
      (source_plane_card F)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup (sourcePlaneNormalizer F)) f.ker R bot_le hkR
  rw [relIndex_bot_left, relIndex_bot_left, relIndex_ker, hmap,
    Nat.card_zpowers, cubic_order, hkcard] at hc
  have hRI : R ≤ K.subgroupOf (sourcePlaneNormalizer F) :=
    normal_card_not_seven_le _ R hmax hi (by omega)
  obtain ⟨c, hc⟩ := tensorMap_surjective F hlinear cubic
  have hcR : c ∈ R := by
    change f c ∈ zpowers cubic
    rw [hc]
    exact mem_zpowers _
  exact ⟨⟨c, hRI hcR⟩, hc⟩

include hlinear in
theorem plane_fixed_kernel_inner
    (K : Subgroup G) (hAK : F.plane ≤ K) (hKN : K ≤ sourcePlaneNormalizer F)
    (hmax : IsCoatom (K.subgroupOf (sourcePlaneNormalizer F)))
    (hi : K.relIndex (sourcePlaneNormalizer F) = 7)
    (a : MulAut K) (ha : ∀ x : F.plane.subgroupOf K, a x = x) :
    ∃ u : F.plane.subgroupOf K, a = MulAut.conj (u : K) := by
  let A := F.plane.subgroupOf K
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hAK).mpr hKN
  let := marked_rectangle_elementary F 2
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hAK).toMonoidHom (subgroupOfEquivOfLe hAK).injective
  have hself : Subgroup.centralizer (A : Set K) ≤ A := by
    intro x hx
    change (x : G) ∈ F.plane
    rw [← source_plane_centralizer F]
    intro y hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨y, hAK hy⟩ hy)
  obtain ⟨c, hc⟩ := plane_cubic_in_index_seven F hlinear K hKN hmax hi
  let q := (tensorMap F hlinear).comp (inclusion hKN)
  have hq : q.ker = A := by
    ext x
    change tensorMap F hlinear (inclusion hKN x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, tensorMap_ker]
    rfl
  apply inner_of_fixed_normal_cyclic_quotient A hself q hq c
  · change (zpowers (tensorMap F hlinear ⟨c, hKN c.property⟩)).Normal
    rw [hc]
    exact cubic_normal
  · intro x hx he
    apply Subtype.ext
    have h := tensorMap_cubic_fixed F hlinear ⟨c, hKN c.property⟩ hc
      ⟨x, hKN x.property⟩ (by rw [tensorMap_ker]; exact hx)
      (Subtype.ext (congrArg (fun k : K => (k : G)) he))
    exact congrArg (fun k : sourcePlaneNormalizer F => (k : G)) h
  · exact fun x hx => ha ⟨x, hx⟩

include hlinear in
theorem intersection_fixed_kernel_inner
    (a : MulAut (rowThreeIntersection F))
    (ha : ∀ x : F.threeSpace.subgroupOf (rowThreeIntersection F), a x = x) :
    ∃ u : F.threeSpace.subgroupOf (rowThreeIntersection F), a = MulAut.conj (u : rowThreeIntersection F) := by
  let E := oppositeMarking F
  have hN : sourcePlaneNormalizer E = sourceThreeSpaceNormalizer F := by
    change normalizer (E.plane : Set G) = _
    rw [oppositeMarking_plane]
  have hAK : E.plane ≤ rowThreeIntersection F := by
    rw [oppositeMarking_plane]
    exact threeSpace_le_rowThreeIntersection F
  have hKN : rowThreeIntersection F ≤ sourcePlaneNormalizer E := hN.symm ▸ inf_le_right
  have hmax : IsCoatom ((rowThreeIntersection F).subgroupOf (sourcePlaneNormalizer E)) := by
    rw [hN]
    change IsCoatom (((rowNormalizer F) ⊓ sourceThreeSpaceNormalizer F).subgroupOf _)
    rw [inf_subgroupOf_right]
    exact SourceGeometry.local_flag_maximal F hlinear
  have hi : (rowThreeIntersection F).relIndex (sourcePlaneNormalizer E) = 7 := by
    rw [hN]
    change ((rowNormalizer F) ⊓ sourceThreeSpaceNormalizer F).relIndex _ = 7
    rw [inf_relIndex_right]
    exact SourceGeometry.plane_point_index F hlinear
  have ha' : ∀ x : E.plane.subgroupOf (rowThreeIntersection F), a x = x := by
    change ∀ x : (oppositeMarking F).plane.subgroupOf (rowThreeIntersection F), a x = x
    rw [oppositeMarking_plane F]
    exact ha
  have h := plane_fixed_kernel_inner E (oppositeMarking_linearFusion F hlinear)
    (rowThreeIntersection F) hAK hKN hmax hi a ha'
  change ∃ u : (oppositeMarking F).plane.subgroupOf (rowThreeIntersection F),
    a = MulAut.conj (u : rowThreeIntersection F) at h
  rw [oppositeMarking_plane F] at h
  exact h

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
