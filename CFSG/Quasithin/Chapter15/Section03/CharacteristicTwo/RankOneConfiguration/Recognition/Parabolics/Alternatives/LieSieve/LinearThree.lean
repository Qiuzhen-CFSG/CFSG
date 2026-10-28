module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.SolvableLift
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms

/-!
# The marked binary linear-three alternative

The actual S₃ shadow makes Y₊S solvable. Its star image intersects L* in a
solvable overgroup of the specified component Sylow two-subgroup. In odd
field degree the scalar center of SL₃ is trivial. For degree greater than
one, the intrinsic solvable-overgroup theorem places this subgroup inside
the Sylow normalizer, whose order is prime to three. But the nontrivial
O^{3′} residual of (M ∩ L)* supplies a factor of three in Y₊*, contradicting
that placement. Thus the field has exactly two elements.

The actual field isomorphism then identifies the model with SL₃(2). Sylow
conjugacy and the binary Bruhat overgroup theorem mark the literal
intersection (M ∩ L)* as the standard line parabolic, which is node zero
in the deleted-cut convention. Each element of S* preserves this parabolic.
The graph coset of Aut(SL₃(2)) cannot preserve a single minimal parabolic,
so its induced action is inner. This supplies the required conjugacy
identity for both labeled parabolic classes under the same marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the second
paragraph of the proof of 15.3.28, printed p.1131 (PDF p.1148), and the
actual SL₃ models in B.5.5–6, printed pp.104–105 (PDF pp.115–116).
The odd degree supplied by 15.3.27(3) remains an explicit input here.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem join_solvable (a : Input d I c) :
    Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let := hs
  obtain ⟨e⟩ := a.facts.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient
    (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr ⟨inferInstance, inferInstance⟩

private theorem yplusStar_three_dvd (a : Input d I c) :
    3 ∣ Nat.card (d.starImage I d.Yplus) := by
  let P := d.starImage I (d.M ⊓ c.L)
  let R := primeToResidual 3 P
  have hd : 3 ∣ Nat.card R := by
    have h := a.componentIntersectionStar_three_dvd
    rw [← R.card_mul_index] at h
    exact (Nat.prime_three.dvd_mul.mp h).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))
  rw [← a.componentIntersectionStar_residual, card_map_of_injective P.subtype_injective]
  exact hd

/-- The solvable S₃ shadow excludes every larger odd-degree linear-three field. -/
theorem linearThree_degree_eq_one (a : Input d I c) (F : ClassificationField)
    (hodd : Odd F.degree)
    (e : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    F.degree = 1 := by
  by_contra hn
  have hn₂ : 2 ≤ F.degree := by have := F.degree_pos; omega
  let L := d.starImage I c.L
  let H := d.starImage I (d.Yplus ⊔ d.S)
  let K := H.subgroupOf L
  let f := e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
    F.card_eq hodd)
  let := join_solvable a
  let : Group.IsSolvable ((d.Yplus ⊔ d.S).subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe a.minimal.1.1.2).toMonoidHom)
      (subgroupOfEquivOfLe a.minimal.1.1.2).injective
  let : Group.IsSolvable H :=
    Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective _)
  let j : K →* H := (L.subtype.comp K.subtype).codRestrict H (fun x => x.property)
  let : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : d.Star I)) h)))
  let : Group.IsSolvable (K.map f.toMonoidHom) :=
    Group.isSolvable_of_surjective (f.toMonoidHom.subgroupMap_surjective K)
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  let Qf := Q.mapSurjective (f := f.toMonoidHom) f.surjective
  have hQK : (Q : Subgroup L) ≤ K := by
    rw [hQ]
    exact comap_mono (map_mono (comap_mono le_sup_right))
  have hN := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F.Carrier hn₂ F.card_eq Qf (K.map f.toMonoidHom) inferInstance (map_mono hQK)
  have hYL : d.starImage I d.Yplus ≤ L := map_mono (comap_mono a.contains)
  have hYK : (d.starImage I d.Yplus).subgroupOf L ≤ K :=
    comap_mono (map_mono (comap_mono le_sup_left))
  have hdK : 3 ∣ Nat.card (K.map f.toMonoidHom) := by
    rw [card_map_of_injective f.injective]
    exact ((Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv).symm ▸
      yplusStar_three_dvd a).trans (card_dvd_of_le hYK)
  exact Matrix.PSL3.LinearThree.BorelStructure.three_not_dvd_card_sylowNormalizer_of_odd
    F.Carrier hodd F.card_eq Qf (hdK.trans (card_dvd_of_le hN))

open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic

private theorem cut_one_mem (v : Fin 3 → ZMod 2) :
    v ∈ cutSpace (Pi.basisFun (ZMod 2) (Fin 3)) (1 : Fin 2) ↔ v 2 = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq, Fin.val_one]
  constructor
  · intro h
    by_contra hn
    exact (by decide : ¬ (2 : Fin 3).val ≤ 1) (h 2 hn)
  · intro hv i hi
    fin_cases i <;> simp_all

private theorem linearThreeParabolic_zero :
    linearThreeParabolic 0 = Matrix.PSL3Two.lineParabolicSL := by
  ext g
  change slEquivLinear 3 g ∈ minimalParabolic (Pi.basisFun (ZMod 2) (Fin 3)) 0 ↔ _
  rw [minimalParabolic, mem_cutStabilizer_maps, Matrix.PSL3Two.lineParabolicSL,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ i ∈ ({0} : Set (Fin 2))ᶜ, ∀ v ∈ cutSpace _ i,
    slEquivLinear 3 g v ∈ cutSpace _ i) ↔
      (∀ ⦃v : Fin 3 → ZMod 2⦄, v 2 = 0 → (g.val.mulVec v) 2 = 0)
  constructor
  · intro h v hv
    exact (cut_one_mem _).mp (h 1 (by decide) v ((cut_one_mem v).mpr hv))
  · intro h i hi v hv
    fin_cases i
    · exact (hi rfl).elim
    · exact (cut_one_mem _).mpr (h ((cut_one_mem v).mp hv))

/-- Mark the literal component intersection over the binary field and prove
preservation of both labeled parabolic conjugacy classes. -/
theorem linearThree_binary_marking (a : Input d I c)
    (e : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nonempty (RankTwoParabolicMarking d I c.L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) linearThreeParabolic) := by
  let L := d.starImage I c.L
  let S := d.starImage I d.S
  let P := d.starImage I (d.M ⊓ c.L)
  let J := P.subgroupOf L
  have hPL : P ≤ L := a.componentIntersectionStar_lt.le
  have hSM : S ≤ d.starImage I (d.MI I) :=
    map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  have hQJ : (Q : Subgroup L) ≤ J := by
    rw [hQ]
    intro x hx
    change (x : d.Star I) ∈ P
    rw [show P = L ⊓ d.starImage I (d.MI I) from a.intersectionStar_eq_inf]
    exact ⟨x.property, hSM hx⟩
  have hJ : J ≠ ⊤ := fun h =>
    a.componentIntersectionStar_lt.not_ge (subgroupOf_eq_top.mp h)
  have hJ₂ : ¬ IsPGroup 2 J := by
    intro hp
    have hd : 3 ∣ Nat.card J := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv]
      exact a.componentIntersectionStar_three_dvd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨f, hSf, hPf⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    (e.trans Matrix.PSL3Two.equiv) Q J hQJ hJ hJ₂
  have hmark : J.map f.toMonoidHom = linearThreeParabolic 0 :=
    hPf.trans linearThreeParabolic_zero.symm
  let b := Pi.basisFun (ZMod 2) (Fin 3)
  let fL := f.trans (slEquivLinear 3)
  have hmarkL : J.map fL.toMonoidHom = minimalParabolic b 0 := by
    change J.map ((slEquivLinear 3).toMonoidHom.comp f.toMonoidHom) = _
    rw [← map_map, hmark]
    exact map_comap_eq_self_of_surjective (f := (slEquivLinear 3).toMonoidHom)
      (slEquivLinear 3).surjective _
  let := a.componentStar_normal
  refine ⟨{ equiv := f, node := 0, intersection := hmark, diagram := ?_ }⟩
  intro s hs i
  let α := componentAction L fL s
  have hα : (minimalParabolic b 0).map α.toMonoidHom = minimalParabolic b 0 := by
    rw [← hmarkL]
    exact componentAction_map_subgroup L fL P hPL s
      (a.sylow_normalizes_componentIntersectionStar hs)
  have hi : α ∈ MulAut.innerSubgroup (LinearGroup 3) := by
    obtain ⟨k, hk | hk⟩ := ThreeAutomorphisms.inner_graph α
    · exact ⟨k, hk.symm⟩
    · have hm := graph_inner_preserves_minimalParabolic_middle b (0 : Fin 2) k
        (by simpa only [hk] using hα)
      norm_num at hm
  obtain ⟨k, hk⟩ := hi
  let l := (slEquivLinear 3).symm k
  refine ⟨l, ?_⟩
  unfold modelSubgroup
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  have hx := congrArg (fun β : MulAut (LinearGroup 3) => β (fL (f.symm x))) hk
  have he : MulAut.conjNormal s (f.symm x) =
      f.symm l * f.symm x * (f.symm l)⁻¹ := by
    apply fL.injective
    rw [map_mul, map_mul, map_inv]
    have hkl : fL (f.symm l) = k := by
      change slEquivLinear 3 (f (f.symm l)) = k
      rw [f.apply_symm_apply]
      exact (slEquivLinear 3).apply_symm_apply k
    rw [hkl]
    change k * fL (f.symm x) * k⁻¹ =
      fL (MulAut.conjNormal s (fL.symm (fL (f.symm x)))) at hx
    rw [fL.symm_apply_apply] at hx
    exact hx.symm
  exact congrArg (fun y : L => (y : d.Star I)) he

/-- The SL₃ branch of 15.3.28: construct the binary minimal-parabolic marking
from the supplied odd-degree model, including its actual field comparison. -/
theorem linearThree_marking (a : Input d I c) (F : ClassificationField)
    (hodd : Odd F.degree)
    (e : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    Nonempty (RankTwoParabolicMarking d I c.L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) linearThreeParabolic) := by
  have hc : Nat.card F.Carrier = 2 := by
    rw [F.card_eq, linearThree_degree_eq_one a F hodd e, pow_one]
  let := Fintype.ofFinite F.Carrier
  let k : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquiv F.Carrier
    (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
  exact linearThree_binary_marking a (e.trans (Atlas.fieldEquivSL 3 k))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
