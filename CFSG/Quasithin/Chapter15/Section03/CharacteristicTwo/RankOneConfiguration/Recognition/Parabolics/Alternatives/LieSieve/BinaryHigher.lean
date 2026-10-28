module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.SolvableLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.BinaryHigher.FlagRecognition
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions

/-!
# Binary higher-rank component geometry and node restrictions

Transport the literal component intersection and the intersected Sylow subgroup
through the supplied model equivalence. The S₃ shadow and embedded O^{3′}
identity give a solvable three-residual, divisibility by three, and order at
most three for each three-subgroup of the intersection. Sylow flag geometry
constructs an actual full basis flag for the specified component Sylow.

For an intersection identified as a minimal parabolic, invariant-overgroup
maximality excludes an inner-only Sylow extension: a larger proper partial
flag would still contain the Sylow subgroup. The concrete binary centre is
trivial, so the component is self-centralizing. An outside actor therefore
induces a genuinely outer automorphism preserving that parabolic. Actual
inverse-transpose geometry forces node 1 in dimension four and is impossible
in dimension five.

The intrinsic flag calculation identifies every proper overgroup from the
proved residual and Sylow data. The final two theorems transport that result
back to the literal component intersection and close the two binary branches
of the source sieve.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the second
paragraph of the proof of 15.3.28, printed p.1131 (PDF p.1148), using
15.3.26–27 and the concrete L₄(2), L₅(2) cases of B.5.5–6, pp.104–105.
-/

@[expose] public section
open Subgroup
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
variable (a : Input d I c)
variable {H : Type*} [Group H] (e : d.starImage I c.L ≃* H)

/-- The literal `(M ∩ L)*` in the specified component model. -/
noncomputable def intersection : Subgroup H :=
  ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map e.toMonoidHom

/-- The original `S* ∩ L*`, intrinsically transported into the model. -/
noncomputable def sylowIntersection : Subgroup H :=
  ((d.starImage I d.S).subgroupOf (d.starImage I c.L)).map e.toMonoidHom

/-- Embed model elements through the chosen equivalence and the actual star inclusion. -/
noncomputable def embedding : H →* d.Star I :=
  (d.starImage I c.L).subtype.comp e.symm.toMonoidHom

omit [Finite G] in
theorem embedding_injective : Function.Injective (embedding e) :=
  (d.starImage I c.L).subtype_injective.comp e.symm.injective

omit [Finite G] in
theorem intersection_map_embedding : (intersection e).map (embedding e) =
    d.starImage I (d.M ⊓ c.L) := by
  rw [intersection, map_map]
  have he : (embedding e).comp e.toMonoidHom = (d.starImage I c.L).subtype := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [he]
  exact map_subgroupOf_eq_of_le (show d.starImage I (d.M ⊓ c.L) ≤ d.starImage I c.L from
    map_mono (comap_mono inf_le_right))

omit [Finite G] in
theorem top_map_embedding : (⊤ : Subgroup H).map (embedding e) = d.starImage I c.L := by
  rw [← MonoidHom.range_eq_map, embedding, MonoidHom.range_comp,
    e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

include a

/-- Properness survives the specified component equivalence. -/
theorem intersection_ne_top : intersection e ≠ ⊤ := by
  intro ht
  have he := congrArg (fun P => P.map (embedding e)) ht
  rw [intersection_map_embedding e, top_map_embedding] at he
  exact a.componentIntersectionStar_lt.ne he

/-- The model intersection is isomorphic to the actual embedded intersection. -/
noncomputable def intersectionEquiv : intersection e ≃* d.starImage I (d.M ⊓ c.L) :=
  ((intersection e).equivMapOfInjective (embedding e) (embedding_injective e)).trans
    (MulEquiv.subgroupCongr (intersection_map_embedding e))

omit [Finite G] in
theorem sylowIntersection_le_intersection : sylowIntersection e ≤ intersection e := by
  apply map_mono
  intro x hx
  change (x : d.Star I) ∈ d.starImage I (d.M ⊓ c.L)
  rw [a.intersectionStar_eq_inf]
  refine ⟨x.property, ?_⟩
  exact map_mono (comap_mono
    (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le)) hx

/-- The model subgroup is Sylow, using normality of the actual component. -/
theorem exists_modelSylow : ∃ U : Sylow 2 H, (U : Subgroup H) = sylowIntersection e := by
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup _).map e.toMonoidHom = _
  rw [hQ]
  rfl

/-- The nontrivial source residual forces a factor of three. -/
theorem intersection_three_dvd : 3 ∣ Nat.card (intersection e) := by
  rw [Nat.card_congr (intersectionEquiv e).toEquiv]
  exact a.componentIntersectionStar_three_dvd

/-- The S₃ shadow bounds actual three-subgroups, rather than only their rank. -/
theorem intersection_three_subgroup_bound (X : Subgroup H)
    (hX : X ≤ intersection e) (hp : IsPGroup 3 X) : Nat.card X ≤ 3 := by
  have hm : X.map (embedding e) ≤ d.starImage I (d.MI I) := by
    calc
      _ ≤ (intersection e).map (embedding e) := map_mono hX
      _ = d.starImage I (d.M ⊓ c.L) := intersection_map_embedding e
      _ ≤ d.starImage I (d.MI I) := by rw [a.intersectionStar_eq_inf]; exact inf_le_right
  have hb := a.star_three_subgroup_card_le_three _ hm (hp.map (embedding e))
  rwa [card_map_of_injective (embedding_injective e)] at hb

/-- The actual S₃ quotient and its normal two-group kernel make Y₊ solvable. -/
theorem yplus_solvable : Group.IsSolvable d.Yplus := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let := hs
  obtain ⟨f⟩ := a.facts.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  let : Group.IsNilpotent (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr
      ⟨inferInstance, inferInstance⟩
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))

/-- Transport the source residual identity before inferring solvability. -/
theorem intersection_residual_solvable : Group.IsSolvable (primeToResidual 3 (intersection e)) := by
  let : Finite H := Finite.of_equiv (d.starImage I c.L) e.toEquiv
  let := yplus_solvable a
  let : Group.IsSolvable (d.Yplus.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (a.yplus_le_intersection.trans inf_le_right)).toMonoidHom)
      (subgroupOfEquivOfLe (a.yplus_le_intersection.trans inf_le_right)).injective
  let : Group.IsSolvable (d.starImage I d.Yplus) :=
    Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective (d.Yplus.subgroupOf I))
  have hs : Group.IsSolvable (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))) := by
    have hh : Group.IsSolvable
        ((primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).map
          (d.starImage I (d.M ⊓ c.L)).subtype) :=
      a.componentIntersectionStar_residual.symm ▸ inferInstance
    let := hh
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).equivMapOfInjective
        (d.starImage I (d.M ⊓ c.L)).subtype Subtype.val_injective).toMonoidHom)
      ((primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).equivMapOfInjective
        (d.starImage I (d.M ⊓ c.L)).subtype Subtype.val_injective).injective
  let f := (intersectionEquiv e).toMonoidHom
  have hm : Group.IsSolvable ((primeToResidual 3 (intersection e)).map f) := by
    rw [map_primeToResidual_of_surjective 3 f (intersectionEquiv e).surjective]
    exact hs
  let := hm
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((primeToResidual 3 (intersection e)).equivMapOfInjective f
      (intersectionEquiv e).injective).toMonoidHom)
    ((primeToResidual 3 (intersection e)).equivMapOfInjective f
      (intersectionEquiv e).injective).injective

/-- Every proper invariant overgroup of the model intersection equals it. -/
theorem invariant_overgroup_eq (P : Subgroup H) (hP : intersection e ≤ P)
    (hproper : P ≠ ⊤)
    (hn : d.starImage I d.S ≤ normalizer (P.map (embedding e) : Set (d.Star I))) :
    P = intersection e := by
  have hPL : P.map (embedding e) ≤ d.starImage I c.L := by
    rw [← top_map_embedding e]
    exact map_mono le_top
  have hne : P.map (embedding e) ≠ d.starImage I c.L := by
    rw [← top_map_embedding e]
    exact fun hh => hproper (map_injective (embedding_injective e) hh)
  have hMP : d.starImage I (d.M ⊓ c.L) ≤ P.map (embedding e) := by
    rw [← intersection_map_embedding e]
    exact map_mono hP
  have hle := a.invariant_component_overgroup_le (P.map (embedding e)) hPL hne
    ((map_mono (comap_mono (le_inf (a.yplus_le_intersection.trans inf_le_left) a.contains))).trans hMP)
    (show d.starImage I d.S ⊓ d.starImage I c.L ≤ P.map (embedding e) from
      (by
        rw [a.intersectionStar_eq_inf] at hMP
        exact (le_inf inf_le_right (inf_le_left.trans
          (map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))))).trans hMP)) hn
  apply le_antisymm ?_ hP
  apply (map_le_map_iff_of_injective (embedding_injective e)).mp
  rwa [intersection_map_embedding e]

/-- The concrete scalar-centre calculation supplies the missing centreless premise. -/
theorem binary_selfCentralizing {n : ℕ} (hn : 0 < n)
    (f : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    centralizer (d.starImage I c.L : Set (d.Star I)) = ⊥ := by
  apply a.componentStar_selfCentralizing
  apply eq_bot_iff.mpr
  intro x hx
  have hh := (centerCongr f ⟨x, hx⟩).property
  change f x ∈ center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) at hh
  rw [binary_center_eq_bot hn, mem_bot] at hh
  exact f.injective (hh.trans f.map_one.symm)

/-- Construct a full flag for the given component Sylow under the original equivalence. -/
theorem exists_fullFlag {m : ℕ} (f : d.starImage I c.L ≃* LinearGroup (m + 1)) :
    ∃ b : Basis m, sylowIntersection f = cutStabilizer b Set.univ := by
  obtain ⟨U, hU⟩ := exists_modelSylow a f
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  exact ⟨b, hU.symm.trans hb⟩

/-- An outside Sylow actor induces a genuinely outer automorphism of the model intersection. -/
theorem exists_outer_preserving (hc : centralizer (d.starImage I c.L : Set (d.Star I)) = ⊥)
    (hs : ¬ d.starImage I d.S ≤ d.starImage I c.L) :
    ∃ α : MulAut H, α ∉ MulAut.innerSubgroup H ∧
      (intersection e).map α.toMonoidHom = intersection e := by
  let := a.componentStar_normal
  obtain ⟨s, hsS, hsL⟩ : ∃ s : d.Star I, s ∈ d.starImage I d.S ∧
      s ∉ d.starImage I c.L := by
    by_contra h
    apply hs
    intro s hsS
    by_contra hsL
    exact h ⟨s, hsS, hsL⟩
  refine ⟨componentAction (d.starImage I c.L) e s, ?_, ?_⟩
  · exact fun hh => hsL ((componentAction_mem_inner _ e hc s).mp hh)
  · exact componentAction_map_subgroup _ e _ a.componentIntersectionStar_lt.le s
      (a.sylow_normalizes_componentIntersectionStar hsS)

/-- A single-node intersection cannot occur when every Sylow actor lies in the component. -/
theorem outer_of_minimalParabolic {m : ℕ} (hm : 3 ≤ m)
    (f : d.starImage I c.L ≃* LinearGroup (m + 1)) (b : Basis m)
    (i : Fin m)
    (hi : intersection f = minimalParabolic b i) :
    ¬ d.starImage I d.S ≤ d.starImage I c.L := by
  classical
  intro hs
  have hex : (Finset.univ.erase i : Finset (Fin m)).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := hex
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  let P := cutStabilizer b ({k} : Set (Fin m))
  have hle : intersection f ≤ P := by
    rw [hi]
    exact (cutStabilizer_le_iff _ _ _).mpr (by simpa using hki.symm)
  have hproper : P ≠ ⊤ := by
    intro he
    have ht : cutStabilizer b (∅ : Set (Fin m)) = ⊤ := by simp [cutStabilizer]
    have hh := (cutStabilizer_le_iff b ∅ {k}).mp (show cutStabilizer b ∅ ≤ P by rw [ht, he])
    exact hh (Set.mem_singleton k)
  have hSP : d.starImage I d.S ≤ P.map (embedding f) := by
    intro s hsS
    let sL : d.starImage I c.L := ⟨s, hs hsS⟩
    have hsf : f sL ∈ sylowIntersection f := mem_map.mpr ⟨sL, hsS, rfl⟩
    refine mem_map.mpr ⟨f sL, hle (sylowIntersection_le_intersection a f hsf), ?_⟩
    exact congrArg Subtype.val (f.symm_apply_apply sL)
  have he := invariant_overgroup_eq a f P hle hproper
    (hSP.trans (P.map (embedding f)).le_normalizer)
  have hh : ({i} : Set (Fin m))ᶜ ⊆ {k} := by
    apply (cutStabilizer_le_iff b {k} {i}ᶜ).mp
    exact he.trans hi |>.le
  exact hjk (hh hji)

/-- Conditional SL₄(2) assembly: every field, including the middle node and outer action, is derived from a single-node intersection. -/
theorem four_of_minimalParabolic
    (f : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (b : Basis 3) (i : Fin 3)
    (hi : intersection (f.trans (slEquivLinear 4)) = minimalParabolic b i) :
    Nonempty (OuterMiddleNodeData d I c.L) := by
  let e := f.trans (slEquivLinear 4)
  have hc := binary_selfCentralizing a (by decide : 0 < 4) f
  have hout := outer_of_minimalParabolic a (by decide : 3 ≤ 3) e b i hi
  obtain ⟨α, hα, hP⟩ := exists_outer_preserving a e hc hout
  rw [hi] at hP
  have hm := outer_preserves_minimalParabolic_middle (by decide : 2 ≤ 3)
    (by decide : 3 ≤ 4) b i α hα hP
  have hin : i = 1 := Fin.ext (by omega)
  exact ⟨⟨e, b, hi.trans (congrArg (minimalParabolic b) hin), hc, hout⟩⟩

/-- Conditional SL₅(2) exclusion: no node can be preserved by the forced outer actor. -/
theorem five_false_of_minimalParabolic
    (f : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (b : Basis 4) (i : Fin 4)
    (hi : intersection (f.trans (slEquivLinear 5)) = minimalParabolic b i) : False := by
  let e := f.trans (slEquivLinear 5)
  have hc := binary_selfCentralizing a (by decide : 0 < 5) f
  have hout := outer_of_minimalParabolic a (by decide : 3 ≤ 4) e b i hi
  obtain ⟨α, hα, hP⟩ := exists_outer_preserving a e hc hout
  rw [hi] at hP
  have hm := outer_preserves_minimalParabolic_middle (by decide : 2 ≤ 4)
    (by decide : 4 ≤ 4) b i α hα hP
  omega

omit a in
/-- The intrinsic flag calculation closes the binary `L₄(2)` branch. -/
theorem four_branch
    (a : Input d I c)
    (f : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Nonempty (OuterMiddleNodeData d I c.L) := by
  let e := f.trans (slEquivLinear 4)
  obtain ⟨U, hU0⟩ := exists_modelSylow a e
  obtain ⟨b, hb⟩ := exists_fullFlag a e
  have hU : (U : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ := hU0.trans hb
  have hUP : (U : Subgroup (LinearGroup 4)) ≤ intersection e := by
    rw [hU0]
    exact sylowIntersection_le_intersection a e
  have hproper : intersection e ≠ ⊤ := intersection_ne_top a e
  have hres : Group.IsSolvable (primeToResidual 3 (intersection e)) :=
    intersection_residual_solvable a e
  have h3 : 3 ∣ Nat.card (intersection e) := intersection_three_dvd a e
  have hbound : ∀ X : Subgroup (LinearGroup 4), X ≤ intersection e →
      IsPGroup 3 X → Nat.card X ≤ 3 := intersection_three_subgroup_bound a e
  obtain ⟨i, hi⟩ :=
    FlagRecognition.four U b hU (intersection e) hUP hproper hres h3 hbound
  exact four_of_minimalParabolic a f b i hi

omit a in
/-- The intrinsic flag calculation excludes the binary `L₅(2)` branch. -/
theorem five_branch
    (a : Input d I c)
    (f : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    False := by
  let e := f.trans (slEquivLinear 5)
  obtain ⟨U, hU0⟩ := exists_modelSylow a e
  obtain ⟨b, hb⟩ := exists_fullFlag a e
  have hU : (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ := hU0.trans hb
  have hUP : (U : Subgroup (LinearGroup 5)) ≤ intersection e := by
    rw [hU0]
    exact sylowIntersection_le_intersection a e
  have hproper : intersection e ≠ ⊤ := intersection_ne_top a e
  have hres : Group.IsSolvable (primeToResidual 3 (intersection e)) :=
    intersection_residual_solvable a e
  have h3 : 3 ∣ Nat.card (intersection e) := intersection_three_dvd a e
  have hbound : ∀ X : Subgroup (LinearGroup 5), X ≤ intersection e →
      IsPGroup 3 X → Nat.card X ≤ 3 := intersection_three_subgroup_bound a e
  obtain ⟨i, hi⟩ :=
    FlagRecognition.five U b hU (intersection e) hUP hproper hres h3 hbound
  exact five_false_of_minimalParabolic a f b i hi

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher
