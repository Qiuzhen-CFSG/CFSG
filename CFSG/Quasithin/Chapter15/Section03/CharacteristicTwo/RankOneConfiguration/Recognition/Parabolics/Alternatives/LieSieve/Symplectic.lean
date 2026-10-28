module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.SolvableLift
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedFlagGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

/-!
# The symplectic branches of the rank-one Lie sieve

The full binary group Sp₄(2) is excluded by its actual S₆ equivalence and
the component's perfectness. For A₆, the order-three residual rules out a
Sylow subgroup as the component intersection, so that intersection is a
maximal parabolic. The concrete Sp₄(2)′ flag census aligns it with a labeled
matrix parabolic. S preserves its Sylow intersection and this parabolic;
there being exactly two maximal overgroups, S fixes the other as well.
This constructs the required marking and both diagram labels.

For a full symplectic group over any binary field, containment of the
component intersection in the Sylow normalizer forces equality. The Borel
is solvable, and both Y₊* and S* normalize it, so solvable-preimage control
gives the reverse inclusion. Its order q⁴(q−1)² contradicts the source
three-part bound: divisibility by three would imply divisibility by nine.
The S₃ shadow also proves that the prime-to-three residual of the actual
intersection is solvable, and this property is transported to the model.

For nonbinary fields, the intrinsic Sylow-overgroup theorem places the
proper model intersection in a conjugate full parabolic. Solvability of
its prime-to-three residual then forces it into the Sylow normalizer.
`symplecticFour_excluded` combines this theorem with the Borel contradiction
and the binary perfectness obstruction, discharging the placement premise
of the retained conditional helper. None of the results uses rank-two
elimination or the later 15.3.30–31 exclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.5.5–6, printed pp.104–105, and 15.3.26–28, pp.1130–1131.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

theorem Input.yplus_solvable (a : Input d I c) : Group.IsSolvable d.Yplus := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := a.facts.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := (pCore_isPGroup (p := 2) (G := (d.Yplus ⊔ d.S : Subgroup G))).isNilpotent
  let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr
      ⟨inferInstance, inferInstance⟩
  exact Group.isSolvable_of_isSolvable_injective (f := inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))
    (inclusion_injective le_sup_left)

theorem Input.componentIntersectionStar_residual_solvable (a : Input d I c) :
    Group.IsSolvable (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))) := by
  let := a.yplus_solvable
  let j := subgroupOfEquivOfLe (a.yplus_le_intersection.trans inf_le_right)
  let : Group.IsSolvable (d.Yplus.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective
  let : Group.IsSolvable (d.starImage I d.Yplus) :=
    Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective
      (d.Yplus.subgroupOf I))
  let f := (d.starImage I (d.M ⊓ c.L)).subtype
  have hs : Group.IsSolvable ((primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).map f) :=
    a.componentIntersectionStar_residual ▸ inferInstance
  let := hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := f.subgroupMap (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))))
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h)))

theorem Input.componentIntersection_eq_sylowNormalizer (a : Input d I c)
    (Q : Sylow 2 (d.starImage I c.L))
    (hQ : (Q : Subgroup (d.starImage I c.L)) =
      (d.starImage I d.S).subgroupOf (d.starImage I c.L))
    (hs : Group.IsSolvable (normalizer (Q : Set (d.starImage I c.L))))
    (hPN : (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) ≤
      normalizer (Q : Set (d.starImage I c.L))) :
    (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) =
      normalizer (Q : Set (d.starImage I c.L)) := by
  let L := d.starImage I c.L
  let S := d.starImage I d.S
  let P := d.starImage I (d.M ⊓ c.L)
  let K := S ⊓ L
  let B := L ⊓ normalizer (K : Set (d.Star I))
  have hPL : P ≤ L := a.componentIntersectionStar_lt.le
  have hQB : normalizer (Q : Set L) = B.subgroupOf L := by
    have he : (Q : Subgroup L) = K.subgroupOf L := by
      rw [hQ]
      ext x
      exact (and_iff_left x.property).symm
    change normalizer ((Q : Subgroup L) : Set L) = _
    rw [he, ← subgroupOf_normalizer_eq (show K ≤ L from inf_le_right)]
    ext x
    exact (and_iff_right x.property).symm
  have hPB : P ≤ B := by
    intro x hx
    have hn := hPN (show (⟨x, hPL hx⟩ : L) ∈ P.subgroupOf L from hx)
    rw [hQB] at hn
    exact hn
  have hsolB : Group.IsSolvable B := by
    have hs' : Group.IsSolvable (B.subgroupOf L) := hQB ▸ hs
    let := hs'
    let j := subgroupOfEquivOfLe (show B ≤ L from inf_le_left)
    exact Group.isSolvable_of_surjective (f := j.toMonoidHom) j.surjective
  have hSL : S ≤ normalizer (L : Set (d.Star I)) := by
    let := a.componentStar_normal
    exact le_normalizer_of_normal
  have hSK : S ≤ normalizer (K : Set (d.Star I)) :=
    (le_inf S.le_normalizer hSL).trans inf_normalizer_le_normalizer_inf
  have hSB : S ≤ normalizer (B : Set (d.Star I)) :=
    (le_inf hSL (hSK.trans (normalizer (K : Set (d.Star I))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hYP : d.starImage I d.Yplus ≤ P :=
    map_mono (comap_mono (le_inf (a.yplus_le_intersection.trans inf_le_left) a.contains))
  have hn : d.starImage I (d.Yplus ⊔ d.S) ≤ normalizer (B : Set (d.Star I)) := by
    change ((d.Yplus ⊔ d.S).subgroupOf I).map (d.starMap I) ≤ _
    rw [subgroupOf_sup (a.yplus_le_intersection.trans inf_le_right) a.sylow_le, Subgroup.map_sup]
    exact sup_le ((hYP.trans hPB).trans B.le_normalizer) hSB
  have hBP := a.solvable_star_subgroup_le_intersection B inf_le_left hsolB hn
  rw [hQB]
  exact le_antisymm (comap_mono hPB) (comap_mono hBP)

theorem Input.componentIntersection_intrinsic_ne_top (a : Input d I c) :
    (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) ≠ ⊤ := by
  intro ht
  exact (not_le_of_gt a.componentIntersectionStar_lt) (subgroupOf_eq_top.mp ht)

theorem Input.componentIntersection_intrinsic_three_dvd (a : Input d I c) :
    3 ∣ Nat.card ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe a.componentIntersectionStar_lt.le).toEquiv]
  exact a.componentIntersectionStar_three_dvd

omit [Finite G] in
theorem Input.componentSylow_le_intersection (a : Input d I c)
    (Q : Sylow 2 (d.starImage I c.L))
    (hQ : (Q : Subgroup (d.starImage I c.L)) =
      (d.starImage I d.S).subgroupOf (d.starImage I c.L)) :
    (Q : Subgroup (d.starImage I c.L)) ≤
      (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
  rw [hQ, a.intersectionStar_eq_inf]
  intro x hx
  exact ⟨x.property, (map_mono (comap_mono
    (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))) hx⟩

theorem Input.alternatingSix_intersection_isCoatom (a : Input d I c)
    (e : d.starImage I c.L ≃* alternatingGroup (Fin 6)) :
    IsCoatom ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  rcases Binary.ComponentActionGeometry.sylow_overgroup_cases e Q _
      (a.componentSylow_le_intersection Q hQ) a.componentIntersection_intrinsic_ne_top
      with he | hc
  · have hdiv := a.componentIntersection_intrinsic_three_dvd
    rw [he] at hdiv
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    rw [hn] at hdiv
    exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdiv))
  · exact hc

theorem Input.componentIntersection_intrinsic_nine_not_dvd (a : Input d I c) :
    ¬ 9 ∣ Nat.card ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe a.componentIntersectionStar_lt.le).toEquiv]
  intro hdiv
  let P := d.starImage I (d.M ⊓ c.L)
  let R : Sylow 3 P := Sylow.nonempty.some
  have hd : 9 ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (n := 2) hdiv
  have hle := a.star_three_subgroup_card_le_three
    ((R : Subgroup P).map P.subtype)
    ((map_subtype_le _).trans (by
      dsimp [P]
      rw [a.intersectionStar_eq_inf]
      exact inf_le_right))
    (R.isPGroup'.map P.subtype)
  rw [card_map_of_injective P.subtype_injective] at hle
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := R)) hd
  omega

theorem Input.componentIntersection_model_residual_solvable (a : Input d I c)
    {H : Type*} [Group H] (e : d.starImage I c.L ≃* H) :
    Group.IsSolvable (primeToResidual 3
      (((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map e.toMonoidHom)) := by
  let f := (subgroupOfEquivOfLe a.componentIntersectionStar_lt.le).symm.trans
    (e.subgroupMap ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)))
  let := a.componentIntersectionStar_residual_solvable
  have hs := Group.isSolvable_of_surjective
    (f.toMonoidHom.subgroupMap_surjective (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))))
  rwa [map_primeToResidual_of_surjective 3 f.toMonoidHom f.surjective] at hs

omit [Finite G] in
theorem symplecticFour_binary_excluded (F : ClassificationField)
    (e : d.starImage I c.L ≃* Sp F.Carrier) (hF : Nat.card F.Carrier = 2) : False := by
  let := c.star_quasisimple
  let f := (e.trans (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F.Carrier hF))).trans
    Binary.symmetricSixEquiv.symm
  let : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have ht : alternatingGroup (Fin 6) = ⊤ :=
    (alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 6))).symm.trans
      Group.IsPerfect.commutator_eq_top
  have hm : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := ht ▸ mem_top _
  exact (by decide : Equiv.swap (0 : Fin 6) 1 ∉ alternatingGroup (Fin 6)) hm

theorem symplecticFour_excluded_of_normalizes (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Sp F.Carrier)
    (Q : Sylow 2 (d.starImage I c.L))
    (hQ : (Q : Subgroup (d.starImage I c.L)) =
      (d.starImage I d.S).subgroupOf (d.starImage I c.L))
    (hPN : (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) ≤
      normalizer (Q : Set (d.starImage I c.L))) : False := by
  let J := (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (normalizer (Q : Set (d.starImage I c.L))).map e.toMonoidHom =
      normalizer (R : Set (Sp F.Carrier)) :=
    Sylow.normalizer_map_surjective Q e.toMonoidHom e.surjective
  let f := (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  have hs : Group.IsSolvable (normalizer (Q : Set (d.starImage I c.L))) := by
    let := isSolvable_sylow_normalizer F.card_eq F.degree_pos R
    exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  have heJ : J = normalizer (Q : Set (d.starImage I c.L)) :=
    a.componentIntersection_eq_sylowNormalizer Q hQ hs hPN
  have hcard : Nat.card J = (2 ^ F.degree)^4 * (2 ^ F.degree - 1)^2 := by
    rw [heJ, Nat.card_congr f.toEquiv,
      Nat.card_congr (EvenBorelTorus.sylowNormalizerEquiv F.card_eq F.degree_pos R).toEquiv,
      card_borel, F.card_eq]
  have hthree := a.componentIntersection_intrinsic_three_dvd
  change 3 ∣ Nat.card J at hthree
  rw [hcard] at hthree
  have hnot : ¬ 3 ∣ (2 ^ F.degree)^4 := by
    intro hh
    exact (by decide : ¬ 3 ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow hh))
  have ht : 3 ∣ 2 ^ F.degree - 1 := Nat.prime_three.dvd_of_dvd_pow
    ((Nat.prime_three.dvd_mul.mp hthree).resolve_left hnot)
  have hnine : 9 ∣ Nat.card J := by
    rw [hcard]
    exact (show 9 ∣ (2 ^ F.degree - 1)^2 from pow_dvd_pow_of_dvd ht 2).trans
      (dvd_mul_left _ _)
  exact a.componentIntersection_intrinsic_nine_not_dvd hnine

/-- Conditional assembly: the sole extra premise is the intrinsic nonbinary
Sylow-overgroup placement theorem. It has no chapter or marking hypotheses. -/
theorem symplecticFour_excluded_of_residual_placement (a : Input d I c)
    (F : ClassificationField) (e : d.starImage I c.L ≃* Sp F.Carrier)
    (place : 2 < Nat.card F.Carrier → ∀ (Q : Sylow 2 (Sp F.Carrier))
      (H : Subgroup (Sp F.Carrier)), (Q : Subgroup (Sp F.Carrier)) ≤ H → H ≠ ⊤ →
        3 ∣ Nat.card H → ¬ 9 ∣ Nat.card H →
        Group.IsSolvable (primeToResidual 3 H) → H ≤ normalizer (Q : Set (Sp F.Carrier))) :
    False := by
  by_cases htwo : Nat.card F.Carrier = 2
  · exact symplecticFour_binary_excluded F e htwo
  have hgt : 2 < Nat.card F.Carrier := lt_of_le_of_ne
    (Nat.succ_le_of_lt (Finite.one_lt_card (α := F.Carrier))) (Ne.symm htwo)
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  let J := (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn : J.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    exact a.componentIntersection_intrinsic_ne_top
      (e.mapSubgroup.injective (ht.trans e.mapSubgroup.map_top.symm))
  have hp := place hgt R (J.map e.toMonoidHom)
    (map_mono (a.componentSylow_le_intersection Q hQ)) hn
    (by rw [card_map_of_injective e.injective]; exact a.componentIntersection_intrinsic_three_dvd)
    (by rw [card_map_of_injective e.injective]; exact a.componentIntersection_intrinsic_nine_not_dvd)
    (a.componentIntersection_model_residual_solvable e)
  have hPN : J ≤ normalizer (Q : Set (d.starImage I c.L)) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [Sylow.normalizer_map_surjective Q e.toMonoidHom e.surjective]
    exact hp
  exact symplecticFour_excluded_of_normalizes a F e Q hQ hPN

/-- The full symplectic entry of B.5.6 is impossible under the local inputs
of 15.3.28. This includes the nonperfect binary group; over larger fields,
intrinsic residual placement and the invariant Borel give the contradiction. -/
theorem symplecticFour_excluded (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False :=
  symplecticFour_excluded_of_residual_placement a F e
    ThreeResidualPlacement.sylow_overgroup_le_normalizer

private theorem fixes_two_coatoms {H : Type*} [Group H]
    (T : Subgroup H) (P : Fin 2 → Subgroup H) (hP : Function.Injective P)
    (geom : ∀ K : Subgroup H, (IsCoatom K ∧ T ≤ K) ↔ ∃ i, K = P i)
    (β : MulAut H) (hT : T.map β.toMonoidHom = T)
    (node : Fin 2) (hnode : (P node).map β.toMonoidHom = P node) :
    ∀ i, (P i).map β.toMonoidHom = P i := by
  intro i
  have hi := (geom (P i)).mpr ⟨i, rfl⟩
  have hc : IsCoatom ((P i).map β.toMonoidHom) :=
    (β.mapSubgroup.isCoatom_iff (P i)).mpr hi.1
  obtain ⟨j, hj⟩ := (geom _).mp ⟨hc, hT ▸ map_mono hi.2⟩
  by_cases hin : i = node
  · simpa only [hin] using hnode
  have hjn : j ≠ node := by
    intro h
    have he := (map_injective β.injective) (hj.trans ((congrArg P h).trans hnode.symm))
    exact hin (hP he)
  have hji : j = i := by omega
  exact hj.trans (congrArg P hji)

private theorem map_conjNormal_subgroupOf {H : Type*} [Group H] [Finite H]
    (L P : Subgroup H) [L.Normal] (s : H) (hs : s ∈ normalizer (P : Set H)) :
    (P.subgroupOf L).map (MulAut.conjNormal (H := L) s).toMonoidHom = P.subgroupOf L := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact (hs (x : H)).mp hx
  · rw [card_map_of_injective (f := (MulAut.conjNormal (H := L) s).toMonoidHom)
      (MulAut.conjNormal (H := L) s).injective]

/-- Conditional assembly from the intrinsic matrix flag census. The actual
intersection is proved maximal, and its S-invariance fixes both nodes. -/
theorem alternatingSix_marking_of_flag_geometry (a : Input d I c)
    (e₀ : d.starImage I c.L ≃* alternatingGroup (Fin 6))
    (geometry : ∃ T : Sylow 2 (commutator (Sp (ZMod 2))),
      Function.Injective symplecticDerivedParabolic ∧
      ∀ P : Subgroup (commutator (Sp (ZMod 2))),
        (IsCoatom P ∧ (T : Subgroup (commutator (Sp (ZMod 2)))) ≤ P) ↔
          ∃ i, P = symplecticDerivedParabolic i) :
    Nonempty (RankTwoParabolicMarking d I c.L
      (commutator (Sp (ZMod 2))) symplecticDerivedParabolic) := by
  let D := commutator (Sp (ZMod 2))
  let L := d.starImage I c.L
  let P := d.starImage I (d.M ⊓ c.L)
  let J := P.subgroupOf L
  let e₁ := e₀.trans (Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm
  obtain ⟨T, hTinj, hgeom⟩ := geometry
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D
    (Q.mapSurjective (f := e₁.toMonoidHom) e₁.surjective) T
  let e := e₁.trans (MulAut.conj g)
  have hQT : (Q : Subgroup L).map e.toMonoidHom = (T : Subgroup D) := by
    change (Q : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e₁.toMonoidHom) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hcJ : IsCoatom (J.map e.toMonoidHom) :=
    (e.mapSubgroup.isCoatom_iff J).mpr (a.alternatingSix_intersection_isCoatom e₀)
  obtain ⟨node, hnode⟩ := (hgeom _).mp
    ⟨hcJ, hQT ▸ map_mono (a.componentSylow_le_intersection Q hQ)⟩
  generalize e = e' at hQT hnode
  refine ⟨{ equiv := e', node := node, intersection := hnode, diagram := ?_ }⟩
  intro s hs i
  let := a.componentStar_normal
  let b := MulAut.conjNormal (H := L) s
  let β : MulAut D := (e'.symm.trans b).trans e'
  have transport (K : Subgroup L) :
      (K.map e'.toMonoidHom).map β.toMonoidHom = (K.map b.toMonoidHom).map e'.toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change e' (b (e'.symm (e' x))) = e' (b x)
    rw [e'.symm_apply_apply]
  have hQb : (Q : Subgroup L).map b.toMonoidHom = (Q : Subgroup L) := by
    rw [hQ]
    exact map_conjNormal_subgroupOf L (d.starImage I d.S) s
      ((d.starImage I d.S).le_normalizer hs)
  have hJb : J.map b.toMonoidHom = J :=
    map_conjNormal_subgroupOf L P s (a.sylow_normalizes_componentIntersectionStar hs)
  have hTb : (T : Subgroup D).map β.toMonoidHom = (T : Subgroup D) := by
    rw [← hQT, transport, hQb]
  have hnodeb : (symplecticDerivedParabolic node).map β.toMonoidHom =
      symplecticDerivedParabolic node := by
    rw [← hnode, transport, hJb]
  have hPi := fixes_two_coatoms (T : Subgroup D) symplecticDerivedParabolic hTinj
    hgeom β hTb node hnodeb i
  let f : D →* d.Star I := L.subtype.comp e'.symm.toMonoidHom
  have hcomp : f.comp β.toMonoidHom = (MulAut.conj s).toMonoidHom.comp f := by
    ext x
    change ((e'.symm (e' (b (e'.symm x))) : L) : d.Star I) =
      s * ((e'.symm x : L) : d.Star I) * s⁻¹
    rw [e'.symm_apply_apply]
    rfl
  have hfixed : ((symplecticDerivedParabolic i).map f).map (MulAut.conj s).toMonoidHom =
      (symplecticDerivedParabolic i).map f := by
    rw [map_map, ← hcomp, ← map_map, hPi]
  refine ⟨1, ?_⟩
  simp only [map_one, Subgroup.coe_one]
  change ((symplecticDerivedParabolic i).map f).map (MulAut.conj s).toMonoidHom =
    ((symplecticDerivedParabolic i).map f).map (MonoidHom.id _)
  rw [Subgroup.map_id]
  exact hfixed

/-- The A₆ alternative with its actual Sp₄(2)′ carrier, the literal component
intersection, and preservation of both labeled parabolic classes. -/
theorem alternatingSix_marking (a : Input d I c)
    (e : d.starImage I c.L ≃* alternatingGroup (Fin 6)) :
    Nonempty (RankTwoParabolicMarking d I c.L
      (commutator (Sp (ZMod 2))) symplecticDerivedParabolic) :=
  alternatingSix_marking_of_flag_geometry a e Binary.exists_derived_flag

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
