module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.CubicPlane
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Placing the Sylow three in the marked centralizer

The plane I = X × ⟨y⟩ supplied by `CubicPlane` lies in an ambient Sylow
three-subgroup P. Its index is three, so it is normal in P and contains
Z(P). Conjugation by P fixes only the center line among the four lines of
I: a normal subgroup of order three in a three-group is central. Hence
P is transitive on the other three lines.

The marked z fixes X and inverts ⟨y⟩. A z-invariant line is one of these
two factors, as follows by taking the commutator of z with an element
of the line. The independent second-centralizer bound excludes ⟨y⟩ as
Z(P). If Z(P) is not already X, z therefore moves it, and an element
of P carries its image to X. Conjugating P by that actual product gives
an ambient Sylow subgroup contained in C_G(X).

Only the earlier conclusions and the explicit second-centralizer
alternatives are used. In particular no invariant Sylow extension of I
or first-centralizer recognition is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3,
printed p.262 (PDF p.137), the placement preceding the order of C_G(X).
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative LinearAlgebra.Projectivization
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
variable {G : Type*} [Group G] [Finite G]
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem card_intrinsic_lines (I : Subgroup G) [IsElementaryAbelian 3 I]
    (hi : Nat.card I = 9) : Nat.card {L : Subgroup I // Nat.card L = 3} = 4 := by
  let e : Subgroup I ≃o Submodule (ZMod 3) (Additive I) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 3)
  have hc (L : Subgroup I) : Nat.card L = 3 ↔ Module.finrank (ZMod 3) (e L) = 1 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := e L)
    change Nat.card L = _ at hh
    rw [Nat.card_zmod] at hh
    rw [hh]
    exact (Nat.pow_right_injective (by decide : 2 ≤ 3)).eq_iff (a := _) (b := 1)
  let f := (Equiv.subtypeEquiv e.toEquiv hc).trans
    (Projectivization.equivSubmodule (ZMod 3) (Additive I)).symm
  have hh := Projectivization.card' (ZMod 3) (Additive I)
  change Nat.card I = _ at hh
  rw [hi, Nat.card_zmod, ← Nat.card_congr f] at hh
  omega

private def lines (I : Subgroup G) : Set (Subgroup G) := {L | L ≤ I ∧ Nat.card L = 3}

private theorem card_lines (I : Subgroup G) [IsElementaryAbelian 3 I]
    (hi : Nat.card I = 9) : (lines I).ncard = 4 := by
  let e : lines I ≃ {L : Subgroup I // Nat.card L = 3} :=
    { toFun := fun L => ⟨L.val.subgroupOf I,
        (Nat.card_congr (subgroupOfEquivOfLe L.property.1).toEquiv).trans L.property.2⟩
      invFun := fun L => ⟨L.val.map I.subtype, map_subtype_le _,
        (card_map_of_injective I.subtype_injective).trans L.property⟩
      left_inv := fun L => Subtype.ext (map_subgroupOf_eq_of_le L.property.1)
      right_inv := fun L => Subtype.ext (by
        change (L.val.map I.subtype).comap I.subtype = L.val
        exact comap_map_eq_self_of_injective I.subtype_injective _) }
  exact (Nat.card_congr e).trans (card_intrinsic_lines I hi)

omit [Finite G] in
private theorem center_image_fixed (P : Sylow 3 G) (p : P) :
    ((center P).map (P : Subgroup G).subtype).map (MulAut.conj (p : G)).toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
  apply le_antisymm
  · rintro _ ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    have he : (MulAut.conj (p : G)) (b : G) = b := by
      change (p : G) * b * (p : G)⁻¹ = b
      have hc : (p : G) * (b : G) = (b : G) * (p : G) :=
        congrArg Subtype.val (mem_center_iff.mp hb p)
      rw [hc, mul_inv_cancel_right]
    change (MulAut.conj (p : G)) (b : G) ∈ _
    rw [he]
    exact mem_map_of_mem _ hb
  · rintro a ⟨b, hb, rfl⟩
    refine ⟨b, mem_map_of_mem _ hb, ?_⟩
    change (p : G) * b * (p : G)⁻¹ = b
    have hc : (p : G) * (b : G) = (b : G) * (p : G) :=
      congrArg Subtype.val (mem_center_iff.mp hb p)
    rw [hc, mul_inv_cancel_right]

private theorem noncentral_lines_conjugate
    (P : Sylow 3 G) (I : Subgroup G) [IsElementaryAbelian 3 I]
    (hi : Nat.card I = 9) (hIP : I ≤ P)
    (hNI : (P : Subgroup G) ≤ normalizer (I : Set G))
    (hZI : (center P).map (P : Subgroup G).subtype ≤ I)
    (hZ : Nat.card ((center P).map (P : Subgroup G).subtype) = 3)
    (L M : Subgroup G) (hL : L ∈ lines I) (hM : M ∈ lines I)
    (hneL : L ≠ (center P).map (P : Subgroup G).subtype)
    (hneM : M ≠ (center P).map (P : Subgroup G).subtype) :
    ∃ p : P, L.map (MulAut.conj (p : G)).toMonoidHom = M := by
  classical
  let Z := (center P).map (P : Subgroup G).subtype
  let : MulAction P (Subgroup G) :=
    MulAction.compHom _ (MulAut.conj.comp (P : Subgroup G).subtype)
  have hfix (p : P) : p • Z = Z := center_image_fixed P p
  have hsub : MulAction.orbit P L ⊆ lines I \ {Z} := by
    rintro R ⟨p, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change L.map (MulAut.conj (p : G)).toMonoidHom ≤ I
      rw [← mem_normalizer_iff_map_conj_eq.mp (hNI p.property)]
      exact map_mono hL.1
    · exact (card_map_of_injective (MulAut.conj (p : G)).injective).trans hL.2
    · intro he
      apply hneL
      exact (MulAction.injective p) (he.trans (hfix p).symm)
  have hc : (lines I \ {Z}).ncard = 3 := by
    rw [Set.ncard_sdiff ((show ({Z} : Set (Subgroup G)) ⊆ lines I from Set.singleton_subset_iff.mpr ⟨hZI, hZ⟩)),
      card_lines I hi, Set.ncard_singleton]
  have hbound : Nat.card (MulAction.orbit P L) ≤ 3 := (Set.ncard_le_ncard hsub).trans_eq hc
  have hnotone : Nat.card (MulAction.orbit P L) ≠ 1 := by
    intro ho
    let := Fintype.ofFinite (MulAction.orbit P L)
    have hf := MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
      simpa only [Nat.card_eq_fintype_card] using ho)
    have hnL : (P : Subgroup G) ≤ normalizer (L : Set G) := by
      intro p hp
      apply mem_normalizer_iff_map_conj_eq.mpr
      exact hf ⟨p, hp⟩
    let : (L.subgroupOf (P : Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hnL
    have hlc : L.subgroupOf (P : Subgroup G) ≤ center P :=
      P.isPGroup'.normal_le_center_of_card_dvd_prime _ (by
        rw [Nat.card_congr (subgroupOfEquivOfLe (hL.1.trans hIP)).toEquiv, hL.2])
    have hlz : L ≤ Z := by
      rw [← map_subgroupOf_eq_of_le (hL.1.trans hIP)]
      exact map_mono hlc
    exact hneL (eq_of_le_of_card_ge hlz (by rw [hL.2, hZ]))
  obtain ⟨n, hn⟩ := P.isPGroup'.card_orbit L
  have hnle : n ≤ 1 := by
    by_contra hh
    have hh' : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have ho : (MulAction.orbit P L).ncard = 3 := by
    change Nat.card (MulAction.orbit P L) = 3
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with hn0 | hn1
    · exact (hnotone (by simpa only [hn0, pow_zero] using hn)).elim
    · simpa only [hn1, pow_one] using hn
  have he := Set.eq_of_subset_of_ncard_le hsub (by rw [hc, ho])
  exact MulAction.mem_orbit_iff.mp (he ▸ (show M ∈ lines I \ {Z} from ⟨hM, hneM⟩))

private theorem zpowers_eq_line (L : Subgroup G) (hL : Nat.card L = 3)
    {b : G} (hb : b ∈ L) (hbne : b ≠ 1) : zpowers b = L := by
  have hb3 : b ^ 3 = 1 := by
    simpa only [hL, Subgroup.coe_pow, OneMemClass.coe_one] using
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨b, hb⟩ : L)))
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hbne
  exact eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [Nat.card_zpowers, hbo, hL])

private theorem invariant_line_eq_factor {D : Seed G} (E : EarlierConclusions D)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t)
    (hyo : orderOf y = 3) (hyinv : D.z * y * D.z⁻¹ = y⁻¹)
    (L : Subgroup G) (hL : Nat.card L = 3) (hLI : L ≤ D.X ⊔ zpowers y)
    (hfix : L.map (MulAut.conj D.z).toMonoidHom = L) :
    L = D.X ∨ L = zpowers y := by
  by_cases hLX : L ≤ D.X
  · exact Or.inl (eq_of_le_of_card_ge hLX (by rw [hL, D.card_X]))
  change ¬ ∀ a, a ∈ L → a ∈ D.X at hLX
  push Not at hLX
  obtain ⟨a, ha, hax⟩ := hLX
  have haI := hLI ha
  have hYX : zpowers y ≤ centralizer (D.X : Set G) :=
    (zpowers_le.mpr hy).trans E.component_le
  change a ∈ ((D.X ⊔ zpowers y : Subgroup G) : Set G) at haI
  rw [coe_mul_of_right_le_normalizer_left D.X (zpowers y)
    (hYX.trans (Subgroup.centralizer_le_normalizer _))] at haI
  obtain ⟨x, hx, b, hb, rfl⟩ := haI
  change x ∈ D.X at hx
  change b ∈ zpowers y at hb
  change x * b ∈ L at ha
  change x * b ∉ D.X at hax
  have hbne : b ≠ 1 := by
    intro hh
    apply hax
    rw [hh, mul_one]
    exact hx
  have hb3 : b ^ 3 = 1 := by
    simpa only [Nat.card_zpowers, hyo, Subgroup.coe_pow, OneMemClass.coe_one] using
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨b, hb⟩ : zpowers y)))
  have hb2 : b⁻¹ * b⁻¹ = b := by
    have hh : b * b = b⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
      simpa only [pow_succ, pow_zero, one_mul] using hb3)
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv hh
  have hxb : x * b = b * x := hYX hb x hx
  have hzx : D.z * x * D.z⁻¹ = x := by
    rw [(mem_centralizer_singleton_iff.mp (D.X_le hx)).symm, mul_inv_cancel_right]
  have hzb : D.z * b * D.z⁻¹ = b⁻¹ := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    change MulAut.conj D.z (y ^ n) = _
    rw [map_zpow]
    change (D.z * y * D.z⁻¹) ^ n = _
    rw [hyinv, inv_zpow]
  have hc : D.z * (x * b) * D.z⁻¹ = x * b⁻¹ := by
    calc
      _ = (D.z * x * D.z⁻¹) * (D.z * b * D.z⁻¹) := by group
      _ = _ := by rw [hzx, hzb]
  have hm : D.z * (x * b) * D.z⁻¹ ∈ L := by
    rw [← hfix]
    exact mem_map_of_mem _ ha
  have he : (D.z * (x * b) * D.z⁻¹) * (x * b)⁻¹ = b := by
    rw [hc, mul_inv_rev]
    calc
      x * b⁻¹ * (b⁻¹ * x⁻¹) = x * (b⁻¹ * b⁻¹) * x⁻¹ := by group
      _ = x * b * x⁻¹ := by rw [hb2]
      _ = b := by rw [hxb, mul_inv_cancel_right]
  have hbL : b ∈ L := he ▸ L.mul_mem hm (L.inv_mem ha)
  exact Or.inr ((zpowers_eq_line L hL hbL hbne).symm.trans
    (zpowers_eq_line (zpowers y) (by rw [Nat.card_zpowers, hyo]) hb hbne))

omit [Finite G] in
private theorem sylow_centralizes_conjugate_center (P : Sylow 3 G) (g : G) :
    ((g • P : Sylow 3 G) : Subgroup G) ≤
      centralizer (((center P).map (P : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G) := by
  rintro a ⟨b, hb, rfl⟩ x ⟨c, ⟨d, hd, rfl⟩, rfl⟩
  have he : (d : G) * b = b * d :=
    congrArg Subtype.val (mem_center_iff.mp hd (⟨b, hb⟩ : P)).symm
  change (g * (d : G) * g⁻¹) * (g * b * g⁻¹) =
    (g * b * g⁻¹) * (g * (d : G) * g⁻¹)
  simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj g) he

/-- The marked cubic plane places an ambient Sylow three in the literal centralizer of X. -/
theorem exists_three_in_centralizer [IsSimpleGroup G] {D : Seed G}
    (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry) :
    ∃ P : Sylow 3 G, (P : Subgroup G) ≤ C D := by
  classical
  obtain ⟨y, P, hy, hyo, hyinv, hIP⟩ := exists_source_plane E
  let I := D.X ⊔ zpowers y
  let : IsElementaryAbelian 3 I := plane_elementary E hy hyo
  have hi : Nat.card I = 9 := plane_card E hy hyo
  let A := I.subgroupOf (P : Subgroup G)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hIP
  have hAc : Nat.card A = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hIP).toEquiv).trans hi
  have hAi : A.index = 3 := by
    have hh := A.card_mul_index
    rw [hAc, three_card E.card P] at hh
    omega
  let : A.Normal := normal_of_index_three_of_isPGroup P.isPGroup' A hAi
  have hNI : (P : Subgroup G) ≤ normalizer (I : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIP).mp inferInstance
  let Z := (center P).map (P : Subgroup G).subtype
  have hZI : Z ≤ I := by
    have hh := map_mono (f := (P : Subgroup G).subtype)
      (center_le_of_abelian_index_three P.isPGroup' (three_noncommutative E hAlt P)
        A inferInstance hAi)
    exact hh.trans (map_subgroupOf_eq_of_le hIP).le
  have hZ : Nat.card Z = 3 := three_center_image_card E hAlt P
  have hZneY : Z ≠ zpowers y := three_center_image_ne_component_cubic E hAlt hy hyo P
  have hZX : ∃ g : G, Z.map (MulAut.conj g).toMonoidHom = D.X := by
    by_cases he : Z = D.X
    · refine ⟨1, ?_⟩
      have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext a
        simp
      rwa [hid, map_id]
    have hmove : Z.map (MulAut.conj D.z).toMonoidHom ≠ Z := by
      intro hf
      rcases invariant_line_eq_factor E hy hyo hyinv Z hZ hZI hf with hx | hy'
      · exact he hx
      · exact hZneY hy'
    let R := Z.map (MulAut.conj D.z).toMonoidHom
    have hRI : R ≤ I := by
      have hh := map_mono (f := (MulAut.conj D.z).toMonoidHom) hZI
      exact hh.trans (mem_normalizer_iff_map_conj_eq.mp (plane_z_normalizes hyinv)).le
    have hRc : Nat.card R = 3 :=
      (card_map_of_injective (MulAut.conj D.z).injective).trans hZ
    obtain ⟨p, hp⟩ := noncentral_lines_conjugate P I hi hIP hNI hZI hZ R D.X
      ⟨hRI, hRc⟩ ⟨le_sup_left, D.card_X⟩ hmove (Ne.symm he)
    refine ⟨(p : G) * D.z, ?_⟩
    change (Z.map (MulAut.conj D.z).toMonoidHom).map
      (MulAut.conj (p : G)).toMonoidHom = D.X at hp
    rw [map_map] at hp
    convert hp using 1
    congr 1
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_inv_rev]
    group
  obtain ⟨g, hg⟩ := hZX
  refine ⟨g • P, ?_⟩
  have hh := sylow_centralizes_conjugate_center P g
  rwa [hg] at hh

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
