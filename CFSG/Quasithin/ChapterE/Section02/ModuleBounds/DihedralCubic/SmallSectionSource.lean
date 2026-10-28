module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallSpanAction
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualTwentySeven
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.CubicActors
public import Theory.ElementaryAbelian.Injective

/-!
# The small section in the solvable E.2.17 source configuration

The order-two image of V modulo the two-core remains order two on the actual
section L/Z: a trivial image would contradict K=[K,V], L=[L,K], and |L/Z|≥16.
The faithful section-action alternatives give section orders 16 or 64. The
64 row would have an extraspecial residual of order27. The source cubic
models force the original residual to have that same row, whose section
image is abelian by the original O²(M)-centralization hypothesis. Thus the
actual section has order16.

Source: Aschbacher--Smith, E.2.17, solvable case, printed pp.229--230.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
variable {H : Type*} [Group H] [Finite H]
omit [Finite H] in
theorem section_elementary_of_image (L Z : Subgroup H) [Z.Normal]
    [IsElementaryAbelian 2 (L.map (QuotientGroup.mk' Z))] :
    IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L) := by
  let f := (QuotientGroup.mk' Z).subgroupMap L
  have hk : f.ker = Z.subgroupOf L := by
    ext x
    change f x = 1 ↔ (x : H) ∈ Z
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (x : H)).mp
      exact congrArg (fun y : L.map (QuotientGroup.mk' Z) => (y : H ⧸ Z)) hx
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : H)).mpr hx
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((QuotientGroup.mk' Z).subgroupMap_surjective L))
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

omit [Finite H] in
private theorem small_section_actor_card (K L Z V Q : Subgroup H)
    [K.Normal] [L.Normal] [Z.Normal] [Q.Normal]
    (hK : K = ⁅K,V⁆) (hL : L = ⁅L,K⁆)
    (hO : ⁅L,Q⁆ ≤ Z) (ha : Nat.card (V.map (QuotientGroup.mk' Q)) = 2)
    (hsize : 16 ≤ Nat.card (L ⧸ Z.subgroupOf L)) :
    let := centralizerModulo_top_normal L Z
    Nat.card (V.map (QuotientGroup.mk' (centralizerModulo ⊤ L Z))) = 2 := by
  let := centralizerModulo_top_normal L Z
  let C := centralizerModulo ⊤ L Z
  let q := QuotientGroup.mk' C
  have hQC : Q ≤ C := by
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨mem_top x, fun u hu =>
      hO (commutator_mem_commutator hu hx)⟩
  let qb : (H ⧸ Q) →* H ⧸ C := QuotientGroup.lift Q q (by
    simpa only [q,QuotientGroup.ker_mk'] using hQC)
  have hc : qb.comp (QuotientGroup.mk' Q) = q := rfl
  have hd : Nat.card (V.map q) ∣ 2 := by
    rw [←ha,←hc,←map_map]
    exact card_map_dvd _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
  · have hv : V.map q = ⊥ := card_eq_one.mp hone
    have hk : K.map q = ⊥ := by
      rw [hK,map_commutator,hv]
      simp
    have hKC : K ≤ C := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff K).mp hk
    have hLZ : L ≤ Z := by
      rw [hL]
      apply commutator_le.mpr
      intro l hl k hk
      exact (mem_centralizerModulo_iff.mp (hKC hk)).2 l hl
    have he : Z.subgroupOf L = ⊤ := by
      exact top_unique (fun x _ => hLZ x.property)
    have hh : Nat.card (L ⧸ Z.subgroupOf L) = 1 := by rw [he]; simp
    omega
  · exact htwo

theorem source_small_section_card
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (V B L Z : Subgroup H) [L.Normal] [Z.Normal]
    (hZL : Z ≤ L) [IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L)]
    (hB : B ≤ V) (hspan : L = conjugateSpanBy B ⊤)
    (hK : pResidual 2 H = ⁅pResidual 2 H,V⁆) (hL : L = ⁅L,pResidual 2 H⁆)
    (hO : ⁅L,pCore 2 H⁆ ≤ Z)
    (ha : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 2)
    (hd : Nat.card (⁅L,V⁆.map (QuotientGroup.mk' Z)) ≤ 4)
    (hsize : 16 ≤ Nat.card (L ⧸ Z.subgroupOf L))
    (hc : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (V : Set H))
    (hm : SolvableMinimalParabolic.CubicResidualModels H) :
    Nat.card (L ⧸ Z.subgroupOf L) = 16 := by
  let := centralizerModulo_top_normal L Z
  let C := centralizerModulo ⊤ L Z
  let q := QuotientGroup.mk' C
  let Q := pCore 2 H
  let K := pResidual 2 H
  let R := pResidual 2 (H ⧸ Q)
  have hQC : Q ≤ C := by
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨mem_top x, fun u hu =>
      hO (commutator_mem_commutator hu hx)⟩
  let qb : (H ⧸ Q) →* H ⧸ C := QuotientGroup.lift Q q (by
    simpa only [q,QuotientGroup.ker_mk'] using hQC)
  have hmap : R.map qb = K.map q := by
    rw [show R = K.map (QuotientGroup.mk' Q) from
      (map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective Q)).symm,map_map]
    rfl
  have hpR : IsPGroup 3 R := by
    rcases hm with h | h | h
    · exact IsPGroup.of_card (n := 1) (by simpa using h.1)
    · exact IsPGroup.of_card (n := 2) (by simpa using h.1)
    · exact IsPGroup.of_card (n := 3) (by simpa using h.1)
  have hp : IsPGroup 3 (K.map q) := hmap ▸ hpR.map qb
  have ha' := small_section_actor_card K L Z V Q hK hL hO ha hsize
  have rows := small_span_section_action K L Z V hZL hK hL hd hsize hp ha'
  rcases rows with h | h
  · exact h.1
  · have hh : 27 ∣ Nat.card R := by
      rw [←h.2.2,←hmap]
      exact card_map_dvd _ _
    rcases hm with h3 | h9 | h27
    · rw [h3.1] at hh
      norm_num at hh
    · rw [h9.1] at hh
      norm_num at hh
    · let := h27.2.1
      have hx := source_twentyseven_section_exclusion S hP hs V B L Z hB hspan hc hO
      apply False.elim
      apply hx
      have he : K.map q = pResidual 2 (H ⧸ C) :=
        map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C)
      exact he ▸ h.2.1
end CFSG.Quasithin.ChapterE.DihedralCubic
